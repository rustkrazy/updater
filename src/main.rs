use std::collections::{BTreeMap, HashMap};
use std::ffi::OsString;
use std::fs::File;
use std::io::{self, Read, Seek, Write};
use std::path::{Path, PathBuf};
use std::thread;
use std::time::Duration;

use anyhow::bail;
use cargo::core::compiler::{BuildConfig, CompileMode};
use cargo::core::SourceId;
use cargo::ops::{CompileFilter, CompileOptions};
use cargo::util::config::Config as CargoConfig;
use cargo::util::interning::InternedString;
use clap::Parser;
use fatfs::{FatType, FormatVolumeOptions};
use fscommon::StreamSlice;
use reqwest::{blocking::Client, header::CONTENT_TYPE, Url};
use squashfs_ng::write::{
    Source as SqsSource, SourceData as SqsSourceData, SourceFile as SqsSourceFile,
    TreeProcessor as SqsTreeProcessor,
};
use tempfile::NamedTempFile;

#[allow(non_upper_case_globals)]
const KiB: u32 = 1024;
#[allow(non_upper_case_globals)]
const MiB: u32 = 1024 * KiB;

const KERNEL_BASE: &str = "https://github.com/rustkrazy/kernel/raw/master/";
const FIRMWARE_BASE: &str = "https://github.com/rustkrazy/firmware/raw/master/";

#[derive(Debug, Parser)]
#[command(author = "The Rustkrazy Authors", version = "v0.1.0", about = "Update a rustkrazy instance over the network.", long_about = None)]
struct Args {
    /// Base URL of the instance, e.g. https://rustkrazy:1234@198.51.100.1
    #[arg(short = 'u', long = "update")]
    update: String,
    /// Size of image in bytes.
    #[arg(short = 'n', long = "size")]
    size: u64,
    /// Architecture of the device running the image. Supported: x86_64 rpi.
    #[arg(short = 'a', long = "architecture")]
    arch: String,
    /// Crates to install into the image.
    #[arg(short = 'c', long = "crates")]
    crates: Vec<String>,
    /// Crates to install from git.
    #[arg(short = 'g', long = "git")]
    git: Vec<String>,
    /// Init crate. rustkrazy_init is a reasonable default for most applications.
    #[arg(short = 'i', long = "init")]
    init: String,
}

fn write_mbr_partition_table(
    mbr: &mut StreamSlice<NamedTempFile>,
    dev_size: u64,
) -> anyhow::Result<()> {
    const INACTIVE: &[u8] = &[0x00];
    const ACTIVE: &[u8] = &[0x80];
    const INVALID_CHS: &[u8] = &[0xFF, 0xFF, 0xFE]; // Causes sector values to be used
    const FAT: &[u8] = &[0xc];
    const LINUX: &[u8] = &[0x83];
    const SQUASHFS: &[u8] = LINUX;
    const SIGNATURE: &[u8] = &[0x55, 0xAA];

    mbr.write_all(&[0; 446])?; // Boot code

    // Partition 1: boot
    mbr.write_all(ACTIVE)?;
    mbr.write_all(INVALID_CHS)?;
    mbr.write_all(FAT)?;
    mbr.write_all(INVALID_CHS)?;
    mbr.write_all(&2048_u32.to_le_bytes())?; // Start at sector 2048
    mbr.write_all(&(256 * MiB / 512).to_le_bytes())?; // 256 MiB in size

    // Partition 2: rootfs A
    mbr.write_all(INACTIVE)?;
    mbr.write_all(INVALID_CHS)?;
    mbr.write_all(SQUASHFS)?;
    mbr.write_all(INVALID_CHS)?;
    mbr.write_all(&(2048 + 256 * MiB / 512).to_le_bytes())?;
    mbr.write_all(&(256 * MiB / 512).to_le_bytes())?;

    // Partition 3: rootfs B
    mbr.write_all(INACTIVE)?;
    mbr.write_all(INVALID_CHS)?;
    mbr.write_all(SQUASHFS)?;
    mbr.write_all(INVALID_CHS)?;
    mbr.write_all(&(2048 + 2 * (256 * MiB / 512)).to_le_bytes())?;
    mbr.write_all(&(256 * MiB / 512).to_le_bytes())?;

    // Partition 4: data
    mbr.write_all(INACTIVE)?;
    mbr.write_all(INVALID_CHS)?;
    mbr.write_all(LINUX)?;
    mbr.write_all(INVALID_CHS)?;
    mbr.write_all(&(2048 + 3 * (256 * MiB / 512)).to_le_bytes())?;
    mbr.write_all(&(dev_size as u32 / 512 - 2048 - 3 * (256 * MiB / 512)).to_le_bytes())?;

    mbr.write_all(SIGNATURE)?;

    println!("Partition table created successfully");
    Ok(())
}

fn update_instance(args: Args) -> anyhow::Result<()> {
    let mut mbr_buf = Vec::new();
    mbr_buf.resize(512, 0);

    let mut boot_buf = Vec::new();
    boot_buf.resize((256 * MiB).try_into()?, 0);

    // We only need to populate one of the two root partitions.
    let mut root_buf = Vec::new();
    root_buf.resize((256 * MiB).try_into()?, 0);

    let mut mbr_file = NamedTempFile::new()?;
    let mut boot_file = NamedTempFile::new()?;
    let mut root_file = NamedTempFile::new()?;

    mbr_file.write_all(&mbr_buf)?;
    boot_file.write_all(&boot_buf)?;
    root_file.write_all(&root_buf)?;

    let mut mbr = StreamSlice::new(mbr_file, 0, 512)?;
    let mut boot = StreamSlice::new(boot_file, 0, (256 * MiB).into())?;
    let mut root = StreamSlice::new(root_file, 0, (256 * MiB).into())?;

    write_mbr_partition_table(&mut mbr, args.size)?;

    let buf = write_boot(&mut boot, &args.arch)?;
    write_mbr(&mut mbr, &mut boot, &buf["vmlinuz"], &buf["cmdline.txt"])?;
    write_root(&mut root, &args.arch, &args.crates, &args.git, &args.init)?;

    mbr.rewind()?;
    boot.rewind()?;
    root.rewind()?;

    mbr.read_to_end(&mut mbr_buf)?;
    boot.read_to_end(&mut boot_buf)?;
    root.read_to_end(&mut root_buf)?;

    let clt = Client::builder()
        .danger_accept_invalid_certs(true)
        .pool_idle_timeout(None)
        .timeout(None)
        .build()?;

    let base = Url::parse(&args.update)?;

    println!("Uploading boot partition...");
    upload(&clt, base.join("/update/boot")?, boot_buf)?;

    println!("Uploading MBR...");
    upload(&clt, base.join("/update/mbr")?, mbr_buf)?;

    println!("Uploading root partition...");
    upload(&clt, base.join("/update/root")?, root_buf)?;

    println!("Rebooting...");
    reboot(clt, base);

    Ok(())
}

fn upload(clt: &Client, dst: Url, buf: Vec<u8>) -> anyhow::Result<()> {
    let resp = clt
        .put(dst)
        .header(CONTENT_TYPE, "application/octet-stream")
        .body(buf)
        .send()?;

    match resp.error_for_status_ref() {
        Ok(_) => {}
        Err(e) => {
            println!("Rustkrazy instance returned an error: {}", resp.text()?);
            return Err(e.into());
        }
    }

    Ok(())
}

fn reboot(clt: Client, base: Url) {
    thread::spawn(move || clt.post(base.join("/reboot").unwrap()).send().unwrap());
    thread::sleep(Duration::from_secs(1));
}

fn write_boot(
    partition: &mut StreamSlice<NamedTempFile>,
    arch: &str,
) -> anyhow::Result<BTreeMap<String, Vec<u8>>> {
    match arch {
        "x86_64" => {}
        "rpi" => {}
        _ => bail!("invalid architecture (supported: x86_64 rpi)"),
    }

    let format_opts = FormatVolumeOptions::new().fat_type(FatType::Fat32);

    fatfs::format_volume(&mut *partition, format_opts)?;

    let fs = fatfs::FileSystem::new(partition, fatfs::FsOptions::new())?;
    let root_dir = fs.root_dir();

    println!("Updating kernel...");

    let mut buf = BTreeMap::new();

    let mut copy = BTreeMap::new();

    copy.insert("vmlinuz", format!("vmlinuz-{}", arch));
    copy.insert("cmdline.txt", String::from("cmdline.txt"));
    copy.insert("config.txt", String::from("config.txt"));

    for (dst, src) in copy {
        let mut file = root_dir.create_file(dst)?;

        let mut resp = reqwest::blocking::get(KERNEL_BASE.to_owned() + &src)?.error_for_status()?;

        buf.insert(dst.to_owned(), Vec::new());
        resp.copy_to(buf.get_mut(dst).unwrap())?;
        io::copy(&mut buf.get(dst).unwrap().as_slice(), &mut file)?;
    }

    // We don't need the firmware to boot on other supported architectures.
    if arch == "rpi" {
        println!("Updating RPi dtbs...");

        let dtbcopy = [
            "bcm2710-rpi-3-b.dtb",
            "bcm2710-rpi-3-b-plus.dtb",
            "bcm2710-rpi-cm3.dtb",
            "bcm2711-rpi-4-b.dtb",
            "bcm2710-rpi-zero-2-w.dtb",
        ];

        for dtb in dtbcopy {
            println!("Updating RPi dtb: {}", dtb);

            let mut file = root_dir.create_file(dtb)?;

            let mut resp =
                reqwest::blocking::get(KERNEL_BASE.to_owned() + dtb)?.error_for_status()?;
            resp.copy_to(&mut file)?;
        }

        println!("Updating RPi firmware...");

        let fwcopy = [
            "bootcode.bin",
            "fixup.dat",
            "fixup4.dat",
            "fixup4cd.dat",
            "fixup4db.dat",
            "fixup4x.dat",
            "fixup_cd.dat",
            "fixup_db.dat",
            "fixup_x.dat",
            "start.elf",
            "start4.elf",
            "start4cd.elf",
            "start4db.elf",
            "start4x.elf",
            "start_cd.elf",
            "start_db.elf",
            "start_x.elf",
        ];

        for fw in fwcopy {
            println!("Updating RPi firmware: {}", fw);

            let mut file = root_dir.create_file(fw)?;

            let mut resp =
                reqwest::blocking::get(FIRMWARE_BASE.to_owned() + fw)?.error_for_status()?;
            resp.copy_to(&mut file)?;
        }
    }

    println!("Boot filesystem created successfully");
    Ok(buf)
}

fn write_mbr(
    mbr: &mut StreamSlice<NamedTempFile>,
    boot: &mut StreamSlice<NamedTempFile>,
    kernel_buf: &[u8],
    cmdline_buf: &[u8],
) -> anyhow::Result<()> {
    let mut buf = Vec::new();
    boot.read_to_end(&mut buf)?;

    let kernel_offset: u32 = (buf
        .windows(kernel_buf.len())
        .position(|window| window == kernel_buf)
        .expect("can't find kernel (/vmlinuz) on boot partition")
        / 512
        + 1)
    .try_into()?;
    let cmdline_offset: u32 = (buf
        .windows(cmdline_buf.len())
        .position(|window| window == cmdline_buf)
        .expect("can't find cmdline (/cmdline.txt) on boot partition")
        / 512
        + 1)
    .try_into()?;

    let kernel_lba = kernel_offset + 2048;
    let cmdline_lba = cmdline_offset + 2048;

    let mut bootloader_params = Vec::new();
    bootloader_params.extend_from_slice(&kernel_lba.to_le_bytes());
    bootloader_params.extend_from_slice(&cmdline_lba.to_le_bytes());

    let mut bootloader_file = File::open("boot.bin")?;
    let mut bootloader_buf = Vec::new();
    bootloader_file.read_to_end(&mut bootloader_buf)?;
    bootloader_buf.resize(432, 0);

    mbr.rewind()?;
    mbr.write_all(&bootloader_buf[..432])?;
    mbr.write_all(&bootloader_params)?;

    println!("MBR updated successfully");
    println!("MBR summary:");
    println!("  LBA: vmlinuz={}, cmdline.txt={}", kernel_lba, cmdline_lba);

    Ok(())
}

fn write_root(
    root: &mut StreamSlice<NamedTempFile>,
    arch: &str,
    crates: &Vec<String>,
    git: &Vec<String>,
    init: &str,
) -> anyhow::Result<()> {
    let target = match arch {
        "x86_64" => "x86_64",
        "rpi" => "aarch64",
        _ => bail!("invalid architecture (supported: x86_64 rpi)"),
    };

    let target_triple = format!("{}-unknown-linux-musl", target);

    println!("Installing crates: {:?}", crates);
    println!("Installing git: {:?}", git);

    let tmp_dir = tempfile::tempdir()?;

    let mut cargo_opts = CargoConfig::default()?;
    let mut compile_opts = CompileOptions::new(&CargoConfig::default()?, CompileMode::Build)?;

    cargo_opts.configure(0, false, None, false, false, false, &None, &[], &[])?;
    compile_opts.build_config = BuildConfig::new(
        &CargoConfig::default()?,
        None,
        false,
        &[target_triple],
        CompileMode::Build,
    )?;
    compile_opts.build_config.requested_profile = InternedString::new("release");

    if arch == "rpi" {
        let rustc_args = vec![
            String::from("-C"),
            String::from("linker=aarch64-linux-gnu-ld"),
        ];

        compile_opts.target_rustc_args = Some(rustc_args);
    }

    for crate_name in crates {
        compile_opts.filter = CompileFilter::single_bin(crate_name.to_owned());

        cargo::ops::install(
            &cargo_opts,
            Some(tmp_dir.path().to_str().unwrap()), // root (output dir)
            vec![(crate_name, None)],
            SourceId::crates_io(&CargoConfig::default()?)?,
            false, // from_cwd
            &compile_opts,
            false, // force
            true,  // no_track
        )?;
    }

    for location in git {
        let mut split = location.split('%');

        let url = Url::parse(split.next().unwrap())?;

        let pkg = split.next().unwrap_or(
            url.path_segments()
                .unwrap()
                .next_back()
                .unwrap()
                .trim_end_matches(".git"),
        );

        compile_opts.filter = CompileFilter::single_bin(pkg.to_owned());

        cargo::ops::install(
            &cargo_opts,
            Some(tmp_dir.path().to_str().unwrap()), // root (output dir)
            vec![(pkg, None)],
            SourceId::from_url(&("git+".to_owned() + url.as_str()))?,
            false, // from_cwd
            &compile_opts,
            false, // force
            true,  // no_track
        )?;
    }

    let mut tmp_file = NamedTempFile::new()?;
    io::copy(root, &mut tmp_file)?;

    let tree = SqsTreeProcessor::new(tmp_file.path())?;

    let mut crate_inodes = Vec::new();

    for pkg in crates {
        let crate_path = tmp_dir.path().join("bin/".to_owned() + pkg);
        let crate_file = File::open(crate_path)?;

        crate_inodes.push(tree.add(SqsSourceFile {
            path: Path::new("/bin").join(if pkg == init { "init" } else { pkg }),
            content: SqsSource {
                data: SqsSourceData::File(Box::new(crate_file)),
                uid: 0,
                gid: 0,
                mode: 0o755,
                modified: 0,
                xattrs: HashMap::new(),
                flags: 0,
            },
        })?);
    }

    for location in git {
        let mut split = location.split('%');

        let url = Url::parse(split.next().unwrap())?;

        let pkg = split.next().unwrap_or(
            url.path_segments()
                .unwrap()
                .next_back()
                .unwrap()
                .trim_end_matches(".git"),
        );

        let crate_path = tmp_dir.path().join("bin/".to_owned() + pkg);
        let crate_file = File::open(crate_path)?;

        crate_inodes.push(tree.add(SqsSourceFile {
            path: Path::new("/bin").join(if pkg == init { "init" } else { pkg }),
            content: SqsSource {
                data: SqsSourceData::File(Box::new(crate_file)),
                uid: 0,
                gid: 0,
                mode: 0o755,
                modified: 0,
                xattrs: HashMap::new(),
                flags: 0,
            },
        })?);
    }

    let init2 = String::from(init);

    let bin_inode = tree.add(SqsSourceFile {
        path: PathBuf::from("/bin"),
        content: SqsSource {
            data: SqsSourceData::Dir(Box::new(
                crates
                    .clone()
                    .into_iter()
                    .map(move |pkg| {
                        if pkg == init2 {
                            String::from("init")
                        } else {
                            pkg
                        }
                    })
                    .map(OsString::from)
                    .zip(crate_inodes.into_iter()),
            )),
            uid: 0,
            gid: 0,
            mode: 0o755,
            modified: 0,
            xattrs: HashMap::new(),
            flags: 0,
        },
    })?;

    let dev_inode = tree.add(SqsSourceFile {
        path: PathBuf::from("/dev"),
        content: SqsSource {
            data: SqsSourceData::Dir(Box::new(Vec::new().into_iter())),
            uid: 0,
            gid: 0,
            mode: 0o755,
            modified: 0,
            xattrs: HashMap::new(),
            flags: 0,
        },
    })?;

    let boot_inode = tree.add(SqsSourceFile {
        path: PathBuf::from("/boot"),
        content: SqsSource {
            data: SqsSourceData::Dir(Box::new(Vec::new().into_iter())),
            uid: 0,
            gid: 0,
            mode: 0o755,
            modified: 0,
            xattrs: HashMap::new(),
            flags: 0,
        },
    })?;

    let data_inode = tree.add(SqsSourceFile {
        path: PathBuf::from("/data"),
        content: SqsSource {
            data: SqsSourceData::Dir(Box::new(Vec::new().into_iter())),
            uid: 0,
            gid: 0,
            mode: 0o755,
            modified: 0,
            xattrs: HashMap::new(),
            flags: 0,
        },
    })?;

    let proc_inode = tree.add(SqsSourceFile {
        path: PathBuf::from("/proc"),
        content: SqsSource {
            data: SqsSourceData::Dir(Box::new(Vec::new().into_iter())),
            uid: 0,
            gid: 0,
            mode: 0o755,
            modified: 0,
            xattrs: HashMap::new(),
            flags: 0,
        },
    })?;

    let tmp_inode = tree.add(SqsSourceFile {
        path: PathBuf::from("/tmp"),
        content: SqsSource {
            data: SqsSourceData::Dir(Box::new(Vec::new().into_iter())),
            uid: 0,
            gid: 0,
            mode: 0o755,
            modified: 0,
            xattrs: HashMap::new(),
            flags: 0,
        },
    })?;

    let run_inode = tree.add(SqsSourceFile {
        path: PathBuf::from("/run"),
        content: SqsSource {
            data: SqsSourceData::Dir(Box::new(Vec::new().into_iter())),
            uid: 0,
            gid: 0,
            mode: 0o755,
            modified: 0,
            xattrs: HashMap::new(),
            flags: 0,
        },
    })?;

    tree.add(SqsSourceFile {
        path: PathBuf::from("/"),
        content: SqsSource {
            data: SqsSourceData::Dir(Box::new(
                vec![
                    (OsString::from("bin"), bin_inode),
                    (OsString::from("dev"), dev_inode),
                    (OsString::from("boot"), boot_inode),
                    (OsString::from("data"), data_inode),
                    (OsString::from("proc"), proc_inode),
                    (OsString::from("tmp"), tmp_inode),
                    (OsString::from("run"), run_inode),
                ]
                .into_iter(),
            )),
            uid: 0,
            gid: 0,
            mode: 0o755,
            modified: 0,
            xattrs: HashMap::new(),
            flags: 0,
        },
    })?;

    tree.finish()?;

    tmp_file.rewind()?;
    root.rewind()?;
    io::copy(&mut tmp_file, root)?;

    println!("Root filesystem updated successfully");
    Ok(())
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    match args.arch.as_str() {
        "x86_64" => {}
        "rpi" => {}
        _ => bail!("invalid architecture (supported: x86_64 rpi)"),
    }

    let init_in_crates = args.crates.iter().any(|pkg| *pkg == args.init);
    let init_in_git = args.git.iter().any(|location| {
        let mut split = location.split('%');

        let url = match Url::parse(split.next().unwrap()) {
            Ok(url) => url,
            Err(e) => {
                println!("Invalid git crate {}: {}", location, e);
                return false;
            }
        };

        let pkg = split.next().unwrap_or(
            url.path_segments()
                .unwrap()
                .next_back()
                .unwrap()
                .trim_end_matches(".git"),
        );

        pkg == args.init
    });

    if !init_in_crates && !init_in_git {
        bail!("Init must be listed in crates to install");
    }

    update_instance(args)?;
    Ok(())
}
