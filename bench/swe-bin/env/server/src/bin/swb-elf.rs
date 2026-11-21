//! `swb-elf link BIN OBJ OUT`, `swb-elf stub BIN OUT NAME...`, `swb-elf check BIN`: the ELF
//! rewrites of the environment (src/elf.rs), as a command for the converter and the tests.

use std::process::ExitCode;
use swe_bin_env::elf;

fn run(args: &[String]) -> Result<String, String> {
    let read = |p: &str| std::fs::read(p).map_err(|e| format!("{p}: {e}"));
    match args {
        [cmd, bin, obj, out] if cmd == "link" => {
            let (img, r) = elf::link(&read(bin)?, &read(obj)?).map_err(|e| e.to_string())?;
            write_exe(out, &img)?;
            Ok(format!("segment {:#x} ({} bytes); replaced: {}; added: {}",
                r.segment.0, r.segment.1, r.replaced.join(" "), r.added.join(" ")))
        }
        [cmd, bin, out, names @ ..] if cmd == "stub" && !names.is_empty() => {
            let (img, done) = elf::stub(&read(bin)?, names).map_err(|e| e.to_string())?;
            write_exe(out, &img)?;
            Ok(done.iter().map(|(n, k)| format!("{n} {k}")).collect::<Vec<_>>().join("\n"))
        }
        [cmd, bin, func, out] if cmd == "isolate" => {
            let img = elf::isolate(&read(bin)?, func).map_err(|e| e.to_string())?;
            std::fs::write(out, img).map_err(|e| e.to_string())?;
            Ok(format!("{out}: every function but {func} is `ret`"))
        }
        [cmd, bin, out, names @ ..] if cmd == "extract" && !names.is_empty() => {
            let obj = elf::extract(&read(bin)?, names).map_err(|e| e.to_string())?;
            std::fs::write(out, obj).map_err(|e| e.to_string())?;
            Ok(format!("{out}: {}", names.join(" ")))
        }
        [cmd, bin] if cmd == "check" => {
            elf::check_submission(&read(bin)?).map_err(|e| e.to_string())?;
            Ok("ok: a static RISC-V 64 executable".into())
        }
        _ => Err("usage: swb-elf link BIN OBJ OUT | stub BIN OUT NAME... | isolate BIN FUNC OUT | extract BIN OUT.o NAME... | check BIN".into()),
    }
}

fn write_exe(path: &str, img: &[u8]) -> Result<(), String> {
    use std::os::unix::fs::PermissionsExt;
    std::fs::write(path, img).map_err(|e| format!("{path}: {e}"))?;
    std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o755)).map_err(|e| format!("{path}: {e}"))
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match run(&args) {
        Ok(s) => {
            println!("{s}");
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("swb-elf: {e}");
            ExitCode::FAILURE
        }
    }
}
