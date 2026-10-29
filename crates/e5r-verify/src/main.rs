//! `e5r-verify`: export binaries for the Lean checker.
//!
//! `e5r-verify IMAGE.elf` is the V0 research export (strict RV32I subset).
//! `e5r-verify flash --board BOARD.json [--namespace NS] IMAGE.elf` exports
//! the flash contents a board boots from.
use std::process::ExitCode;

fn run(args: Vec<String>) -> Result<String, String> {
    let read = |p: &str| std::fs::read(p).map_err(|e| format!("{p}: {e}"));
    match args.first().map(String::as_str) {
        Some("flash") => {
            let mut board = None;
            let mut ns = "Image".to_string();
            let mut elf = None;
            let mut it = args[1..].iter();
            while let Some(a) = it.next() {
                match a.as_str() {
                    "--board" => board = it.next().cloned(),
                    "--namespace" => ns = it.next().cloned().ok_or("--namespace needs a value")?,
                    _ if elf.is_none() && !a.starts_with('-') => elf = Some(a.clone()),
                    _ => return Err(format!("unexpected argument {a}")),
                }
            }
            let board = board.ok_or("flash needs --board BOARD.json")?;
            let elf = elf.ok_or("flash needs an ELF path")?;
            let text = String::from_utf8(read(&board)?).map_err(|e| e.to_string())?;
            let w = e5r_verify::board::Board::parse(&text)?.windows()?;
            e5r_verify::flash::export_flash(&read(&elf)?, w, &ns)
        }
        Some(path) if args.len() == 1 && !path.starts_with('-') => e5r_verify::export(&read(path)?),
        _ => Err("usage: e5r-verify IMAGE.elf | e5r-verify flash --board BOARD.json [--namespace NS] IMAGE.elf".into()),
    }
}

fn main() -> ExitCode {
    match run(std::env::args().skip(1).collect()) {
        Ok(source) => {
            print!("{source}");
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("e5r-verify: {e}");
            ExitCode::FAILURE
        }
    }
}
