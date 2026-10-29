//! Export a strict static RV32I ELF to Lean on standard output.
fn main() {
    let result = (|| {
        let mut args = std::env::args_os().skip(1);
        let path = args.next().ok_or("usage: e5r-verify IMAGE.elf")?;
        if args.next().is_some() {
            return Err("usage: e5r-verify IMAGE.elf".to_string());
        }
        let bytes = std::fs::read(path).map_err(|e| e.to_string())?;
        e5r_verify::export(&bytes)
    })();
    match result {
        Ok(source) => print!("{source}"),
        Err(e) => {
            eprintln!("e5r-verify: {e}");
            std::process::exit(1);
        }
    }
}
