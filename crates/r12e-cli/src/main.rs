//! The `r12e` command line.
//!
//! A thin client: it parses arguments, calls the library, and prints. Every
//! command takes `--json`, and the JSON is the same facts the text shows.

// One unsafe block, in `map_file`: memory-mapping a file is inherently
// unsafe because another process can truncate it underneath us. Denied rather
// than forbidden so that one audited call can opt in with a written reason.
#![deny(unsafe_code)]

mod addr;
mod json;
mod out;
mod print;

use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Args, Parser, Subcommand};
use r12e_analysis::Options;
use r12e_core::{Addr, Arch, Caps};
use r12e_format::LoadOptions;

/// Exit codes, so a script can branch on the outcome.
mod exit {
    /// Everything worked.
    pub const OK: u8 = 0;
    /// The command ran but found nothing matching.
    pub const NOT_FOUND: u8 = 1;
    /// The arguments did not make sense. clap exits with this itself; the
    /// constant is here so the documented set is complete.
    #[allow(dead_code)]
    pub const USAGE: u8 = 2;
    /// The file could not be read or parsed.
    pub const BAD_INPUT: u8 = 3;
}

#[derive(Parser)]
#[command(
    name = "r12e",
    version,
    about = "Reverse engineering from the command line",
    long_about = "Loads a binary, recovers functions, disassembles, and reports \
                  what it found and why it believes it.\n\n\
                  Every command takes --json. Exit codes: 0 ok, 1 nothing found, \
                  2 bad usage, 3 bad input."
)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

/// Arguments shared by every command that opens a file.
#[derive(Args, Clone)]
struct Common {
    /// The binary to analyze.
    file: PathBuf,
    /// Emit JSON instead of text.
    #[arg(long, global = true)]
    json: bool,
    /// Threads for analysis. 0 or unset uses one per core.
    #[arg(long, global = true)]
    threads: Option<usize>,
    /// Load a headerless image at this base address.
    #[arg(long, value_parser = parse_u64)]
    base: Option<u64>,
    /// Architecture for a headerless image.
    #[arg(long)]
    arch: Option<String>,
    /// Skip the heuristic prologue scan, leaving only evidence-led discovery.
    #[arg(long)]
    no_scan: bool,
}

#[derive(Subcommand)]
enum Command {
    /// Container, architecture, entry point, and what the loader noticed.
    Info(Common),
    /// Sections and their mapping.
    Sections(Common),
    /// Symbols the container names.
    Symbols(Common),
    /// Symbols needed from elsewhere.
    Imports(Common),
    /// Symbols offered to others.
    Exports(Common),
    /// Recovered functions, with the evidence for each.
    Funcs(Common),
    /// Disassemble a function, a range, or everything.
    Disas {
        #[command(flatten)]
        common: Common,
        /// A symbol name, an address, or `all`. Defaults to every function.
        #[arg(default_value = "all")]
        target: String,
        /// Show the raw encoding beside each instruction.
        #[arg(long)]
        bytes: bool,
    },
    /// References to or from an address.
    Xrefs {
        #[command(flatten)]
        common: Common,
        /// The address or symbol to ask about.
        target: String,
        /// Show what it points at rather than what points at it.
        #[arg(long)]
        from: bool,
    },
    /// Strings found in the image.
    Strings {
        #[command(flatten)]
        common: Common,
        /// Shortest run to report.
        #[arg(long, default_value_t = 4)]
        min: usize,
        /// Also scan executable memory, which is noisy.
        #[arg(long)]
        in_code: bool,
    },
    /// Counts: functions, blocks, instructions, references, strings.
    Stats(Common),
}

impl Command {
    fn common(&self) -> &Common {
        match self {
            Command::Info(c)
            | Command::Sections(c)
            | Command::Symbols(c)
            | Command::Imports(c)
            | Command::Exports(c)
            | Command::Funcs(c)
            | Command::Stats(c) => c,
            Command::Disas { common, .. }
            | Command::Xrefs { common, .. }
            | Command::Strings { common, .. } => common,
        }
    }
}

fn parse_u64(s: &str) -> Result<u64, String> {
    addr::parse_number(s).ok_or_else(|| format!("{s:?} is not a number"))
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    let mut w = out::Out::new();
    let result = run(&cli, &mut w);
    // A reader that went away is the normal end of `... | head`, not a failure.
    let piped_out = !w.finish();
    match result {
        Ok(code) => ExitCode::from(if piped_out { exit::OK } else { code }),
        Err(e) => {
            eprintln!("r12e: {e}");
            ExitCode::from(exit::BAD_INPUT)
        }
    }
}

fn run(cli: &Cli, w: &mut out::Out) -> Result<u8, String> {
    let common = cli.command.common();

    let file =
        std::fs::File::open(&common.file).map_err(|e| format!("{}: {e}", common.file.display()))?;
    // Memory-mapped: opening a 500 MB binary should not copy it.
    let data = map_file(&file).map_err(|e| format!("{}: {e}", common.file.display()))?;

    let arch = match &common.arch {
        Some(a) => Some(
            a.parse::<Arch>()
                .map_err(|e| format!("{e}; try x86-64, aarch64, arm or x86"))?,
        ),
        None => None,
    };
    let load_opts = LoadOptions {
        caps: Caps::default(),
        base: common.base.map(Addr),
        arch,
        eh_frame: true,
    };
    let object = r12e_format::load(&data, &load_opts).map_err(|e| e.to_string())?;

    // Commands that only need the container skip analysis entirely, which is
    // what makes `info` on a 500 MB binary instant.
    match &cli.command {
        Command::Info(c) => return print::info(w, &object, c.json),
        Command::Sections(c) => return print::sections(w, &object, c.json),
        Command::Symbols(c) => return print::symbols(w, &object, c.json),
        Command::Imports(c) => return print::imports(w, &object, c.json),
        Command::Exports(c) => return print::exports(w, &object, c.json),
        _ => {}
    }

    let mut opts = Options {
        threads: common.threads,
        ..Options::default()
    };
    if common.no_scan {
        opts.scan_gaps = false;
    }
    if let Command::Strings { min, in_code, .. } = &cli.command {
        opts.string_opts.min_len = *min;
        opts.string_opts.in_code = *in_code;
        // Nothing else is needed for a string scan.
        opts.follow_calls = false;
        opts.scan_gaps = false;
        opts.xrefs = false;
    }
    if matches!(cli.command, Command::Funcs(_) | Command::Stats(_)) {
        opts.strings = matches!(cli.command, Command::Stats(_));
    }

    let program = r12e_analysis::analyze(object, &opts);

    match &cli.command {
        Command::Funcs(c) => print::funcs(w, &program, c.json),
        Command::Stats(c) => print::stats(w, &program, c.json),
        Command::Strings { common, .. } => print::strings(w, &program, common.json),
        Command::Disas {
            common,
            target,
            bytes,
        } => print::disas(w, &program, target, *bytes, common.json),
        Command::Xrefs {
            common,
            target,
            from,
        } => print::xrefs(w, &program, target, *from, common.json),
        _ => unreachable!("handled above"),
    }
}

/// Map the file read-only, so opening a 500 MB binary does not copy it.
///
/// The obligation is that nothing truncates the file while the mapping lives.
/// Nothing here writes to it, and the mapping is dropped when the command
/// ends; a truncation racing the read is a corrupted read, which the loaders
/// already treat as ordinary hostile input.
#[allow(unsafe_code)]
fn map_file(file: &std::fs::File) -> std::io::Result<memmap2::Mmap> {
    unsafe { memmap2::Mmap::map(file) }
}
