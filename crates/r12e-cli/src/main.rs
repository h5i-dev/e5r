//! The `r12e` command line.
//!
//! A thin client: it parses arguments, calls the library, and prints. Every
//! command takes `--json`, and the JSON is the same facts the text shows.

// One unsafe block, in `map_file`: memory-mapping a file is inherently
// unsafe because another process can truncate it underneath us. Denied rather
// than forbidden so that one audited call can opt in with a written reason.
#![deny(unsafe_code)]

mod addr;
mod annotate;
mod json;
mod mcp;
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
    /// Annotation log to use. Defaults to the binary's path plus `.r12e`.
    #[arg(long, global = true)]
    db: Option<PathBuf>,
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
    /// Compare two builds and say which functions changed.
    ///
    /// Matching runs strongest evidence first: identical bytes, then the
    /// instruction shape, then names, then position in the call graph.
    /// Changed functions are reported most changed first, which is the order a
    /// patch diff is read in.
    Diff {
        #[command(flatten)]
        common: Common,
        /// The other build to compare against.
        other: PathBuf,
        /// Also list the pairs that did not change.
        #[arg(long)]
        all: bool,
    },
    /// Decompile a function to pseudo-C.
    ///
    /// The output says what the machine does in C's notation; it does not claim
    /// to be the source. Where the control flow does not fit a loop or a
    /// branch, a labelled goto appears rather than a shape that is not there,
    /// and the count is printed.
    Decompile {
        #[command(flatten)]
        common: Common,
        /// Address, symbol, or `all`.
        target: String,
    },
    /// Report what the pointers a function takes appear to point at.
    ///
    /// Inferred from the offsets the code touches through them, which is
    /// evidence rather than a declaration: it says what was seen, not what the
    /// type was.
    Shapes {
        #[command(flatten)]
        common: Common,
        /// Address, symbol, or `all`.
        target: String,
    },
    /// Ask a question about the program.
    ///
    /// `functions where insns > 100 and name ~ "crypt"`, and the same shape
    /// for strings, symbols, imports, exports, sections and xrefs.
    Query {
        #[command(flatten)]
        common: Common,
        /// The query.
        query: Vec<String>,
    },
    /// Build and apply function signatures.
    ///
    /// A signature identifies a function by what it is rather than where it
    /// is, so a library built from a binary with symbols names the same code
    /// in one without them.
    Sig {
        #[command(subcommand)]
        what: SigCommand,
        #[command(flatten)]
        common: Common,
    },
    /// Speak the Model Context Protocol on stdin and stdout, so an agent can
    /// drive the analysis.
    Mcp,
    /// Read and write the annotation log.
    ///
    /// The log is a text file git can merge: every assertion is one line keyed
    /// to a content anchor, so the work survives a rebuild and two analysts on
    /// separate branches merge without conflict markers.
    Annotate {
        #[command(flatten)]
        common: Common,
        #[command(subcommand)]
        what: Annotation,
    },
}

/// What to do with signatures.
#[derive(Subcommand)]
enum SigCommand {
    /// Write a signature for every named function.
    Create {
        /// Where to write them; standard output when absent.
        #[arg(short, long)]
        out: Option<PathBuf>,
    },
    /// Name what a signature library recognizes.
    Apply {
        /// The signature file.
        library: PathBuf,
    },
}

/// What to do to the annotation log.
#[derive(Subcommand)]
enum Annotation {
    /// Name a function or an address.
    Name {
        /// Address or symbol.
        target: String,
        /// The name. Omit to clear it.
        value: Option<String>,
    },
    /// Attach a comment.
    Comment {
        /// Address or symbol.
        target: String,
        /// The text. Omit to clear it.
        value: Option<String>,
    },
    /// Record a type or prototype.
    Type {
        /// Address or symbol.
        target: String,
        /// The type, as source text. Omit to clear it.
        value: Option<String>,
    },
    /// Show everything the log says about this binary.
    List,
    /// Take back the most recent assertion.
    Undo,
    /// Put back the most recently undone assertion.
    Redo,
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
            Command::Annotate { common, .. } | Command::Diff { common, .. } => common,
            // The server takes its paths per call rather than up front.
            Command::Mcp => unreachable!("handled before a file is opened"),
            Command::Query { common, .. }
            | Command::Sig { common, .. }
            | Command::Disas { common, .. }
            | Command::Decompile { common, .. }
            | Command::Shapes { common, .. }
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
    // The server opens files itself, one per tool call.
    if matches!(cli.command, Command::Mcp) {
        return mcp::serve();
    }
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
        debug_info: true,
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
    if matches!(cli.command, Command::Annotate { .. } | Command::Diff { .. }) {
        opts.strings = false;
        opts.xrefs = false;
    }

    let mut program = r12e_analysis::analyze(object, &opts);

    // Names from the log override what the container said, because the point
    // of writing one down was to overrule the engine.
    let db = common
        .db
        .clone()
        .unwrap_or_else(|| annotate::default_path(&common.file));
    if !matches!(cli.command, Command::Annotate { .. }) {
        for (at, name, _) in annotate::names(&program, &db) {
            if let Some(f) = program.functions.get_mut(&at) {
                f.name = Some(name);
            }
        }
    }

    match &cli.command {
        Command::Funcs(c) => print::funcs(w, &program, c.json),
        Command::Stats(c) => print::stats(w, &program, c.json),
        Command::Strings { common, .. } => print::strings(w, &program, common.json),
        Command::Disas {
            common,
            target,
            bytes,
        } => print::disas(w, &program, target, *bytes, common.json),
        Command::Decompile { common, target } => {
            print::decompile(w, &program, target, common.json)
        }
        Command::Shapes { common, target } => print::shapes(w, &program, target, common.json),
        Command::Query { common, query } => {
            print::query(w, &program, &query.join(" "), common.json)
        }
        Command::Sig { what, common } => match what {
            SigCommand::Create { out } => {
                let library = r12e_api::collect_signatures(
                    &program,
                    &common.file.file_name().unwrap_or_default().to_string_lossy(),
                );
                match out {
                    Some(path) => {
                        std::fs::write(path, library.to_text())
                            .map_err(|e| format!("{}: {e}", path.display()))?;
                        eprintln!("{} signature(s) written", library.len());
                        Ok(exit::OK)
                    }
                    None => {
                        for line in library.to_text().lines() {
                            out::outln!(w, "{line}");
                        }
                        Ok(exit::OK)
                    }
                }
            }
            SigCommand::Apply { library } => {
                let text = std::fs::read_to_string(library)
                    .map_err(|e| format!("{}: {e}", library.display()))?;
                let library = r12e_db::signature::Library::from_text(&text);
                print::identified(w, &program, &library, common.json)
            }
        },
        Command::Xrefs {
            common,
            target,
            from,
        } => print::xrefs(w, &program, target, *from, common.json),
        Command::Diff { common, other, all } => {
            let other_data = std::fs::File::open(other)
                .and_then(|f| map_file(&f))
                .map_err(|e| format!("{}: {e}", other.display()))?;
            let other_obj =
                r12e_format::load(&other_data, &load_opts).map_err(|e| e.to_string())?;
            let other_prog = r12e_analysis::analyze(other_obj, &opts);
            print::diff(w, &program, &other_prog, *all, common.json)
        }
        Command::Annotate { what, common } => {
            let who = whoami();
            match what {
                Annotation::Name { target, value } => annotate::set(
                    w,
                    &program,
                    &db,
                    r12e_db::Field::Name,
                    target,
                    value.clone(),
                    &who,
                ),
                Annotation::Comment { target, value } => annotate::set(
                    w,
                    &program,
                    &db,
                    r12e_db::Field::Comment,
                    target,
                    value.clone(),
                    &who,
                ),
                Annotation::Type { target, value } => annotate::set(
                    w,
                    &program,
                    &db,
                    r12e_db::Field::Type,
                    target,
                    value.clone(),
                    &who,
                ),
                Annotation::List => annotate::list(w, &program, &db, common.json),
                Annotation::Undo => annotate::step(w, &db, false),
                Annotation::Redo => annotate::step(w, &db, true),
            }
        }
        _ => unreachable!("handled above"),
    }
}

/// Who to record as the author of an assertion.
///
/// The environment, then the OS user, then a placeholder. Never a hostname or
/// anything else that would leak more than a name into a file meant for a pull
/// request.
fn whoami() -> String {
    std::env::var("R12E_AUTHOR")
        .or_else(|_| std::env::var("USER"))
        .or_else(|_| std::env::var("USERNAME"))
        .unwrap_or_else(|_| "unknown".to_string())
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
