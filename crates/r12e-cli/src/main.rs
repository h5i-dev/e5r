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
mod batch;
mod budget;
mod json;
mod mcp;
mod out;
mod patch;
mod print;
mod progress;
mod repl;
mod shell;

use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Args, CommandFactory, Parser, Subcommand};
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
pub struct Cli {
    #[command(subcommand)]
    command: Command,
}

/// Arguments shared by every command that opens a file.
#[derive(Args, Clone)]
pub struct Common {
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
    /// When to colour the output. Piped output is never coloured under `auto`.
    #[arg(long, global = true, value_name = "WHEN", default_value = "auto")]
    color: out::When,
    /// Do not page, even when a terminal is reading.
    #[arg(long, global = true)]
    no_pager: bool,
    /// Stop after this many seconds and report what was finished.
    #[arg(long, global = true, value_name = "SECONDS")]
    budget: Option<f64>,
    /// Stop after this many items and report what was finished.
    #[arg(long, global = true, value_name = "N")]
    limit: Option<usize>,
    /// Show progress on stderr. Off when stderr is not a terminal.
    #[arg(long, global = true)]
    progress: bool,
}

#[derive(Subcommand)]
pub enum Command {
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
    /// List virtual tables and the classes they belong to.
    Vtables {
        #[command(flatten)]
        common: Common,
    },
    /// Recover C++ classes, their hierarchy and their member functions.
    ///
    /// From the type information where the binary has it, and from the virtual
    /// tables alone where it does not. Every claim says what it rests on: a
    /// name read out of RTTI is proven, one inferred from what a function
    /// writes is not, and the two are never printed as each other.
    Classes {
        #[command(flatten)]
        common: Common,
        /// Also list member functions and what each one touches through
        /// `this`. This lifts every member function, which on a real C++
        /// library takes tens of seconds.
        #[arg(long)]
        members: bool,
    },
    /// Run a function in the interpreter.
    ///
    /// The same machine the lifter's semantics gate uses, which is measured
    /// against what real hardware does. Nothing escapes the process: memory is
    /// a copy, a system call stops the run, and a budget bounds it.
    Emulate {
        #[command(flatten)]
        common: Common,
        /// Address or symbol of the function to run.
        target: String,
        /// Integer arguments, in the calling convention's order.
        #[arg(value_parser = parse_u64)]
        args: Vec<u64>,
        /// How deep to follow calls.
        #[arg(long, default_value_t = 64)]
        depth: u32,
        /// How many IR operations to allow.
        ///
        /// Not `--budget`, which is global and counts seconds. Two options
        /// with one name and two types is a clap panic at parse time, which is
        /// what this was: `r12e emulate` could not be run at all.
        #[arg(long, default_value_t = 1 << 22)]
        steps: u64,
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
    /// Run several commands over one file and print one document.
    ///
    /// For a caller that wants every answer at once: each line of the script
    /// is a command, and the results come back together with the command that
    /// produced each one, so nothing has to be matched up afterwards.
    Batch {
        #[command(flatten)]
        common: Common,
        /// A file of commands, one per line; `-` reads standard input.
        #[arg(short, long)]
        script: Option<PathBuf>,
        /// A command to run, repeatable.
        #[arg(short, long)]
        command: Vec<String>,
    },
    /// Record, preview and apply byte patches.
    ///
    /// An edit is anchored to the code around it, so a patch written against
    /// one build still lands on the right instruction in the next one. It
    /// carries the bytes it expects to find, and applies as a whole set or not
    /// at all.
    Patch {
        #[command(flatten)]
        common: Common,
        #[command(subcommand)]
        what: PatchCommand,
    },
    /// Save and reopen an analysis session.
    ///
    /// A project file names the binary by content as well as by path, so
    /// opening one against the wrong build says so rather than producing
    /// answers about bytes that are not there.
    Project {
        #[command(subcommand)]
        what: ProjectCommand,
    },
    /// Report an overlay, section entropy, and what they suggest.
    ///
    /// Findings are observations with a strength, never a verdict: a section
    /// that is writable and executable is a fact, and what put it there is
    /// not. A packer is named only when a section carries that packer's own
    /// signature.
    Overlay {
        #[command(flatten)]
        common: Common,
    },
    /// List the members of an `ar` archive.
    ///
    /// An archive holds objects rather than being one, so it is not loaded:
    /// picking a member silently would make every later answer about bytes
    /// the caller did not choose.
    Archive {
        #[command(flatten)]
        common: Common,
        /// Also list the symbols each member defines.
        #[arg(long)]
        symbols: bool,
    },
    /// Write a completion script for a shell.
    ///
    /// Generated from the command tree, so it cannot describe a command that
    /// does not exist.
    Completions {
        /// Which shell.
        shell: shell::Shell,
    },
    /// Write the manual page, in roff.
    Manpage,
    /// Speak the Model Context Protocol on stdin and stdout, so an agent can
    /// drive the analysis.
    Mcp,
    /// Open an interactive session.
    ///
    /// One analysis, many questions. The commands are the ones below, spelled
    /// the same way and without the file, so nothing has to be learned twice.
    /// Analyzing a large binary takes seconds, and a session that paid that
    /// per command would be unusable on exactly the binaries worth a session.
    Repl {
        #[command(flatten)]
        common: Common,
    },
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

/// What to do with a patch set.
#[derive(Subcommand)]
pub enum PatchCommand {
    /// Capture an edit from the binary as it is now.
    #[command(group = clap::ArgGroup::new("replacement").required(true).args(["bytes", "asm"]))]
    Record {
        /// Address or symbol to write at.
        target: String,
        /// The bytes to write, in hex.
        #[arg(long)]
        bytes: Option<String>,
        /// The instructions to write, assembled at the target address.
        ///
        /// Exclusive with `--bytes`: a patch whose two spellings disagree is
        /// one nobody can review.
        #[arg(long)]
        asm: Option<String>,
        /// Pad the edit to this many bytes with no-ops.
        ///
        /// An instruction that encodes shorter than the one it replaces leaves
        /// a hole, and the bytes after it are no longer the instructions they
        /// were.
        #[arg(long, value_name = "N")]
        pad_to: Option<usize>,
        /// Why.
        #[arg(long, default_value = "")]
        note: String,
        /// The patch set to add to, created when it does not exist.
        #[arg(short, long)]
        out: PathBuf,
    },
    /// List what a patch set says, without opening the binary.
    Show {
        /// The patch set.
        set: PathBuf,
    },
    /// Say where it would land and what it would overwrite.
    Preview {
        /// The patch set.
        set: PathBuf,
    },
    /// Write the patched binary.
    Apply {
        /// The patch set.
        set: PathBuf,
        /// Where to write. Defaults to refusing unless `--in-place`.
        #[arg(short, long)]
        out: Option<PathBuf>,
        /// Overwrite the binary itself.
        #[arg(long)]
        in_place: bool,
        /// Write even where an edit matched on its address alone.
        #[arg(long)]
        allow_address_only: bool,
    },
    /// Write the binary with the patch set taken back out.
    Revert {
        /// The patch set that was applied.
        set: PathBuf,
        /// Where to write.
        #[arg(short, long)]
        out: Option<PathBuf>,
        /// Overwrite the binary itself.
        #[arg(long)]
        in_place: bool,
        /// Refuse where an edit matched on its address alone.
        ///
        /// Off by default, because a patched binary no longer holds the bytes
        /// the anchor fingerprinted: that is what applying the patch did. The
        /// expected bytes still have to match, and they are the exact bytes
        /// the apply wrote.
        #[arg(long)]
        anchored_only: bool,
    },
    /// Write the set that undoes this one, without applying anything.
    Invert {
        /// The patch set.
        set: PathBuf,
        /// Where to write it.
        #[arg(short, long)]
        out: PathBuf,
    },
    /// Combine several sets into one.
    Merge {
        /// The sets, in the order they apply.
        sets: Vec<PathBuf>,
        /// Where to write the result.
        #[arg(short, long)]
        out: PathBuf,
    },
}

/// What to do with a project file.
#[derive(Subcommand)]
pub enum ProjectCommand {
    /// Record what it takes to reopen this session.
    New {
        /// The binary.
        binary: PathBuf,
        /// Where to write the project.
        #[arg(short, long)]
        out: PathBuf,
        /// An analysis option, as `key=value`. Repeatable.
        #[arg(long = "set")]
        settings: Vec<String>,
        /// The annotation log. Defaults to the binary's path plus `.r12e`.
        #[arg(long)]
        log: Option<PathBuf>,
    },
    /// Print a project file.
    Show {
        /// The project.
        project: PathBuf,
    },
    /// Say whether a binary is the one the project was made for.
    Verify {
        /// The project.
        project: PathBuf,
        /// The binary. Defaults to the path the project records.
        #[arg(long)]
        binary: Option<PathBuf>,
    },
    /// Attach a signature library, a patch set, or a log.
    Add {
        /// The project.
        project: PathBuf,
        /// A signature library. Repeatable.
        #[arg(long)]
        signatures: Vec<PathBuf>,
        /// A patch set. Repeatable.
        #[arg(long = "patch")]
        patches: Vec<PathBuf>,
        /// The annotation log.
        #[arg(long)]
        log: Option<PathBuf>,
    },
}

/// What to do with signatures.
#[derive(Subcommand)]
pub enum SigCommand {
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
pub enum Annotation {
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
    /// Colour and paging for this command, or `None` when its output is meant
    /// for a program rather than for a person.
    fn terminal_options(&self) -> Option<(out::When, bool)> {
        match self {
            // The server speaks a protocol, and the two writers below are
            // redirected into a file the first time and never read on screen.
            Command::Mcp | Command::Completions { .. } | Command::Manpage => None,
            Command::Project { .. } => Some((out::When::Auto, false)),
            _ => {
                let c = self.common();
                if c.json {
                    return None;
                }
                Some((c.color, !c.no_pager))
            }
        }
    }

    fn common(&self) -> &Common {
        match self {
            Command::Info(c)
            | Command::Sections(c)
            | Command::Symbols(c)
            | Command::Imports(c)
            | Command::Exports(c)
            | Command::Funcs(c)
            | Command::Stats(c) => c,
            Command::Annotate { common, .. }
            | Command::Batch { common, .. }
            | Command::Diff { common, .. } => common,
            // The server takes its paths per call rather than up front.
            Command::Mcp
            | Command::Project { .. }
            | Command::Completions { .. }
            | Command::Manpage => {
                unreachable!("handled before a file is opened")
            }
            Command::Vtables { common, .. }
            | Command::Classes { common, .. }
            | Command::Overlay { common, .. }
            | Command::Archive { common, .. }
            | Command::Repl { common }
            | Command::Patch { common, .. }
            | Command::Emulate { common, .. }
            | Command::Query { common, .. }
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
    // JSON is for a program, so it is never coloured and never paged whatever
    // the terminal is.
    if let Some(c) = cli.command.terminal_options() {
        w.attach_terminal(c.0, c.1);
    }
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

pub fn run(cli: &Cli, w: &mut out::Out) -> Result<u8, String> {
    // The server opens files itself, one per tool call, and the two writers
    // below have no input at all.
    match &cli.command {
        Command::Mcp => return mcp::serve(),
        // A project names its own files; none of them is the binary the other
        // commands open up front.
        Command::Project { what } => return project(w, what),
        Command::Completions { shell } => {
            let script = shell::completions(&Cli::command(), *shell);
            for line in script.lines() {
                out::outln!(w, "{line}");
            }
            return Ok(exit::OK);
        }
        Command::Manpage => {
            let page = shell::manpage(&Cli::command());
            for line in page.lines() {
                out::outln!(w, "{line}");
            }
            return Ok(exit::OK);
        }
        _ => {}
    }
    let common = cli.command.common();

    let file =
        std::fs::File::open(&common.file).map_err(|e| format!("{}: {e}", common.file.display()))?;
    // Memory-mapped: opening a 500 MB binary should not copy it.
    let data = map_file(&file).map_err(|e| format!("{}: {e}", common.file.display()))?;

    if let Command::Archive { common, symbols } = &cli.command {
        return print::archive(w, &data, *symbols, common.json);
    }

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
    let mut object = r12e_format::load(&data, &load_opts).map_err(|e| e.to_string())?;
    // A position independent library writes zero wherever a pointer goes and
    // leaves a relocation saying what belongs there, so every virtual table
    // and every type-information pointer in a shared object reads as zeroes
    // until these are applied. Reading them as they sit does not fail, it
    // quietly answers "there is nothing here".
    r12e_api::apply_relative_relocations(&mut object);
    // A PE keeps its debug information in a separate file, so the loader,
    // which only sees bytes, cannot reach it. This is the first layer that
    // can.
    annotate::load_pdb(&mut object, &common.file);
    let object = object;

    // Commands that only need the container skip analysis entirely, which is
    // what makes `info` on a 500 MB binary instant.
    match &cli.command {
        Command::Info(c) => return print::info(w, &object, c.json),
        Command::Sections(c) => return print::sections(w, &object, c.json),
        Command::Symbols(c) => return print::symbols(w, &object, c.json),
        Command::Imports(c) => return print::imports(w, &object, c.json),
        Command::Exports(c) => return print::exports(w, &object, c.json),
        Command::Overlay { common } => return print::overlay(w, &object, &data, common.json),
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

    let program = r12e_analysis::analyze(object, &opts);

    let mut program = program;
    if let Command::Repl { common } = &cli.command {
        return repl::run(w, cli, common, &mut program, &data);
    }
    dispatch(cli, w, &mut program, &data, &load_opts, &opts)
}

/// Run one command against a program that is already analyzed.
///
/// Split out so the interactive session can answer a hundred commands from one
/// analysis. Everything before this point reads and analyzes the file, which on
/// a large binary is seconds and would be paid per line otherwise.
pub fn dispatch(
    cli: &Cli,
    w: &mut out::Out,
    program: &mut r12e_analysis::Program,
    data: &[u8],
    load_opts: &LoadOptions,
    opts: &Options,
) -> Result<u8, String> {
    let common = cli.command.common();

    // Names from the log override what the container said, because the point
    // of writing one down was to overrule the engine.
    let db = common
        .db
        .clone()
        .unwrap_or_else(|| annotate::default_path(&common.file));
    let mut comments = std::collections::BTreeMap::new();
    let mut declared = std::collections::BTreeMap::new();
    if !matches!(cli.command, Command::Annotate { .. }) {
        for (at, name, _) in annotate::names(program, &db) {
            if let Some(f) = program.functions.get_mut(&at) {
                f.name = Some(name);
            }
        }
        comments = annotate::comments(program, &db);
        declared = annotate::declarations(program, &db);
    }

    // These need only the container, and a session reaches them through here
    // as well, so they are answered in the same place rather than twice.
    match &cli.command {
        Command::Info(c) => return print::info(w, &program.object, c.json),
        Command::Sections(c) => return print::sections(w, &program.object, c.json),
        Command::Symbols(c) => return print::symbols(w, &program.object, c.json),
        Command::Imports(c) => return print::imports(w, &program.object, c.json),
        Command::Exports(c) => return print::exports(w, &program.object, c.json),
        Command::Overlay { common } => {
            return print::overlay(w, &program.object, data, common.json);
        }
        _ => {}
    }

    match &cli.command {
        Command::Funcs(c) => print::funcs(w, program, c.json),
        Command::Stats(c) => print::stats(w, program, c.json),
        Command::Strings { common, .. } => print::strings(w, program, common.json),
        Command::Disas {
            common,
            target,
            bytes,
        } => print::disas(
            w,
            program,
            target,
            *bytes,
            common.json,
            print::Limits {
                budget: budget::Budget::new(common.budget, common.limit),
                progress: common.progress,
                declared: &declared,
                comments: &comments,
            },
        ),
        Command::Decompile { common, target } => print::decompile(
            w,
            program,
            target,
            common.json,
            print::Limits {
                budget: budget::Budget::new(common.budget, common.limit),
                progress: common.progress,
                declared: &declared,
                comments: &comments,
            },
        ),
        Command::Shapes { common, target } => print::shapes(w, program, target, common.json),
        Command::Emulate {
            common,
            target,
            args,
            depth,
            steps,
        } => print::emulate(w, program, target, args, *depth, *steps, common.json),
        Command::Vtables { common } => print::vtables(w, program, common.json),
        Command::Classes { common, members } => print::classes(w, program, *members, common.json),
        Command::Batch {
            common,
            script,
            command,
        } => batch::run(w, cli, common, script.as_deref(), command),
        Command::Query { common, query } => print::query(w, program, &query.join(" "), common.json),
        Command::Patch { what, common } => {
            let subject = patch::Subject {
                program,
                file: data,
                binary: &common.file,
            };
            match what {
                PatchCommand::Record {
                    target,
                    bytes,
                    asm,
                    pad_to,
                    note,
                    out,
                } => patch::record(
                    w,
                    &subject,
                    target,
                    patch::Replacement {
                        source: match (bytes, asm) {
                            (Some(b), _) => patch::Source::Bytes(patch::hex(b)?),
                            (_, Some(a)) => patch::Source::Asm(a),
                            _ => unreachable!("the argument group requires one"),
                        },
                        pad_to: *pad_to,
                    },
                    &whoami(),
                    note,
                    out,
                ),
                PatchCommand::Show { set } => patch::show(w, &patch::read(set)?),
                PatchCommand::Preview { set } => patch::preview(w, &subject, &patch::read(set)?),
                PatchCommand::Apply {
                    set,
                    out,
                    in_place,
                    allow_address_only,
                } => patch::apply(
                    w,
                    &subject,
                    &patch::read(set)?,
                    out.as_deref(),
                    *in_place,
                    *allow_address_only,
                ),
                PatchCommand::Revert {
                    set,
                    out,
                    in_place,
                    anchored_only,
                } => patch::apply(
                    w,
                    &subject,
                    &patch::read(set)?.revert(),
                    out.as_deref(),
                    *in_place,
                    !*anchored_only,
                ),
                PatchCommand::Invert { set, out } => patch::invert(w, &patch::read(set)?, out),
                PatchCommand::Merge { sets, out } => patch::merge(w, sets, out),
            }
        }
        Command::Sig { what, common } => match what {
            SigCommand::Create { out } => {
                let library = r12e_api::collect_signatures(
                    program,
                    &common
                        .file
                        .file_name()
                        .unwrap_or_default()
                        .to_string_lossy(),
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
                print::identified(w, program, &library, common.json)
            }
        },
        Command::Xrefs {
            common,
            target,
            from,
        } => print::xrefs(w, program, target, *from, common.json),
        Command::Diff { common, other, all } => {
            let other_data = std::fs::File::open(other)
                .and_then(|f| map_file(&f))
                .map_err(|e| format!("{}: {e}", other.display()))?;
            let other_obj = r12e_format::load(&other_data, load_opts).map_err(|e| e.to_string())?;
            let other_prog = r12e_analysis::analyze(other_obj, opts);
            print::diff(w, program, &other_prog, *all, common.json)
        }
        Command::Annotate { what, common } => {
            let who = whoami();
            match what {
                Annotation::Name { target, value } => annotate::set(
                    w,
                    program,
                    &db,
                    r12e_db::Field::Name,
                    target,
                    value.clone(),
                    &who,
                ),
                Annotation::Comment { target, value } => annotate::set(
                    w,
                    program,
                    &db,
                    r12e_db::Field::Comment,
                    target,
                    value.clone(),
                    &who,
                ),
                Annotation::Type { target, value } => annotate::set(
                    w,
                    program,
                    &db,
                    r12e_db::Field::Type,
                    target,
                    value.clone(),
                    &who,
                ),
                Annotation::List => annotate::list(w, program, &db, common.json),
                Annotation::Undo => annotate::step(w, &db, false),
                Annotation::Redo => annotate::step(w, &db, true),
            }
        }
        _ => unreachable!("handled above"),
    }
}

/// The project commands, which open the files they name and nothing else.
fn project(w: &mut out::Out, what: &ProjectCommand) -> Result<u8, String> {
    match what {
        ProjectCommand::New {
            binary,
            out,
            settings,
            log,
        } => {
            let file =
                std::fs::File::open(binary).map_err(|e| format!("{}: {e}", binary.display()))?;
            let data = map_file(&file).map_err(|e| format!("{}: {e}", binary.display()))?;
            let object = r12e_format::load(&data, &LoadOptions::default())
                .map_err(|e| format!("{}: {e}", binary.display()))?;
            patch::project_new(w, binary, &object, &data, settings, log.as_deref(), out)
        }
        ProjectCommand::Show { project } => patch::project_show(w, &patch::project_read(project)?),
        ProjectCommand::Verify { project, binary } => {
            let proj = patch::project_read(project)?;
            let path = binary
                .clone()
                .unwrap_or_else(|| PathBuf::from(&proj.binary.path));
            let file =
                std::fs::File::open(&path).map_err(|e| format!("{}: {e}", path.display()))?;
            let data = map_file(&file).map_err(|e| format!("{}: {e}", path.display()))?;
            patch::project_verify(w, &proj, &path, &data)
        }
        ProjectCommand::Add {
            project,
            signatures,
            patches,
            log,
        } => patch::project_add(w, project, signatures, patches, log.as_deref()),
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

#[cfg(test)]
mod tests {
    use super::*;

    /// Every subcommand's parser is well formed.
    ///
    /// `clap` builds the parser at run time, so a definition that contradicts
    /// itself is not a compile error: it is a panic the first time someone
    /// runs the subcommand that contains it. `emulate` had one for its whole
    /// life -- a global `--budget` counting seconds and a subcommand
    /// `--budget` counting IR operations, two types under one name -- and
    /// `r12e emulate` could not be run at all. Nothing noticed, because
    /// nothing ever built the parser outside of running the program.
    ///
    /// `debug_assert` is clap's own consistency check, and it is the same one
    /// that panics at parse time. Running it here turns "the first user to try
    /// this subcommand" into "the test run".
    #[test]
    fn the_command_tree_is_consistent() {
        Cli::command().debug_assert();
    }

    /// No subcommand names an option the global set already owns.
    ///
    /// The check above catches a redefinition with a different type, which is
    /// the panic that happened. It does not catch one with the *same* type:
    /// that parses, and quietly gives the subcommand's copy, so the same flag
    /// before and after the subcommand would mean two things with no error
    /// anywhere. A name is either global or it is not.
    #[test]
    fn no_subcommand_shadows_a_global_option() {
        let cli = Cli::command();
        // The global options live on `Common`, which is flattened into every
        // subcommand rather than declared on the root, so that is where they
        // are visible.
        let globals: std::collections::BTreeSet<String> = cli
            .get_subcommands()
            .flat_map(|s| s.get_arguments())
            .filter(|a| a.is_global_set())
            .map(|a| a.get_id().to_string())
            .collect();
        assert!(!globals.is_empty(), "no global options were found at all");

        let mut clashes = Vec::new();
        for sub in cli.get_subcommands() {
            for arg in sub.get_arguments() {
                let id = arg.get_id().to_string();
                if !arg.is_global_set() && globals.contains(&id) {
                    clashes.push(format!("{} --{id}", sub.get_name()));
                }
            }
        }
        assert!(
            clashes.is_empty(),
            "these subcommands redefine a global option: {}",
            clashes.join(", ")
        );
    }
}
