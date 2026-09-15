//! The interactive session.
//!
//! One analysis, many questions. The point is not to save typing: it is that
//! analyzing a large binary takes seconds, and a session that paid that per
//! command would be unusable on exactly the binaries where a session is worth
//! having.
//!
//! Commands are the ones the command line already has, spelled the same way,
//! so nothing has to be learned twice and anything read in the manual works
//! here. The binary is fixed for the session, so a command does not name it.

use std::io::{BufRead, IsTerminal, Write};

use r12e_analysis::Program;
use r12e_core::Addr;

use crate::out::{Out, outln};
use crate::{Cli, Command, Common, exit};

/// What a short name stands for. Only for the commands typed a hundred times
/// an hour; everything else is spelled out, because a grammar of two-letter
/// pairs is what this is meant to be an alternative to.
const ALIASES: &[(&str, &str)] = &[
    ("d", "disas"),
    ("dec", "decompile"),
    ("f", "funcs"),
    ("i", "info"),
    ("s", "strings"),
    ("x", "xrefs"),
    ("q", "query"),
    ("?", "help"),
];

/// Run the session.
pub fn run(
    w: &mut Out,
    cli: &Cli,
    common: &Common,
    program: &mut Program,
    data: &[u8],
) -> Result<u8, String> {
    let interactive = std::io::stdin().is_terminal();
    if interactive {
        outln!(
            w,
            "{} function(s) in {}. `help` lists the commands, `quit` leaves.",
            program.functions.len(),
            common.file.display()
        );
    }
    // The prompt carries the current address, because the commands that take
    // one are the commands that get typed repeatedly.
    let mut here: Option<Addr> = program.functions_by_address().next().map(|f| f.entry);
    let stdin = std::io::stdin();
    let mut line = String::new();
    loop {
        if interactive {
            let at = here.map(|a| a.to_string()).unwrap_or_else(|| "?".into());
            let mut e = std::io::stderr();
            let _ = write!(e, "{at}> ");
            let _ = e.flush();
        }
        line.clear();
        if stdin
            .lock()
            .read_line(&mut line)
            .map_err(|e| e.to_string())?
            == 0
        {
            break; // end of input, which is how a piped session ends
        }
        let text = line.split('#').next().unwrap_or("").trim();
        if text.is_empty() {
            continue;
        }
        match step(w, cli, common, program, data, text, &mut here) {
            Step::Continue => {}
            Step::Leave => break,
        }
    }
    if interactive {
        outln!(w, "");
    }
    Ok(exit::OK)
}

/// Whether the session goes on.
enum Step {
    Continue,
    Leave,
}

fn step(
    w: &mut Out,
    cli: &Cli,
    common: &Common,
    program: &mut Program,
    data: &[u8],
    text: &str,
    here: &mut Option<Addr>,
) -> Step {
    let Some(words) = crate::batch::split(text) else {
        eprintln!("r12e: a quote was never closed");
        return Step::Continue;
    };
    let Some(first) = words.first().map(String::as_str) else {
        return Step::Continue;
    };
    match first {
        "quit" | "exit" | "q!" => return Step::Leave,
        "help" | "?" => {
            help(w);
            return Step::Continue;
        }
        // Moving is its own command because every listing command defaults to
        // where you are, and typing the address into each one is the thing a
        // session exists to avoid.
        "seek" | "s@" => {
            match words.get(1).and_then(|t| crate::addr::resolve(program, t)) {
                Some(a) => *here = Some(a),
                None => eprintln!("r12e: no such address"),
            }
            return Step::Continue;
        }
        _ => {}
    }

    let name = ALIASES
        .iter()
        .find(|(short, _)| *short == first)
        .map(|(_, long)| *long)
        .unwrap_or(first);

    // The file comes from the session, not the line, so a command cannot be
    // pointed at a different binary than the one that was analyzed.
    let mut argv: Vec<String> = vec![
        "r12e".into(),
        name.into(),
        common.file.display().to_string(),
    ];
    let mut rest: Vec<String> = words[1..].to_vec();
    // A command that takes a target and was given none gets the current
    // address, which is what makes seeking worth anything.
    if rest.is_empty()
        && matches!(name, "disas" | "decompile" | "shapes" | "xrefs")
        && let Some(a) = here
    {
        rest.push(a.to_string());
    }
    argv.extend(rest);

    let parsed = match <Cli as clap::Parser>::try_parse_from(&argv) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("r12e: {e}");
            return Step::Continue;
        }
    };
    match &parsed.command {
        // Both of these would analyze the file again, which is the cost this
        // exists to avoid, and nesting a session inside one answers nothing.
        Command::Repl { .. } | Command::Batch { .. } => {
            eprintln!("r12e: not from a session");
            return Step::Continue;
        }
        _ => {}
    }

    // The same analysis, borrowed, for every command: this is the whole point.
    // Dispatch is exactly the command line's own path, so a session and a
    // one-shot invocation cannot disagree about what a command does.
    let opts = r12e_analysis::Options::default();
    let load = r12e_format::LoadOptions::default();
    if let Err(e) = crate::dispatch(&parsed, w, program, data, &load, &opts) {
        eprintln!("r12e: {e}");
    }
    let _ = cli;
    Step::Continue
}

fn help(w: &mut Out) {
    outln!(w, "Commands are the ones r12e takes, without the file:");
    outln!(w, "");
    outln!(
        w,
        "  info  sections  symbols  imports  exports  funcs  stats"
    );
    outln!(w, "  disas [where]      decompile [where]   shapes [where]");
    outln!(
        w,
        "  xrefs [where]      strings             query <question>"
    );
    outln!(w, "  classes  vtables  sig  annotate  overlay  archive");
    outln!(w, "");
    outln!(
        w,
        "  seek <where>       move, so the commands above need no address"
    );
    outln!(w, "  quit               leave");
    outln!(w, "");
    outln!(w, "Short forms: d disas, dec decompile, f funcs, i info,");
    outln!(w, "             s strings, x xrefs, q query, ? help.");
    outln!(w, "");
    outln!(
        w,
        "`where` is an address, a symbol, `main+0x20`, or `all`. Anything the"
    );
    outln!(w, "manual says works here, and --json works too.");
}
