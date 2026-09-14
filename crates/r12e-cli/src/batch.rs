//! Running several commands over one file and printing one document.
//!
//! An agent or a script that wants ten answers should not pay for ten
//! analyses, and should not have to match ten outputs back to what it asked.
//! Each command is run against the program already in memory and its answer is
//! returned next to the command that produced it.
//!
//! A command that fails does not stop the rest: its entry carries the error
//! instead of an answer, which is what a caller wants from a batch.

use std::path::Path;

use clap::Parser;

use crate::out::{Out, outln};
use crate::{Cli, Command, Common, exit};

/// Run a script of commands and print one JSON document.
pub fn run(
    w: &mut Out,
    cli: &Cli,
    common: &Common,
    script: Option<&Path>,
    commands: &[String],
) -> Result<u8, String> {
    let mut lines: Vec<String> = commands.to_vec();
    if let Some(path) = script {
        let text = if path == Path::new("-") {
            std::io::read_to_string(std::io::stdin()).map_err(|e| e.to_string())?
        } else {
            std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?
        };
        lines.extend(
            text.lines()
                .map(|l| l.split('#').next().unwrap_or("").trim().to_string())
                .filter(|l| !l.is_empty()),
        );
    }
    if lines.is_empty() {
        return Err("a batch needs commands: pass --command or --script".into());
    }

    let file = common.file.display().to_string();
    outln!(w, "{{");
    outln!(w, "  \"schema\": \"r12e/1\",");
    outln!(w, "  \"file\": {},", quote(&file));
    outln!(w, "  \"results\": [");

    let mut worst = exit::OK;
    for (n, line) in lines.iter().enumerate() {
        let separator = if n + 1 == lines.len() { "" } else { "," };
        let (status, body) = one(cli, common, line);
        if status != exit::OK {
            worst = worst.max(status);
        }
        outln!(w, "    {{");
        outln!(w, "      \"command\": {},", quote(line));
        outln!(w, "      \"status\": {status},");
        outln!(w, "      \"output\": {body}");
        outln!(w, "    }}{separator}");
    }
    outln!(w, "  ]");
    outln!(w, "}}");
    Ok(worst)
}

/// Run one command and return its status and its answer as JSON.
fn one(cli: &Cli, common: &Common, line: &str) -> (u8, String) {
    let Some(words) = split(line) else {
        return (exit::USAGE, quote("a quote was never closed"));
    };
    // The file comes from the batch, not from the line, so a script cannot be
    // written once and silently read a different binary. It goes straight
    // after the subcommand, where the command line puts it: a command whose
    // last argument takes everything left would otherwise swallow it.
    let mut words = words.into_iter();
    let Some(subcommand) = words.next() else {
        return (exit::USAGE, quote("an empty command"));
    };
    let mut argv: Vec<String> = vec![
        "r12e".to_string(),
        subcommand,
        common.file.display().to_string(),
    ];
    argv.extend(words);
    argv.push("--json".to_string());

    let parsed = match Cli::try_parse_from(&argv) {
        Ok(parsed) => parsed,
        Err(e) => return (exit::USAGE, quote(&first_line(&e.to_string()))),
    };
    // A batch of batches would analyze the file again for each one, which is
    // the cost this exists to avoid.
    if matches!(parsed.command, Command::Batch { .. } | Command::Mcp) {
        return (exit::USAGE, quote("a batch cannot run a batch or a server"));
    }
    let _ = cli;

    let mut buffer = Out::buffer();
    let status = match crate::run(&parsed, &mut buffer) {
        Ok(status) => status,
        Err(e) => return (exit::BAD_INPUT, quote(&e)),
    };
    let text = buffer.take();
    let text = text.trim();
    if text.is_empty() {
        return (status, "null".to_string());
    }
    (status, text.to_string())
}

/// The words of a command line, respecting quotes.
pub fn split(line: &str) -> Option<Vec<String>> {
    let mut out = Vec::new();
    let mut current = String::new();
    let mut quote: Option<char> = None;
    let mut any = false;
    for c in line.chars() {
        match (quote, c) {
            (Some(q), c) if c == q => quote = None,
            (Some(_), c) => current.push(c),
            (None, '"') | (None, '\'') => {
                quote = Some(c);
                any = true;
            }
            (None, c) if c.is_whitespace() => {
                if !current.is_empty() || any {
                    out.push(std::mem::take(&mut current));
                    any = false;
                }
            }
            (None, c) => current.push(c),
        }
    }
    if quote.is_some() {
        return None;
    }
    if !current.is_empty() || any {
        out.push(current);
    }
    Some(out)
}

fn first_line(text: &str) -> String {
    text.lines()
        .find(|l| !l.trim().is_empty())
        .unwrap_or("")
        .trim_start_matches("error: ")
        .to_string()
}

/// A JSON string, escaped.
fn quote(text: &str) -> String {
    let mut out = String::with_capacity(text.len() + 2);
    out.push('"');
    for c in text.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn quotes_keep_words_together() {
        let words = split("query 'functions where insns > 10'").expect("splits");
        assert_eq!(words, vec!["query", "functions where insns > 10"]);
    }

    #[test]
    fn an_unclosed_quote_is_an_error() {
        assert!(split("query 'oops").is_none());
    }

    #[test]
    fn an_empty_argument_survives_splitting() {
        let words = split("annotate name main ''").expect("splits");
        assert_eq!(words.len(), 4);
        assert_eq!(words[3], "");
    }

    #[test]
    fn a_string_is_escaped_for_json() {
        assert_eq!(quote("a\"b\\c\nd"), "\"a\\\"b\\\\c\\nd\"");
    }
}
