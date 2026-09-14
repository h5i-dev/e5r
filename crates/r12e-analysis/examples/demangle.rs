//! A filter that demangles the symbol names in whatever is piped through it.
//!
//! `perf` on this machine does not know Rust's v0 scheme, so a profile of r12e
//! reads as `_RNvNtCs..._13r12e_analysis3cfg10build_with`. This crate already
//! depends on the demangler the rest of the tool uses, so the profile can be
//! made readable without installing anything.
//!
//! It belongs in the CLI as `r12e demangle` rather than here. It is an example
//! because the analysis crate is the one `scripts/flamegraph.sh` profiles, and
//! an example needs no new command, no new flag and no other crate's consent.
//!
//! Usage: ... | cargo run --release -p r12e-analysis --example demangle

use std::io::{BufRead, Write};

/// Whether a byte can appear in a mangled symbol.
fn symbolic(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_' || b == b'$' || b == b'.'
}

/// Replace every mangled name in one line with what it means.
fn rewrite(line: &str, out: &mut String) {
    let b = line.as_bytes();
    let mut i = 0;
    while i < b.len() {
        if (b[i] == b'_' || b[i] == b'?') && (i == 0 || !symbolic(b[i - 1])) {
            let mut j = i;
            while j < b.len() && symbolic(b[j]) {
                j += 1;
            }
            // A trailing `.llvm.1234` is LLVM's, not part of the name, and the
            // demangler rejects the whole symbol if it is left on.
            let token = &line[i..j];
            let stem = token.split(".llvm.").next().unwrap_or(token);
            if let Some((_, name)) = r12e_types::demangle(stem) {
                out.push_str(&name);
                i = j;
                continue;
            }
        }
        // One character rather than one byte: `i` is always on a boundary,
        // because everything a mangled name is made of is ASCII.
        let ch = line[i..].chars().next().unwrap_or('\u{fffd}');
        out.push(ch);
        i += ch.len_utf8();
    }
}

fn main() {
    let stdin = std::io::stdin();
    let stdout = std::io::stdout();
    let mut w = std::io::BufWriter::new(stdout.lock());
    let mut buf = String::new();
    for line in stdin.lock().lines().map_while(Result::ok) {
        buf.clear();
        rewrite(&line, &mut buf);
        if writeln!(w, "{buf}").is_err() {
            return;
        }
    }
}
