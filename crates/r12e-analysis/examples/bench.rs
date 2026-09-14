//! What one command's worth of analysis costs, eagerly and lazily.
//!
//! Not a test. It exists so the M11 numbers are measured with the library the
//! CLI calls rather than inferred from a CLI that has its own per-command
//! workarounds in it. Peak resident set comes from the kernel, and agrees with
//! `/usr/bin/time`.
//!
//! Usage: bench <binary> <mode> [cache-dir]
//!
//!   load          parse the header and the symbol table, nothing else
//!   funcs-eager   what `r12e funcs` costs today: analyze() with strings off
//!   funcs-lazy    a session asked for functions and nothing else
//!   strings-lazy  a session asked for strings and nothing else
//!   all           everything, which is what `r12e stats` needs
//!
//! A cache directory makes the lazy modes read and write it, so running one
//! twice prints a miss and then a hit.

use std::time::Instant;

use r12e_analysis::{Cache, ContentHash, Options, Session};
use r12e_format::LoadOptions;

/// Peak resident set in kilobytes, as the kernel saw it.
fn peak_rss() -> u64 {
    std::fs::read_to_string("/proc/self/status")
        .unwrap_or_default()
        .lines()
        .find(|l| l.starts_with("VmHWM:"))
        .and_then(|l| l.split_whitespace().nth(1))
        .and_then(|v| v.parse().ok())
        .unwrap_or(0)
}

fn main() {
    let mut args = std::env::args().skip(1);
    let path = args
        .next()
        .expect("usage: bench <binary> <mode> [cache-dir]");
    let mode = args.next().unwrap_or_else(|| "all".to_string());
    let cache_dir = args.next();

    let start = Instant::now();
    let data = std::fs::read(&path).expect("read");
    let object = r12e_format::load(&data, &LoadOptions::default()).expect("load");
    let loaded = start.elapsed();

    let opts = Options {
        strings: mode != "funcs-eager",
        ..Options::default()
    };

    let work = Instant::now();
    let note = if mode == "funcs-eager" {
        let p = r12e_analysis::analyze(object, &opts);
        format!("{} functions, {} xrefs", p.functions.len(), p.xrefs.len())
    } else {
        let mut session = Session::new(object, opts);
        if let Some(dir) = &cache_dir {
            session = session.with_cache(Cache::at(dir), ContentHash::of(&data));
        }
        match mode.as_str() {
            "load" => "nothing asked for".to_string(),
            "funcs-lazy" => {
                let f = session.functions();
                let blocks: usize = f.values().map(|f| f.cfg.blocks.len()).sum();
                let insns: u64 = f.values().map(|f| f.cfg.insns() as u64).sum();
                format!("{} functions, {blocks} blocks, {insns} insns", f.len())
            }
            "strings-lazy" => format!("{} strings", session.strings().len()),
            "all" => {
                let s = session.into_program().stats();
                format!(
                    "{} functions, {} blocks, {} insns, {} xrefs, {} strings",
                    s.functions, s.blocks, s.insns, s.xrefs, s.strings
                )
            }
            other => panic!("unknown mode {other}"),
        }
    };
    let elapsed = work.elapsed();

    println!(
        "{mode:<13} load {:>6.3}s  work {:>6.3}s  total {:>6.3}s  peak {:>7} KB  {note}",
        loaded.as_secs_f64(),
        elapsed.as_secs_f64(),
        start.elapsed().as_secs_f64(),
        peak_rss(),
    );
}
