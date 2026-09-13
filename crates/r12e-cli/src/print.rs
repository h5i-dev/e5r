//! Output. Text for a person, JSON for everything else.
//!
//! Both come from the same values, so `--json` never shows more or less than
//! the listing does.

use r12e_analysis::{Program, XrefKind};
use r12e_core::{Addr, Strength};
use r12e_format::Object;

use crate::addr;
use crate::exit;
use crate::json;
use crate::out::{Out, outln};

type R = Result<u8, String>;

/// Container summary.
pub fn info(w: &mut Out, o: &Object, as_json: bool) -> R {
    if as_json {
        return json::emit(w, &json::info(o));
    }
    outln!(
        w,
        "file      {} {}, {}-bit, {:?}",
        o.format,
        o.arch,
        o.bits,
        o.endian
    );
    if let Some(e) = o.entry {
        outln!(w, "entry     {e}");
    }
    outln!(w, "base      {}", o.image_base);
    outln!(w, "pic       {}", o.pic);
    outln!(
        w,
        "mapped    {} segments, {}",
        o.memory.segments().len(),
        o.memory
            .bounds()
            .map(|b| b.to_string())
            .unwrap_or_else(|| "nothing".into())
    );
    outln!(
        w,
        "symbols   {} ({} dynamic)",
        o.symbols.len(),
        o.symbols.iter().filter(|s| s.dynamic).count()
    );
    outln!(w, "imports   {}", o.imports.len());
    outln!(w, "exports   {}", o.exports.len());
    outln!(w, "hints     {} function entries", o.function_hints.len());
    for (k, v) in &o.metadata {
        outln!(w, "{k:<10}{v}");
    }
    for warning in &o.warnings {
        outln!(w, "warning   {warning}");
    }
    Ok(exit::OK)
}

/// Sections and their mapping.
pub fn sections(w: &mut Out, o: &Object, as_json: bool) -> R {
    if as_json {
        return json::emit(w, &json::sections(o));
    }
    if o.sections.is_empty() {
        eprintln!("no sections");
        return Ok(exit::NOT_FOUND);
    }
    outln!(
        w,
        "{:<24}{:<20}{:>10}  {:>10}  perm",
        "name",
        "address",
        "size",
        "file off"
    );
    for s in &o.sections {
        let addr = if s.range.is_empty() {
            "unmapped".to_string()
        } else {
            s.range.start().to_string()
        };
        outln!(
            w,
            "{:<24}{:<20}{:>10x}  {:>10x}  {}{}{}",
            s.name,
            addr,
            s.range.len(),
            s.file_offset,
            'r',
            if s.write { 'w' } else { '-' },
            if s.exec { 'x' } else { '-' },
        );
    }
    Ok(exit::OK)
}

/// Symbols.
pub fn symbols(w: &mut Out, o: &Object, as_json: bool) -> R {
    if as_json {
        return json::emit(w, &json::symbols(o));
    }
    if o.symbols.is_empty() {
        eprintln!("no symbols");
        return Ok(exit::NOT_FOUND);
    }
    for s in &o.symbols {
        outln!(
            w,
            "{:<20}{:>8x}  {:<10}{:<8}{}",
            s.addr.to_string(),
            s.size,
            format!("{:?}", s.kind).to_lowercase(),
            if s.dynamic { "dynamic" } else { "static" },
            r12e_types::pretty(&s.name)
        );
    }
    Ok(exit::OK)
}

/// Imports.
pub fn imports(w: &mut Out, o: &Object, as_json: bool) -> R {
    if as_json {
        return json::emit(w, &json::imports(o));
    }
    if o.imports.is_empty() {
        eprintln!("no imports");
        return Ok(exit::NOT_FOUND);
    }
    for i in &o.imports {
        let name = r12e_types::pretty(&i.name);
        let lib = i
            .library
            .as_deref()
            .map(|l| format!("{l}  "))
            .unwrap_or_default();
        match i.thunk {
            Some(t) => outln!(w, "{t}  {lib}{name}"),
            None => outln!(w, "{:<20}{lib}{name}", ""),
        }
    }
    Ok(exit::OK)
}

/// Exports.
pub fn exports(w: &mut Out, o: &Object, as_json: bool) -> R {
    if as_json {
        return json::emit(w, &json::exports(o));
    }
    if o.exports.is_empty() {
        eprintln!("no exports");
        return Ok(exit::NOT_FOUND);
    }
    for e in &o.exports {
        outln!(w, "{}  {}", e.addr, r12e_types::pretty(&e.name));
    }
    Ok(exit::OK)
}

/// Recovered functions, with the evidence for each.
pub fn funcs(w: &mut Out, p: &Program, as_json: bool) -> R {
    if as_json {
        return json::emit(w, &json::funcs(p));
    }
    if p.functions.is_empty() {
        eprintln!("no functions recovered");
        return Ok(exit::NOT_FOUND);
    }
    outln!(
        w,
        "{:<20}{:>8}  {:>6}  {:>6}  {:<10}{:<28}{}",
        "address",
        "size",
        "blocks",
        "insns",
        "strength",
        "evidence",
        "name"
    );
    for f in p.functions_by_address() {
        let ev = {
            let mut s = f.provenance.best.to_string();
            for c in &f.provenance.corroborating {
                s.push_str(", ");
                s.push_str(c.as_str());
            }
            s
        };
        outln!(
            w,
            "{:<20}{:>8x}  {:>6}  {:>6}  {:<10}{:<28}{}{}",
            f.entry.to_string(),
            f.cfg.covered_bytes(),
            f.cfg.blocks.len(),
            f.cfg.insns(),
            f.provenance.strength().to_string(),
            truncate(&ev, 27),
            f.display_name(),
            if f.is_complete() {
                ""
            } else {
                "  [incomplete]"
            },
        );
    }
    Ok(exit::OK)
}

fn truncate(s: &str, n: usize) -> String {
    if s.len() <= n {
        s.to_string()
    } else {
        format!("{}…", &s[..n - 1])
    }
}

/// Counts.
pub fn stats(w: &mut Out, p: &Program, as_json: bool) -> R {
    if as_json {
        return json::emit(w, &json::stats(p));
    }
    let s = p.stats();
    outln!(w, "functions   {}", s.functions);
    outln!(
        w,
        "  complete  {} ({:.1}%)",
        s.complete,
        pct(s.complete, s.functions)
    );
    outln!(w, "  capped    {}", s.capped);
    outln!(w, "blocks      {}", s.blocks);
    outln!(
        w,
        "jump tables {} resolved, {} targets; {} functions still indirect",
        s.tables,
        s.table_targets,
        s.indirect
    );
    outln!(w, "insns       {}", s.insns);
    outln!(w, "xrefs       {}", s.xrefs);
    outln!(w, "strings     {}", s.strings);
    outln!(w, "rounds      {}", p.rounds);
    outln!(w, "evidence");
    for (k, n) in p.by_strength().iter().rev() {
        outln!(w, "  {:<9} {n}", k.to_string());
    }
    Ok(exit::OK)
}

fn pct(a: usize, b: usize) -> f64 {
    if b == 0 {
        0.0
    } else {
        a as f64 * 100.0 / b as f64
    }
}

/// Strings.
pub fn strings(w: &mut Out, p: &Program, as_json: bool) -> R {
    if as_json {
        return json::emit(w, &p.strings);
    }
    if p.strings.is_empty() {
        eprintln!("no strings");
        return Ok(exit::NOT_FOUND);
    }
    for s in &p.strings {
        outln!(w, "{}  {:?}", s.addr, s.text);
    }
    Ok(exit::OK)
}

/// Disassembly.
pub fn disas(w: &mut Out, p: &Program, target: &str, show_bytes: bool, as_json: bool) -> R {
    let chosen: Vec<&r12e_analysis::Function> = if target == "all" {
        p.functions_by_address().collect()
    } else {
        let Some(a) = addr::resolve(p, target) else {
            return Err(format!("{target:?} is not an address, a symbol, or `all`"));
        };
        match p.function(a).or_else(|| p.function_at(a)) {
            Some(f) => vec![f],
            None => {
                eprintln!("no function covers {a}");
                return Ok(exit::NOT_FOUND);
            }
        }
    };
    if chosen.is_empty() {
        eprintln!("no functions recovered");
        return Ok(exit::NOT_FOUND);
    }

    if as_json {
        return json::emit(w, &json::disas(p, &chosen));
    }

    for (n, f) in chosen.iter().enumerate() {
        if n > 0 {
            outln!(w);
        }
        outln!(
            w,
            "{} <{}>:  {} block(s), {}",
            f.entry,
            f.display_name(),
            f.cfg.blocks.len(),
            f.provenance
        );
        let insns = p.instructions(f);
        let mut prev_end: Option<Addr> = None;
        for i in &insns {
            // A gap means the function is split; say so rather than implying
            // the bytes between are its code.
            if prev_end.is_some_and(|e| e != i.addr) {
                outln!(w, "  ...");
            }
            prev_end = Some(i.next());
            let text = r12e_arch::format(&p.object.arch, i, false);
            let raw = if show_bytes {
                p.object
                    .memory
                    .slice(i.addr, i.len as u64)
                    .map(|b| b.iter().map(|x| format!("{x:02x}")).collect::<String>())
                    .unwrap_or_default()
            } else {
                String::new()
            };
            let annot = annotate(p, i);
            outln!(
                w,
                "  {:>12x}: {:<10}{}{}",
                i.addr.get(),
                raw,
                text.replace('\t', " "),
                annot
            );
        }
    }
    Ok(exit::OK)
}

/// The `<name>` a listing puts after a branch or a data reference.
fn annotate(p: &Program, i: &r12e_arch::Insn) -> String {
    let mut out = String::new();
    if let Some(t) = i.flow.target() {
        if let Some(n) = p.name_of(t) {
            out = format!("  <{n}>");
        }
    }
    for x in p.xrefs.from(i.addr) {
        if x.kind == XrefKind::Data || x.kind == XrefKind::Read || x.kind == XrefKind::Write {
            if let Some(s) = p.strings.iter().find(|s| s.addr == x.to) {
                out = format!("  ; {:?}", s.text);
            } else if let Some(t) = p.text_at(x.to, 64) {
                out = format!("  ; {t:?}");
            } else if let Some(n) = p.name_of(x.to) {
                out = format!("  ; {n}");
            }
        }
    }
    out
}

/// References.
pub fn xrefs(w: &mut Out, p: &Program, target: &str, from: bool, as_json: bool) -> R {
    let Some(a) = addr::resolve(p, target) else {
        return Err(format!("{target:?} is not an address or a symbol"));
    };
    let refs = if from { p.xrefs.from(a) } else { p.xrefs.to(a) };
    if as_json {
        return json::emit(w, &json::xrefs(p, refs));
    }
    if refs.is_empty() {
        eprintln!("no references {} {a}", if from { "from" } else { "to" });
        return Ok(exit::NOT_FOUND);
    }
    for x in refs {
        let other = if from { x.to } else { x.from };
        let name = p
            .function_at(other)
            .map(|f| format!(" in {}", f.display_name()))
            .unwrap_or_default();
        outln!(
            w,
            "{:<10}{}{}",
            format!("{:?}", x.kind).to_lowercase(),
            other,
            name
        );
    }
    Ok(exit::OK)
}

/// The strength word, for JSON.
pub fn strength_name(s: Strength) -> &'static str {
    s.as_str()
}
