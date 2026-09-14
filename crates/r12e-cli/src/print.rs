//! Output. Text for a person, JSON for everything else.
//!
//! Both come from the same values, so `--json` never shows more or less than
//! the listing does.

use r12e_analysis::{Program, XrefKind};
use r12e_core::{Addr, Strength};
use r12e_format::Object;

use crate::addr;
use crate::budget::{Budget, Stopped};
use crate::exit;
use crate::json;
use crate::out::{Out, Role, outln};
use crate::progress::Progress;

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
        // A key longer than the column still needs a space after it, or the
        // value runs into the name.
        outln!(w, "{k:<9} {}", v.replace('\n', " "));
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
        "{}",
        head(
            w,
            &format!(
                "{:<24}{:<20}{:>10}  {:>10}  perm",
                "name", "address", "size", "file off"
            )
        )
    );
    for s in &o.sections {
        let addr = if s.range.is_empty() {
            "unmapped".to_string()
        } else {
            s.range.start().to_string()
        };
        outln!(
            w,
            "{:<24}{}{:>10x}  {:>10x}  {}{}{}",
            s.name,
            cell(w, Role::Addr, &addr, 20),
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
            "{}{:>8x}  {:<10}{:<8}{}",
            cell(w, Role::Addr, &s.addr.to_string(), 20),
            s.size,
            format!("{:?}", s.kind).to_lowercase(),
            if s.dynamic { "dynamic" } else { "static" },
            w.paint(Role::Name, &last(w, 48, &r12e_types::pretty(&s.name)))
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
        "{}",
        head(
            w,
            &format!(
                "{:<20}{:>8}  {:>6}  {:>6}  {:<10}{:<28}{}",
                "address", "size", "blocks", "insns", "strength", "evidence", "name"
            )
        )
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
        let strength = f.provenance.strength().to_string();
        let tail = if f.is_complete() {
            ""
        } else {
            "  [incomplete]"
        };
        outln!(
            w,
            "{}{:>8x}  {:>6}  {:>6}  {}{:<28}{}{}",
            cell(w, Role::Addr, &f.entry.to_string(), 20),
            f.cfg.covered_bytes(),
            f.cfg.blocks.len(),
            f.cfg.insns(),
            cell(w, strength_role(&strength), &strength, 10),
            truncate(&ev, 27),
            w.paint(Role::Name, &last(w, 84 + tail.len(), &f.display_name())),
            tail,
        );
    }
    Ok(exit::OK)
}

fn truncate(s: &str, n: usize) -> String {
    if s.len() <= n {
        s.to_string()
    } else {
        // On a character boundary, because a name can be UTF-8 and cutting a
        // multi-byte sequence in half would panic.
        let mut cut = n - 1;
        while cut > 0 && !s.is_char_boundary(cut) {
            cut -= 1;
        }
        format!("{}…", &s[..cut])
    }
}

/// A fixed-width cell, padded before it is coloured so the escape sequences do
/// not count toward the width.
fn cell(w: &Out, role: Role, text: &str, width: usize) -> String {
    w.paint(role, &format!("{text:<width$}"))
}

/// A header row, which is one colour across.
fn head(w: &Out, text: &str) -> String {
    w.paint(Role::Head, text)
}

/// Fit the last column of a listing to the terminal, and never when the output
/// is going somewhere else: a piped listing must diff against the same listing
/// taken a week ago.
fn last(w: &Out, used: usize, text: &str) -> String {
    match w.width() {
        Some(total) if total > used + 8 => truncate(text, total - used),
        Some(_) => truncate(text, 8),
        None => text.to_string(),
    }
}

/// The colour a strength is printed in. The ladder is the point: a reader
/// scanning a listing should see at a glance which rows are facts.
fn strength_role(s: &str) -> Role {
    match s {
        "proven" | "asserted" => Role::Strong,
        "inferred" => Role::Weak,
        _ => Role::Unknown,
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
    outln!(w, "  noreturn  {}", s.noreturn);
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
        outln!(
            w,
            "{}  {}",
            w.paint(Role::Addr, &s.addr.to_string()),
            last(w, 22, &format!("{:?}", s.text))
        );
    }
    Ok(exit::OK)
}

/// Disassembly.
pub fn disas(
    w: &mut Out,
    p: &Program,
    target: &str,
    show_bytes: bool,
    as_json: bool,
    mut budget: Budget,
    progress: bool,
    comments: &std::collections::BTreeMap<Addr, String>,
) -> R {
    let mut chosen: Vec<&r12e_analysis::Function> = if target == "all" {
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

    let wanted = chosen.len();
    if !budget.unlimited() {
        let mut allowed = Vec::with_capacity(chosen.len());
        let mut why = Stopped::Finished;
        for f in chosen {
            why = budget.take();
            if !why.complete() {
                break;
            }
            allowed.push(f);
        }
        crate::budget::report(&budget, why, allowed.len(), wanted, "function(s)");
        chosen = allowed;
    }

    if as_json {
        return json::emit(w, &json::disas(p, &chosen));
    }

    let mut bar = Progress::new("disassembled", chosen.len(), progress && !as_json);
    for (n, f) in chosen.iter().enumerate() {
        bar.step();
        if n > 0 {
            outln!(w);
        }
        outln!(
            w,
            "{} <{}>:  {} block(s), {}",
            w.paint(Role::Addr, &f.entry.to_string()),
            w.paint(Role::Name, &f.display_name()),
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
            // An asserted comment comes last, after the tool's own note, so
            // the two are never confused: everything before it was worked out
            // and everything after it was written down by a person.
            let said = match comments.get(&i.addr) {
                Some(c) => w.paint(Role::Weak, &format!("  ; {c}")),
                None => String::new(),
            };
            outln!(
                w,
                "  {}: {:<10}{}{}{said}",
                w.paint(Role::Addr, &format!("{:>12x}", i.addr.get())),
                raw,
                text.replace('\t', " "),
                w.paint(Role::Name, &annot)
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

/// A comparison of two builds.
pub fn diff(w: &mut Out, old: &Program, new: &Program, all: bool, as_json: bool) -> R {
    let d = r12e_diff::compare(old, new);
    if as_json {
        return json::emit(w, &json::diff(&d));
    }
    outln!(
        w,
        "{} matched ({} changed, {} identical), {} removed, {} added",
        d.matched.len(),
        d.changed_count(),
        d.identical_count(),
        d.removed.len(),
        d.added.len()
    );
    if d.matched.is_empty() && d.added.is_empty() && d.removed.is_empty() {
        eprintln!("nothing to compare");
        return Ok(exit::NOT_FOUND);
    }
    outln!(w);
    outln!(
        w,
        "{:<12}{:<20}{:<20}{:>7}  {:>7}  {}",
        "similarity",
        "old",
        "new",
        "old n",
        "new n",
        "name"
    );
    for m in d.matched.iter().filter(|m| all || m.changed()) {
        outln!(
            w,
            "{:<12.3}{:<20}{:<20}{:>7}  {:>7}  {}  [{}]",
            m.similarity,
            m.old.to_string(),
            m.new.to_string(),
            m.old_insns,
            m.new_insns,
            m.name,
            m.kind.as_str()
        );
    }
    for (a, n) in &d.removed {
        outln!(
            w,
            "{:<12}{:<20}{:<20}{:>7}  {:>7}  {n}",
            "removed",
            a.to_string(),
            "",
            "",
            ""
        );
    }
    for (a, n) in &d.added {
        outln!(
            w,
            "{:<12}{:<20}{:<20}{:>7}  {:>7}  {n}",
            "added",
            "",
            a.to_string(),
            "",
            ""
        );
    }
    Ok(exit::OK)
}

/// Decompile one function, or every recovered function, to pseudo-C.
pub fn decompile(
    w: &mut Out,
    p: &Program,
    target: &str,
    as_json: bool,
    mut budget: Budget,
    progress: bool,
) -> R {
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

    // Decompiled in chunks so a budget can stop between them. One function at
    // a time would lose the cross-function pass that settles call arity, and
    // the whole list at once cannot be interrupted; a chunk is the compromise,
    // and it is small enough that the budget overshoots by at most one chunk.
    const CHUNK: usize = 64;
    let wanted = chosen.len();
    let mut bar = Progress::new("decompiled", wanted, progress && !as_json);
    let mut unit = r12e_api::Unit::default();
    let mut why = Stopped::Finished;
    if budget.unlimited() {
        unit = r12e_api::decompile_program(p, &chosen);
        bar.step();
    } else {
        for group in chosen.chunks(CHUNK) {
            let mut taking: Vec<&r12e_analysis::Function> = Vec::with_capacity(group.len());
            for f in group {
                why = budget.take();
                if !why.complete() {
                    break;
                }
                taking.push(f);
            }
            if !taking.is_empty() {
                let part = r12e_api::decompile_program(p, &taking);
                unit.declarations.extend(part.declarations);
                unit.functions.extend(part.functions);
                for _ in 0..taking.len() {
                    bar.step();
                }
            }
            if !why.complete() {
                break;
            }
        }
        // Declarations come from every chunk and repeat across them.
        unit.declarations.sort();
        unit.declarations.dedup();
    }
    bar.finish();
    let produced = unit.functions.len();
    if as_json {
        let items = unit
            .functions
            .iter()
            .map(|d| {
                let f = p.function(d.addr).unwrap_or(chosen[0]);
                (f, d.text.clone(), d.gotos, d.locals, d.unmodelled)
            })
            .collect();
        return json::emit(w, &json::decompiled(items));
    }

    if !unit.declarations.is_empty() {
        outln!(w, "#include <stdint.h>");
        for d in &unit.declarations {
            outln!(w, "{d}");
        }
        outln!(w);
    }
    crate::budget::report(&budget, why, produced, wanted, "function(s)");
    for (n, d) in unit.functions.iter().enumerate() {
        if n > 0 {
            outln!(w);
        }
        // What a reader needs to judge the output: where it came from, and how
        // much of it the structuring and the lifter could not express.
        outln!(w, "// {}", d.addr);
        if d.gotos > 0 || d.unmodelled > 0 {
            outln!(
                w,
                "// {} goto(s), {} unmodelled instruction(s)",
                d.gotos,
                d.unmodelled
            );
        }
        for line in d.text.lines() {
            outln!(w, "{line}");
        }
    }
    Ok(exit::OK)
}

/// Report what a function's pointers point at.
pub fn shapes(w: &mut Out, p: &Program, target: &str, as_json: bool) -> R {
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

    let found: Vec<(&r12e_analysis::Function, Vec<r12e_api::Pointer>)> = chosen
        .iter()
        .map(|f| (*f, r12e_api::shapes_of(p, f)))
        .filter(|(_, s)| !s.is_empty())
        .collect();

    if as_json {
        return json::emit(w, &json::shapes(&found));
    }
    if found.is_empty() {
        eprintln!("no pointers with a recoverable shape");
        return Ok(exit::NOT_FOUND);
    }
    for (n, (f, pointers)) in found.iter().enumerate() {
        if n > 0 {
            outln!(w);
        }
        outln!(w, "{} <{}>:", f.entry, f.display_name());
        for pointer in pointers {
            let name = match pointer.argument {
                Some(n) => format!("arg{n}"),
                None => format!("reg{:x}", pointer.register),
            };
            let size = match pointer.size {
                Some(s) => format!("{s} bytes"),
                None => "size unknown".to_string(),
            };
            let access = if pointer.written {
                "read and written"
            } else {
                "read only"
            };
            outln!(w, "  {name}: {size}, {access}");
            for (offset, width) in &pointer.fields {
                outln!(w, "    +{offset:<4} {width} byte(s)");
            }
        }
    }
    Ok(exit::OK)
}

/// Report what a signature library recognized.
pub fn identified(
    w: &mut Out,
    p: &Program,
    library: &r12e_db::signature::Library,
    as_json: bool,
) -> R {
    let found = r12e_api::identify(p, library);
    if as_json {
        return json::emit(w, &json::identified(&found));
    }
    if found.is_empty() {
        eprintln!("nothing in {} signature(s) matched", library.len());
        return Ok(exit::NOT_FOUND);
    }
    outln!(
        w,
        "{}",
        head(
            w,
            &format!("{:<20} {:<10} {:<28} {}", "address", "match", "name", "was")
        )
    );
    for i in &found {
        // The resolution is the point of this listing: `exact` and `shape` are
        // evidence, `address` is a coincidence until someone checks it.
        let role = match i.resolution.as_str() {
            "exact" | "shape" => Role::Strong,
            "address" => Role::Unknown,
            _ => Role::Weak,
        };
        outln!(
            w,
            "{} {} {} {}",
            cell(w, Role::Addr, &i.addr.to_string(), 20),
            cell(w, role, i.resolution.as_str(), 10),
            cell(w, Role::Name, &i.name, 28),
            i.was
        );
    }
    Ok(exit::OK)
}

/// Answer a query.
pub fn query(w: &mut Out, p: &Program, text: &str, as_json: bool) -> R {
    if text.trim().is_empty() {
        return Err("a query is needed: try `functions where insns > 100`".into());
    }
    let answer = r12e_api::query::run(p, text)?;
    if as_json {
        return json::emit(w, &json::query(&answer));
    }
    if answer.rows.is_empty() {
        eprintln!("nothing matched");
        return Ok(exit::NOT_FOUND);
    }

    // Column widths from the data, so a table of addresses does not reserve
    // room for the longest name a symbol could have.
    let widths: Vec<usize> = answer
        .columns
        .iter()
        .enumerate()
        .map(|(n, c)| {
            answer
                .rows
                .iter()
                .map(|r| {
                    r.values
                        .get(n)
                        .map(|(_, v)| escape(&v.to_string()).len())
                        .unwrap_or(0)
                })
                .chain(std::iter::once(c.len()))
                .max()
                .unwrap_or(c.len())
                .min(60)
        })
        .collect();

    let mut header = String::new();
    for (c, width) in answer.columns.iter().zip(&widths) {
        let _ = std::fmt::Write::write_fmt(&mut header, format_args!("{c:<width$}  "));
    }
    outln!(w, "{}", header.trim_end());
    for row in &answer.rows {
        let mut line = String::new();
        for ((_, value), width) in row.values.iter().zip(&widths) {
            // A string from a binary can contain anything, including the
            // newline that would break the table it is printed in.
            let text = escape(&value.to_string());
            let text = if text.len() > 60 { &text[..60] } else { &text };
            let _ = std::fmt::Write::write_fmt(&mut line, format_args!("{text:<width$}  "));
        }
        outln!(w, "{}", line.trim_end());
    }
    if answer.rows.len() < answer.matched {
        eprintln!("{} of {} shown", answer.rows.len(), answer.matched);
    }
    Ok(exit::OK)
}

/// A string that will not break the table it is printed in.
fn escape(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for c in text.chars() {
        match c {
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push('.'),
            c => out.push(c),
        }
    }
    out
}

/// Run a function and report what it did.
#[allow(clippy::too_many_arguments)]
pub fn emulate(
    w: &mut Out,
    p: &Program,
    target: &str,
    args: &[u64],
    depth: u32,
    budget: u64,
    as_json: bool,
) -> R {
    let Some(a) = addr::resolve(p, target) else {
        return Err(format!("{target:?} is not an address or a symbol"));
    };
    let Some(f) = p.function(a).or_else(|| p.function_at(a)) else {
        eprintln!("no function covers {a}");
        return Ok(exit::NOT_FOUND);
    };
    let setup = r12e_api::Setup {
        arguments: args.to_vec(),
        depth,
        budget,
        ..Default::default()
    };
    let run = r12e_api::emulate::run(p, f, &setup);

    if as_json {
        return json::emit(w, &json::run(f, &run));
    }
    outln!(w, "{} <{}>", f.entry, f.display_name());
    outln!(w, "  stopped   {}", describe(&run.stop));
    outln!(w, "  result    {:#x} ({})", run.result, run.result as i64);
    outln!(
        w,
        "  executed  {} instruction(s), {} operation(s)",
        run.insns,
        run.ops
    );
    if !run.unlifted.is_empty() {
        let shown: Vec<String> = run.unlifted.iter().take(5).map(|a| a.to_string()).collect();
        outln!(
            w,
            "  unmodelled {} instruction(s): {}",
            run.unlifted.len(),
            shown.join(", ")
        );
    }
    if !run.written.is_empty() {
        outln!(w, "  wrote     {} byte(s) of memory", run.written.len());
    }
    Ok(exit::OK)
}

/// Why a run stopped, in words.
fn describe(stop: &r12e_ir::Stop) -> String {
    use r12e_ir::Stop;
    match stop {
        Stop::Returned => "returned".into(),
        Stop::Budget => "ran out of budget".into(),
        Stop::Unimplemented(a) => {
            format!("reached an instruction the lifter does not model at {a}")
        }
        Stop::NoCode(a) => format!("branched to {a}, where there is no code"),
        Stop::Call(a) => format!("called {a}, and calls were not being followed"),
        Stop::DivideByZero(a) => format!("divided by zero at {a}"),
    }
}

/// List the virtual tables.
pub fn vtables(w: &mut Out, p: &Program, as_json: bool) -> R {
    let tables = r12e_api::vtables(p);
    if as_json {
        return json::emit(w, &json::vtables(p, &tables));
    }
    if tables.is_empty() {
        eprintln!("no virtual tables found");
        return Ok(exit::NOT_FOUND);
    }
    for (n, t) in tables.iter().enumerate() {
        if n > 0 {
            outln!(w);
        }
        outln!(
            w,
            "{} <{}>  {} method(s), {}",
            t.entry,
            t.class.as_deref().unwrap_or("unnamed"),
            t.methods.len(),
            t.evidence.as_str()
        );
        if t.offset_to_top != 0 {
            outln!(w, "  offset to top {}", t.offset_to_top);
        }
        for (slot, method) in t.methods.iter().enumerate() {
            let name = p
                .function(*method)
                .map(|f| f.display_name())
                .unwrap_or_else(|| format!("{method}"));
            outln!(w, "  [{slot}] {method}  {name}");
        }
    }
    Ok(exit::OK)
}

/// Overlay, entropy and what they suggest.
pub fn overlay(w: &mut Out, o: &Object, data: &[u8], as_json: bool) -> R {
    let report = r12e_format::overlay::analyze(o, data);
    if as_json {
        return json::emit(w, &json::overlay(&report));
    }
    outln!(w, "described end  {:#x}", report.described_end);
    match &report.overlay {
        Some(ov) => outln!(
            w,
            "overlay        {:#x}, {} bytes, entropy {:.2}, looks like {}",
            ov.offset,
            ov.size,
            ov.entropy,
            ov.content.as_str()
        ),
        None => outln!(w, "overlay        none"),
    }
    if !report.sections.is_empty() {
        outln!(w, "");
        outln!(
            w,
            "{:<24}{:>10}  {:>8}  {:>8}",
            "section",
            "size",
            "entropy",
            "peak"
        );
        for s in &report.sections {
            let peak = s.peak().map(|p| p.entropy).unwrap_or(s.entropy);
            outln!(
                w,
                "{:<24}{:>10x}  {:>8.2}  {:>8.2}",
                s.name,
                s.size,
                s.entropy,
                peak
            );
        }
    }
    if !report.findings.is_empty() {
        outln!(w, "");
        for f in &report.findings {
            let where_ = f.section.as_deref().unwrap_or("image");
            outln!(w, "{:<10} {:<24} {}", f.strength.as_str(), where_, f.detail);
        }
    }
    for warn in &report.warnings {
        eprintln!("note: {warn}");
    }
    // Nothing found is a real answer about a file, not a failed lookup.
    Ok(exit::OK)
}

/// Members of an `ar` archive, and the symbols each one defines.
pub fn archive(w: &mut Out, data: &[u8], symbols: bool, as_json: bool) -> R {
    let ar = r12e_format::archive::open(data).map_err(|e| e.to_string())?;
    if as_json {
        return json::emit(w, &json::archive(&ar));
    }
    outln!(
        w,
        "{} archive, {} member(s), {} indexed symbol(s){}",
        ar.flavor.as_str(),
        ar.members.len(),
        ar.index.len(),
        if ar.thin { ", thin" } else { "" }
    );
    outln!(w, "");
    outln!(w, "{:<44}{:>10}  {:>10}", "member", "offset", "size");
    for (n, m) in ar.members.iter().enumerate() {
        outln!(w, "{:<44}{:>10x}  {:>10x}", m.name, m.offset, m.size);
        if symbols {
            for s in ar.symbols_of(n) {
                outln!(w, "    {s}");
            }
        }
    }
    for warn in &ar.warnings {
        eprintln!("note: {warn}");
    }
    if ar.members.is_empty() {
        return Ok(exit::NOT_FOUND);
    }
    Ok(exit::OK)
}
