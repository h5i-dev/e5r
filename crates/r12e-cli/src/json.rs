//! The JSON surface.
//!
//! Versioned: `schema` names the shape, and a breaking change to any of these
//! bumps the major version. Agents and scripts read this, so it is an API.

use r12e_analysis::{Function, Program, Xref};
use r12e_arch::Insn;
use r12e_core::Addr;
use r12e_format::Object;
use serde::Serialize;

use crate::exit;

/// The schema version every document carries.
const SCHEMA: &str = "r12e/1";

/// Print a document and report success.
pub fn emit<T: Serialize>(w: &mut crate::out::Out, value: &T) -> Result<u8, String> {
    let s = serde_json::to_string_pretty(value).map_err(|e| e.to_string())?;
    w.line(format_args!("{s}"));
    Ok(exit::OK)
}

/// Addresses serialize as hex strings: JSON numbers lose the top bits of a
/// 64-bit address in any consumer that parses them as doubles.
fn hex(a: Addr) -> String {
    format!("{:#x}", a.get())
}

#[derive(Serialize)]
pub struct Info {
    schema: &'static str,
    format: String,
    arch: String,
    bits: u8,
    endian: &'static str,
    entry: Option<String>,
    image_base: String,
    pic: bool,
    segments: usize,
    symbols: usize,
    imports: usize,
    exports: usize,
    function_hints: usize,
    metadata: std::collections::BTreeMap<String, String>,
    warnings: Vec<String>,
}

pub fn info(o: &Object) -> Info {
    Info {
        schema: SCHEMA,
        format: o.format.to_string(),
        arch: o.arch.to_string(),
        bits: o.bits.bytes() as u8 * 8,
        endian: match o.endian {
            r12e_core::Endian::Little => "little",
            r12e_core::Endian::Big => "big",
        },
        entry: o.entry.map(hex),
        image_base: hex(o.image_base),
        pic: o.pic,
        segments: o.memory.segments().len(),
        symbols: o.symbols.len(),
        imports: o.imports.len(),
        exports: o.exports.len(),
        function_hints: o.function_hints.len(),
        metadata: o.metadata.clone(),
        warnings: o.warnings.clone(),
    }
}

#[derive(Serialize)]
pub struct SectionOut {
    name: String,
    addr: String,
    size: String,
    file_offset: String,
    file_size: String,
    exec: bool,
    write: bool,
}

#[derive(Serialize)]
pub struct Listing<T> {
    schema: &'static str,
    count: usize,
    items: Vec<T>,
}

fn listing<T>(items: Vec<T>) -> Listing<T> {
    Listing {
        schema: SCHEMA,
        count: items.len(),
        items,
    }
}

pub fn sections(o: &Object) -> Listing<SectionOut> {
    listing(
        o.sections
            .iter()
            .map(|s| SectionOut {
                name: s.name.clone(),
                addr: hex(s.range.start()),
                size: format!("{:#x}", s.range.len()),
                file_offset: format!("{:#x}", s.file_offset),
                file_size: format!("{:#x}", s.file_size),
                exec: s.exec,
                write: s.write,
            })
            .collect(),
    )
}

#[derive(Serialize)]
pub struct SymbolOut {
    name: String,
    addr: String,
    size: String,
    kind: String,
    binding: String,
    dynamic: bool,
}

pub fn symbols(o: &Object) -> Listing<SymbolOut> {
    listing(
        o.symbols
            .iter()
            .map(|s| SymbolOut {
                name: s.name.clone(),
                addr: hex(s.addr),
                size: format!("{:#x}", s.size),
                kind: format!("{:?}", s.kind).to_lowercase(),
                binding: format!("{:?}", s.binding).to_lowercase(),
                dynamic: s.dynamic,
            })
            .collect(),
    )
}

#[derive(Serialize)]
pub struct ImportOut {
    name: String,
    library: Option<String>,
    thunk: Option<String>,
}

pub fn imports(o: &Object) -> Listing<ImportOut> {
    listing(
        o.imports
            .iter()
            .map(|i| ImportOut {
                name: i.name.clone(),
                library: i.library.clone(),
                thunk: i.thunk.map(hex),
            })
            .collect(),
    )
}

#[derive(Serialize)]
pub struct ExportOut {
    name: String,
    addr: String,
}

pub fn exports(o: &Object) -> Listing<ExportOut> {
    listing(
        o.exports
            .iter()
            .map(|e| ExportOut {
                name: e.name.clone(),
                addr: hex(e.addr),
            })
            .collect(),
    )
}

#[derive(Serialize)]
pub struct FunctionOut {
    addr: String,
    name: String,
    named: bool,
    size: String,
    blocks: usize,
    insns: u32,
    complete: bool,
    strength: &'static str,
    evidence: Vec<String>,
}

fn function_out(f: &Function) -> FunctionOut {
    let mut evidence = vec![f.provenance.best.as_str().to_string()];
    evidence.extend(
        f.provenance
            .corroborating
            .iter()
            .map(|e| e.as_str().to_string()),
    );
    FunctionOut {
        addr: hex(f.entry),
        name: f.display_name(),
        named: f.name.is_some(),
        size: format!("{:#x}", f.cfg.covered_bytes()),
        blocks: f.cfg.blocks.len(),
        insns: f.cfg.insns(),
        complete: f.is_complete(),
        strength: crate::print::strength_name(f.provenance.strength()),
        evidence,
    }
}

pub fn funcs(p: &Program) -> Listing<FunctionOut> {
    listing(p.functions_by_address().map(function_out).collect())
}

#[derive(Serialize)]
pub struct Stats {
    schema: &'static str,
    functions: usize,
    complete: usize,
    capped: usize,
    noreturn: usize,
    blocks: usize,
    tables: usize,
    table_targets: usize,
    indirect: usize,
    insns: u64,
    xrefs: usize,
    strings: usize,
    rounds: usize,
    by_strength: std::collections::BTreeMap<String, usize>,
}

pub fn stats(p: &Program) -> Stats {
    let s = p.stats();
    Stats {
        schema: SCHEMA,
        functions: s.functions,
        complete: s.complete,
        capped: s.capped,
        noreturn: s.noreturn,
        blocks: s.blocks,
        tables: s.tables,
        table_targets: s.table_targets,
        indirect: s.indirect,
        insns: s.insns,
        xrefs: s.xrefs,
        strings: s.strings,
        rounds: p.rounds,
        by_strength: p
            .by_strength()
            .into_iter()
            .map(|(k, v)| (k.as_str().to_string(), v))
            .collect(),
    }
}

#[derive(Serialize)]
pub struct InsnOut {
    addr: String,
    len: u8,
    text: String,
    flow: String,
    target: Option<String>,
}

#[derive(Serialize)]
pub struct DisasOut {
    function: FunctionOut,
    insns: Vec<InsnOut>,
}

fn insn_out(p: &Program, i: &Insn) -> InsnOut {
    InsnOut {
        addr: hex(i.addr),
        len: i.len,
        text: r12e_arch::format(&p.object.arch, i, false).replace('\t', " "),
        flow: match i.flow {
            r12e_arch::Flow::Next => "next",
            r12e_arch::Flow::Branch(_) => "branch",
            r12e_arch::Flow::CondBranch(_) => "cond_branch",
            r12e_arch::Flow::IndirectBranch => "indirect_branch",
            r12e_arch::Flow::Call(_) => "call",
            r12e_arch::Flow::IndirectCall => "indirect_call",
            r12e_arch::Flow::Return => "return",
            r12e_arch::Flow::Trap => "trap",
            r12e_arch::Flow::Syscall => "syscall",
        }
        .to_string(),
        target: i.flow.target().map(hex),
    }
}

/// One decompiled function, with the numbers that say how well it went.
#[derive(Serialize)]
pub struct DecompileOut {
    function: FunctionOut,
    code: String,
    gotos: usize,
    locals: usize,
    unmodelled: usize,
}

pub fn decompiled(items: Vec<(&Function, String, usize, usize, usize)>) -> Listing<DecompileOut> {
    listing(
        items
            .into_iter()
            .map(|(f, code, gotos, locals, unmodelled)| DecompileOut {
                function: function_out(f),
                code,
                gotos,
                locals,
                unmodelled,
            })
            .collect(),
    )
}

/// One pointer's inferred shape.
#[derive(Serialize)]
pub struct FieldOut {
    offset: i64,
    size: u8,
}

/// What one function's pointers point at.
#[derive(Serialize)]
pub struct ShapeOut {
    function: FunctionOut,
    pointers: Vec<PointerOut>,
}

#[derive(Serialize)]
pub struct PointerOut {
    argument: Option<usize>,
    register: String,
    size: Option<u64>,
    written: bool,
    fields: Vec<FieldOut>,
}

pub fn shapes(found: &[(&Function, Vec<r12e_api::Pointer>)]) -> Listing<ShapeOut> {
    listing(
        found
            .iter()
            .map(|(f, pointers)| ShapeOut {
                function: function_out(f),
                pointers: pointers
                    .iter()
                    .map(|p| PointerOut {
                        argument: p.argument,
                        register: format!("{:#x}", p.register),
                        size: p.size,
                        written: p.written,
                        fields: p
                            .fields
                            .iter()
                            .map(|(offset, size)| FieldOut {
                                offset: *offset,
                                size: *size,
                            })
                            .collect(),
                    })
                    .collect(),
            })
            .collect(),
    )
}

/// One function a signature library recognized.
#[derive(Serialize)]
pub struct IdentifiedOut {
    addr: String,
    name: String,
    was: String,
    r#match: String,
    source: String,
}

pub fn identified(found: &[r12e_api::Identified]) -> Listing<IdentifiedOut> {
    listing(
        found
            .iter()
            .map(|i| IdentifiedOut {
                addr: hex(i.addr),
                name: i.name.clone(),
                was: i.was.clone(),
                r#match: i.resolution.as_str().to_string(),
                source: i.source.clone(),
            })
            .collect(),
    )
}

/// The answer to a query, as objects keyed by column name.
#[derive(Serialize)]
pub struct QueryOut {
    schema: &'static str,
    entity: String,
    matched: usize,
    count: usize,
    items: Vec<std::collections::BTreeMap<String, serde_json::Value>>,
}

pub fn query(answer: &r12e_api::Answer) -> QueryOut {
    let items = answer
        .rows
        .iter()
        .map(|row| {
            row.values
                .iter()
                .map(|(name, value)| {
                    use r12e_api::query::Field;
                    let v = match value {
                        Field::Number(n) => serde_json::Value::from(*n),
                        Field::Address(a) => serde_json::Value::from(hex(*a)),
                        Field::Text(t) => serde_json::Value::from(t.clone()),
                        Field::Bool(b) => serde_json::Value::from(*b),
                        Field::Missing => serde_json::Value::Null,
                    };
                    (name.to_string(), v)
                })
                .collect()
        })
        .collect::<Vec<_>>();
    QueryOut {
        schema: SCHEMA,
        entity: answer.entity.as_str().to_string(),
        matched: answer.matched,
        count: items.len(),
        items,
    }
}

/// What one emulated run did.
#[derive(Serialize)]
pub struct RunOut {
    function: FunctionOut,
    stopped: String,
    result: String,
    insns: u64,
    ops: u64,
    unmodelled: Vec<String>,
    bytes_written: usize,
}

pub fn run(f: &Function, r: &r12e_api::Run) -> RunOut {
    RunOut {
        function: function_out(f),
        stopped: format!("{:?}", r.stop).to_lowercase(),
        result: format!("{:#x}", r.result),
        insns: r.insns,
        ops: r.ops,
        unmodelled: r.unlifted.iter().map(|a| hex(*a)).collect(),
        bytes_written: r.written.len(),
    }
}

/// One virtual table.
#[derive(Serialize)]
pub struct VTableOut {
    addr: String,
    entry: String,
    class: Option<String>,
    offset_to_top: i64,
    typeinfo: Option<String>,
    evidence: String,
    methods: Vec<MethodOut>,
}

#[derive(Serialize)]
pub struct MethodOut {
    slot: usize,
    addr: String,
    name: Option<String>,
}

pub fn vtables(p: &Program, tables: &[r12e_api::VTable]) -> Listing<VTableOut> {
    listing(
        tables
            .iter()
            .map(|t| VTableOut {
                addr: hex(t.addr),
                entry: hex(t.entry),
                class: t.class.clone(),
                offset_to_top: t.offset_to_top,
                typeinfo: t.typeinfo.map(hex),
                evidence: t.evidence.as_str().to_string(),
                methods: t
                    .methods
                    .iter()
                    .enumerate()
                    .map(|(slot, addr)| MethodOut {
                        slot,
                        addr: hex(*addr),
                        name: p.function(*addr).map(|f| f.display_name()),
                    })
                    .collect(),
            })
            .collect(),
    )
}

pub fn disas(p: &Program, fns: &[&Function]) -> Listing<DisasOut> {
    listing(
        fns.iter()
            .map(|f| DisasOut {
                function: function_out(f),
                insns: p.instructions(f).iter().map(|i| insn_out(p, i)).collect(),
            })
            .collect(),
    )
}

#[derive(Serialize)]
pub struct XrefOut {
    from: String,
    to: String,
    kind: String,
    from_function: Option<String>,
}

pub fn xrefs(p: &Program, refs: &[Xref]) -> Listing<XrefOut> {
    listing(
        refs.iter()
            .map(|x| XrefOut {
                from: hex(x.from),
                to: hex(x.to),
                kind: format!("{:?}", x.kind).to_lowercase(),
                from_function: p.function_at(x.from).map(|f| f.display_name()),
            })
            .collect(),
    )
}

/// A comparison of two builds.
#[derive(Serialize)]
pub struct DiffOut {
    schema: &'static str,
    matched: usize,
    changed: usize,
    identical: usize,
    removed: Vec<Value>,
    added: Vec<Value>,
    /// Changed pairs, most changed first.
    changes: Vec<Value>,
}

use serde_json::{Value, json};

pub fn diff(d: &r12e_diff::Diff) -> DiffOut {
    let pair = |m: &r12e_diff::Match| {
        json!({
            "old": format!("{:#x}", m.old.get()),
            "new": format!("{:#x}", m.new.get()),
            "name": m.name,
            "kind": m.kind.as_str(),
            "similarity": m.similarity,
            "old_insns": m.old_insns,
            "new_insns": m.new_insns,
        })
    };
    let side = |(a, n): &(r12e_core::Addr, String)| json!({ "addr": format!("{:#x}", a.get()), "name": n });
    DiffOut {
        schema: SCHEMA,
        matched: d.matched.len(),
        changed: d.changed_count(),
        identical: d.identical_count(),
        removed: d.removed.iter().map(side).collect(),
        added: d.added.iter().map(side).collect(),
        changes: d.changed().map(pair).collect(),
    }
}

#[derive(Serialize)]
pub struct OverlayOut {
    offset: String,
    size: u64,
    entropy: f64,
    content: &'static str,
}

#[derive(Serialize)]
pub struct SectionEntropyOut {
    name: String,
    file_offset: String,
    size: u64,
    entropy: f64,
    peak_entropy: f64,
    peak_offset: Option<String>,
}

#[derive(Serialize)]
pub struct FindingOut {
    kind: &'static str,
    section: Option<String>,
    detail: String,
    strength: &'static str,
}

#[derive(Serialize)]
pub struct OverlayReport {
    schema: &'static str,
    described_end: String,
    overlay: Option<OverlayOut>,
    sections: Vec<SectionEntropyOut>,
    findings: Vec<FindingOut>,
    warnings: Vec<String>,
}

pub fn overlay(r: &r12e_format::overlay::Report) -> OverlayReport {
    OverlayReport {
        schema: SCHEMA,
        described_end: format!("{:#x}", r.described_end),
        overlay: r.overlay.as_ref().map(|o| OverlayOut {
            offset: format!("{:#x}", o.offset),
            size: o.size,
            entropy: o.entropy,
            content: o.content.as_str(),
        }),
        sections: r
            .sections
            .iter()
            .map(|s| SectionEntropyOut {
                name: s.name.clone(),
                file_offset: format!("{:#x}", s.file_offset),
                size: s.size,
                entropy: s.entropy,
                peak_entropy: s.peak().map(|p| p.entropy).unwrap_or(s.entropy),
                peak_offset: s.peak().map(|p| format!("{:#x}", p.offset)),
            })
            .collect(),
        findings: r
            .findings
            .iter()
            .map(|f| FindingOut {
                kind: f.kind.as_str(),
                section: f.section.clone(),
                detail: f.detail.clone(),
                strength: f.strength.as_str(),
            })
            .collect(),
        warnings: r.warnings.clone(),
    }
}

#[derive(Serialize)]
pub struct MemberOut {
    name: String,
    offset: u64,
    size: u64,
    mtime: u64,
    symbols: Vec<String>,
}

#[derive(Serialize)]
pub struct ArchiveOut {
    schema: &'static str,
    flavor: &'static str,
    thin: bool,
    members: Vec<MemberOut>,
    warnings: Vec<String>,
}

pub fn archive(a: &r12e_format::archive::Archive) -> ArchiveOut {
    ArchiveOut {
        schema: SCHEMA,
        flavor: a.flavor.as_str(),
        thin: a.thin,
        members: a
            .members
            .iter()
            .enumerate()
            .map(|(n, m)| MemberOut {
                name: m.name.clone(),
                offset: m.offset,
                size: m.size,
                mtime: m.mtime,
                symbols: a.symbols_of(n).into_iter().map(str::to_string).collect(),
            })
            .collect(),
        warnings: a.warnings.clone(),
    }
}
