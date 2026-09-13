//! Byte-sized register operands, resolved against the register that holds them.
//!
//! The dataflow versions the register file in eight-byte units and keeps
//! one-byte register locations for the flags, which sit above the registers. A
//! lifter that names `al`, or the low byte of `w0`, as a one-byte register
//! varnode therefore names storage that no write to the whole register ever
//! reaches: the read misses its definition and the write is dead. These tests
//! pin that no lifted function does that, and that the two shapes it broke
//! carry their value through.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use r12e_analysis::{Options, Program, analyze};
use r12e_core::{Addr, Arch};
use r12e_format::LoadOptions;
use r12e_ir::lift::{aarch64, x86};
use r12e_ir::op::Space;
use r12e_ir::ssa::{self, Location, Operand, SsaFunction, Value};
use r12e_ir::{func, opt, stack};

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(name: &str) -> Option<Program> {
    let data = std::fs::read(corpus()?.join(name)).ok()?;
    let obj = r12e_format::load(&data, &LoadOptions::default()).ok()?;
    Some(analyze(obj, &Options::default()))
}

fn ssa_of(f: &func::Function) -> SsaFunction {
    let mut s = ssa::build(f);
    opt::optimize(&mut s);
    s
}

/// Every complete function in a program, lifted and optimized, as the
/// decompiler sees them.
fn functions(p: &Program) -> Vec<(String, SsaFunction)> {
    p.functions_by_address()
        .filter(|f| f.is_complete() && f.cfg.blocks.len() < 200)
        .filter_map(|f| {
            let blocks: BTreeMap<Addr, (Addr, Vec<Addr>)> = f
                .cfg
                .blocks
                .iter()
                .map(|(a, b)| (*a, (b.range.end(), b.successors.clone())))
                .collect();
            let mut ir = func::build(&p.object.memory, &p.object.arch, f.entry, &blocks);
            if !ir.is_complete() {
                return None;
            }
            stack::promote(&mut ir);
            Some((f.display_name(), ssa_of(&ir)))
        })
        .collect()
}

fn one(p: &Program, name: &str) -> Option<SsaFunction> {
    let f = p
        .functions_by_address()
        .find(|f| f.display_name() == name)?;
    let blocks: BTreeMap<Addr, (Addr, Vec<Addr>)> = f
        .cfg
        .blocks
        .iter()
        .map(|(a, b)| (*a, (b.range.end(), b.successors.clone())))
        .collect();
    let mut ir = func::build(&p.object.memory, &p.object.arch, f.entry, &blocks);
    stack::promote(&mut ir);
    Some(ssa_of(&ir))
}

/// The first register-file offset that is not a general register. Above it a
/// one-byte location is a flag, which is meant to be a location of its own.
fn flags_begin(arch: &Arch) -> u64 {
    match arch {
        Arch::AArch64 => aarch64::gpr_offset(32),
        _ => x86::gpr_offset(16),
    }
}

/// Every location an operation names, whether defined or read.
fn locations(f: &SsaFunction) -> Vec<(Addr, Location)> {
    let mut out = Vec::new();
    for b in f.blocks.values() {
        for op in &b.ops {
            if let Some(v) = op.out {
                out.push((op.addr, v.location));
            }
            for i in &op.inputs {
                match i {
                    Operand::Value(v) => out.push((op.addr, v.location)),
                    Operand::Undefined(l) => out.push((op.addr, *l)),
                    Operand::Const(..) => {}
                }
            }
        }
    }
    out
}

/// No function anywhere in the corpus names a byte of a general register as a
/// location of its own.
///
/// This is the invariant the two defects broke. It is checked over whole
/// binaries rather than over one instruction because the ways in are many: a
/// `setcc`, a shift count in `cl`, an `strb` of a register, a byte multiply.
#[test]
fn no_function_versions_a_byte_of_a_general_register() {
    for binary in [
        "dt-arith.x64.O2",
        "dt-memory.x64.O2",
        "driver.x64.O0",
        "driver.x64.O2",
        "dt-arith.a64.O2",
        "dt-memory.a64.O2",
        "driver.a64.O0",
        "driver.a64.O2",
    ] {
        let Some(p) = open(binary) else { continue };
        let limit = flags_begin(&p.object.arch);
        let mut bad = Vec::new();
        for (name, s) in functions(&p) {
            for (at, l) in locations(&s) {
                if l.space == Space::Register && l.size == 1 && l.offset < limit {
                    bad.push(format!("{name} at {at:?}: {:#x}:1", l.offset));
                }
            }
        }
        bad.dedup();
        assert!(
            bad.is_empty(),
            "{binary}: {} byte-of-a-register location(s), the first few:\n  {}",
            bad.len(),
            bad[..bad.len().min(8)].join("\n  ")
        );
    }
}

/// Everything the value of `at` depends on, following definitions backwards.
fn depends_on(f: &SsaFunction, at: Value) -> BTreeSet<Location> {
    let mut defs: BTreeMap<Value, Vec<Operand>> = BTreeMap::new();
    for b in f.blocks.values() {
        for op in &b.ops {
            if let Some(v) = op.out {
                defs.insert(v, op.inputs.clone());
            }
        }
    }
    let mut seen = BTreeSet::new();
    let mut out = BTreeSet::new();
    let mut work = vec![at];
    while let Some(v) = work.pop() {
        if !seen.insert(v) {
            continue;
        }
        out.insert(v.location);
        for i in defs.get(&v).into_iter().flatten() {
            match i {
                Operand::Value(u) => work.push(*u),
                Operand::Undefined(l) => {
                    out.insert(*l);
                }
                Operand::Const(..) => {}
            }
        }
    }
    out
}

/// Every definition of a register in a function, newest last.
fn defs_of(f: &SsaFunction, offset: u64) -> Vec<Value> {
    let mut out: Vec<Value> = Vec::new();
    for b in f.blocks.values() {
        for op in &b.ops {
            if let Some(v) = op.out {
                if v.location.space == Space::Register && v.location.offset == offset {
                    out.push(v);
                }
            }
        }
    }
    out.sort_by_key(|v| v.version);
    out
}

/// `iszero` is `xor eax, eax; test edi, edi; sete al; ret`, so the returned
/// `rax` has to depend on `rdi`. With the `sete` writing a location of its own
/// the whole comparison was dead and the function returned the constant zero.
#[test]
fn a_setcc_into_a_zeroed_register_reaches_the_result() {
    let Some(p) = open("dt-arith.x64.O2") else {
        return;
    };
    let s = one(&p, "iszero").expect("iszero");
    let rax = *defs_of(&s, x86::gpr_offset(0))
        .last()
        .expect("rax is written");
    let sources = depends_on(&s, rax);
    let rdi = x86::gpr_offset(7);
    assert!(
        sources
            .iter()
            .any(|l| l.space == Space::Register && l.offset == rdi),
        "iszero returns something that does not depend on rdi: {sources:?}"
    );
}

/// `rotate` computes two different shift counts into `ecx` and shifts by `cl`
/// each time. Reading `cl` as a location of its own missed both writes, so the
/// counts collapsed into one and the function grew `rcx` as an argument.
#[test]
fn a_shift_by_cl_reads_the_ecx_the_code_computed() {
    let Some(p) = open("driver.x64.O0") else {
        return;
    };
    let s = one(&p, "rotate").expect("rotate");
    let rcx = x86::gpr_offset(1);
    for (at, l) in locations(&s) {
        assert!(
            !(l.space == Space::Register && l.offset == rcx && l.size == 1),
            "rotate at {at:?} still versions cl on its own"
        );
    }
    let undefined: Vec<String> = s
        .blocks
        .values()
        .flat_map(|b| b.ops.iter())
        .flat_map(|op| op.inputs.iter())
        .filter_map(|i| match i {
            Operand::Undefined(l) if l.space == Space::Register && l.offset == rcx => {
                Some(format!("{:#x}:{}", l.offset, l.size))
            }
            _ => None,
        })
        .collect();
    assert!(
        undefined.is_empty(),
        "rotate reads rcx before writing it, so the shift count came from the caller: {undefined:?}"
    );
}
