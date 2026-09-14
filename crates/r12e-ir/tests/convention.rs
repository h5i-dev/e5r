//! Detecting the convention a function uses, rather than assuming one.
//!
//! Functions here are built by hand. What is under test is the classification
//! itself, and a hand-built function makes the evidence exact instead of
//! whatever a compiler happened to emit. The corpus measurements live in
//! `call_sites.rs`, where real code and the compiler's own record of it are.

use std::collections::BTreeMap;

use r12e_core::provenance::Strength;
use r12e_core::{Addr, Arch};
use r12e_ir::abi::{self, Abi, Named};
use r12e_ir::conv::{self, Convention, Departure, Observed, Purpose};
use r12e_ir::dwreg;
use r12e_ir::lift::{aarch64, x86};
use r12e_ir::op::{Op, Space};
use r12e_ir::ssa::{Location, Operand, SsaBlock, SsaFunction, SsaKind, SsaOp, Value};

const ENTRY: Addr = Addr(0x1000);

fn reg(offset: u64) -> Location {
    Location {
        space: Space::Register,
        offset,
        size: 8,
    }
}

fn op(kind: Op, out: Option<Value>, inputs: Vec<Operand>) -> SsaOp {
    SsaOp {
        addr: ENTRY,
        kind: SsaKind::Op(kind),
        out,
        inputs,
        size: 8,
    }
}

fn value(location: Location, version: u32) -> Value {
    Value { location, version }
}

fn ret() -> SsaOp {
    op(Op::Return, None, Vec::new())
}

fn func(arch: Arch, ops: Vec<SsaOp>) -> SsaFunction {
    let mut blocks = BTreeMap::new();
    blocks.insert(
        ENTRY,
        SsaBlock {
            ops,
            successors: Vec::new(),
            predecessors: Vec::new(),
        },
    );
    SsaFunction {
        arch,
        entry: ENTRY,
        blocks,
    }
}

/// A function that copies each of `sources` into the first result register and
/// returns.
fn reads(abi: &Abi, arch: Arch, sources: &[u64]) -> SsaFunction {
    let result = reg(abi.results[0]);
    let mut ops = Vec::new();
    for (n, source) in sources.iter().enumerate() {
        let version = n as u32 + 1;
        let mut inputs = vec![Operand::Undefined(reg(*source))];
        if n > 0 {
            inputs.push(Operand::Value(value(result, version - 1)));
        }
        ops.push(op(
            if n == 0 { Op::Copy } else { Op::IntAdd },
            Some(value(result, version)),
            inputs,
        ));
    }
    ops.push(ret());
    func(arch, ops)
}

#[test]
fn a_function_that_reads_no_argument_register_takes_no_arguments() {
    let abi = abi::of(&Arch::X86_64);
    let f = func(Arch::X86_64, vec![ret()]);
    let d = conv::detect(&f, &abi);

    // The whole point: the fixed order would hand this six integer arguments
    // and eight floating point ones, and it takes none.
    assert_eq!(d.convention, Convention::Standard);
    assert_eq!(d.arity(), 0);
    assert_eq!(d.assumed_arity(), 0);
    assert!(d.departures.is_empty());
    assert_eq!(d.named, Some(Named::SysV));
    assert_eq!(d.strength, Strength::Inferred);
}

#[test]
fn a_register_the_convention_passes_nothing_in_is_a_convention_the_compiler_invented() {
    let abi = abi::of(&Arch::X86_64);
    // r10 is caller-saved and System V passes no argument in it, so a static
    // function reading it at entry got a convention of its own.
    let f = reads(&abi, Arch::X86_64, &[x86::gpr_offset(10)]);
    let d = conv::detect(&f, &abi);

    assert_eq!(d.convention, Convention::NonStandard);
    assert_eq!(d.custom_registers(), vec![x86::gpr_offset(10)]);
    assert!(d.departures.contains(&Departure::Argument {
        register: x86::gpr_offset(10)
    }));
    // Not normalised into the default: no named convention fits.
    assert_eq!(d.named, None);
    assert_eq!(d.arity(), 1);
}

#[test]
fn the_platform_default_is_not_the_only_one_a_machine_has() {
    // The same four registers, under the two x86-64 conventions. Which
    // argument each one is differs, which is the whole reason a PE image
    // cannot be read with the System V table.
    let registers: Vec<u64> = [1u8, 2, 8, 9].iter().map(|n| x86::gpr_offset(*n)).collect();

    let win = abi::of_named(&Arch::X86_64, Named::Win64);
    let f = reads(&win, Arch::X86_64, &registers);
    let d = conv::detect(&f, &win);
    let purposes: Vec<Purpose> = d.arguments.iter().map(|a| a.purpose).collect();
    assert_eq!(
        purposes,
        vec![
            Purpose::Integer(0),
            Purpose::Integer(1),
            Purpose::Integer(2),
            Purpose::Integer(3)
        ]
    );
    assert_eq!(d.convention, Convention::Standard);
    assert_eq!(d.named, Some(Named::Win64));
    assert_eq!(d.arity(), 4);
    assert_eq!(d.assumed_arity(), 4);

    let sysv = abi::of(&Arch::X86_64);
    let d = conv::detect(&reads(&sysv, Arch::X86_64, &registers), &sysv);
    let purposes: Vec<Purpose> = d.arguments.iter().map(|a| a.purpose).collect();
    assert_eq!(
        purposes,
        vec![
            Purpose::Integer(2),
            Purpose::Integer(3),
            Purpose::Integer(4),
            Purpose::Integer(5)
        ]
    );
    // Read with the wrong table the same four registers look like the last
    // four of six, so the fixed order invents two arguments that were never
    // passed. The gap is what says so.
    assert_eq!(d.convention, Convention::Fewer);
    assert_eq!(d.arity(), 4);
    assert_eq!(d.assumed_arity(), 6);

    // The Microsoft convention reserves shadow space, so its first stack
    // argument is five slots up rather than one.
    assert_eq!(win.stack_argument_base, 40);
    assert_eq!(sysv.stack_argument_base, 8);
}

#[test]
fn a_callee_that_pops_the_callers_arguments_says_so() {
    let abi = abi::of(&Arch::X86_64);
    let sp = reg(abi.stack_pointer);
    // `ret 0x10`: the lifter pops the return address and then raises the stack
    // pointer by the immediate, so it comes back sixteen bytes higher than the
    // convention leaves it.
    let f = func(
        Arch::X86_64,
        vec![
            op(
                Op::IntAdd,
                Some(value(sp, 1)),
                vec![Operand::Undefined(sp), Operand::Const(24, 8)],
            ),
            ret(),
        ],
    );
    let d = conv::detect(&f, &abi);
    assert_eq!(d.callee_pops, 16);
    assert_eq!(d.convention, Convention::NonStandard);
    assert!(d.departures.contains(&Departure::CalleePops { bytes: 16 }));

    // The same shape under a convention where the callee does pop is the
    // named convention rather than an invention.
    let stdcall = abi::of_named(&Arch::X86, Named::Cdecl);
    let d = conv::detect(&f, &stdcall);
    assert_eq!(d.named, Some(Named::Stdcall));
}

#[test]
fn a_function_that_leaves_the_stack_where_it_found_it_pops_nothing() {
    let abi = abi::of(&Arch::X86_64);
    let sp = reg(abi.stack_pointer);
    let f = func(
        Arch::X86_64,
        vec![
            op(
                Op::IntAdd,
                Some(value(sp, 1)),
                vec![Operand::Undefined(sp), Operand::Const(8, 8)],
            ),
            ret(),
        ],
    );
    let d = conv::detect(&f, &abi);
    assert_eq!(d.callee_pops, 0);
    assert_eq!(d.convention, Convention::Standard);
}

#[test]
fn a_prologue_saving_a_register_is_not_an_argument_arriving_in_it() {
    let abi = abi::of(&Arch::X86_64);
    let rbx = reg(x86::gpr_offset(3));
    // Read rbx, use it, and reload it from the frame on the way out: the
    // ordinary prologue and epilogue, not a convention.
    let saved = func(
        Arch::X86_64,
        vec![
            op(
                Op::IntAdd,
                Some(value(rbx, 1)),
                vec![Operand::Undefined(rbx), Operand::Const(1, 8)],
            ),
            op(Op::Load, Some(value(rbx, 2)), vec![Operand::Const(0x20, 8)]),
            ret(),
        ],
    );
    let d = conv::detect(&saved, &abi);
    assert_eq!(d.convention, Convention::Standard);
    assert!(d.custom_registers().is_empty());

    // The same read with no restore is a register the compiler took for
    // itself, and both facts are reported.
    let taken = func(
        Arch::X86_64,
        vec![
            op(
                Op::IntAdd,
                Some(value(rbx, 1)),
                vec![Operand::Undefined(rbx), Operand::Const(1, 8)],
            ),
            ret(),
        ],
    );
    let d = conv::detect(&taken, &abi);
    assert_eq!(d.convention, Convention::NonStandard);
    assert_eq!(d.custom_registers(), vec![x86::gpr_offset(3)]);
    assert!(d.departures.contains(&Departure::Clobbers {
        register: x86::gpr_offset(3)
    }));
}

#[test]
fn the_registers_a_convention_reserves_are_not_arguments() {
    // AAPCS64 passes the address of a memory-returned result in x8 and the
    // return address arrives in x30. Neither is something a caller passed, and
    // counting them would give every large-struct function an extra argument.
    let abi = abi::of(&Arch::AArch64);
    let f = reads(
        &abi,
        Arch::AArch64,
        &[aarch64::gpr_offset(8), aarch64::gpr_offset(30)],
    );
    let d = conv::detect(&f, &abi);
    assert_eq!(d.arity(), 0);
    assert_eq!(d.convention, Convention::Standard);
    assert!(
        d.arguments
            .iter()
            .any(|a| a.purpose == Purpose::IndirectResult)
    );

    // System V reports the variadic vector count the same way.
    let sysv = abi::of(&Arch::X86_64);
    let f = reads(&sysv, Arch::X86_64, &[x86::gpr_offset(0)]);
    let d = conv::detect(&f, &sysv);
    assert_eq!(d.arity(), 0);
    assert_eq!(d.convention, Convention::Standard);
}

#[test]
fn a_result_nobody_reads_is_not_a_result() {
    let abi = abi::of(&Arch::X86_64);
    let f = reads(&abi, Arch::X86_64, &[abi.integer_arguments[0]]);
    // On its own the function has left something in rax.
    assert_eq!(conv::detect(&f, &abi).result, Some(x86::gpr_offset(0)));

    // Two callers, neither of which reads it: it returns nothing, and `void`
    // beats a fabricated `uint64_t`.
    let ignored = Observed {
        sites: 2,
        result_read: 0,
        ..Observed::default()
    };
    assert_eq!(conv::detect_with(&f, &abi, &ignored).result, None);

    // One that does: the result stands.
    let read = Observed {
        sites: 2,
        result_read: 1,
        ..Observed::default()
    };
    assert_eq!(
        conv::detect_with(&f, &abi, &read).result,
        Some(x86::gpr_offset(0))
    );
}

#[test]
fn call_sites_corroborate_what_one_functions_reads_only_suggest() {
    let abi = abi::of(&Arch::X86_64);
    let f = reads(&abi, Arch::X86_64, &[abi.integer_arguments[0]]);

    let alone = conv::detect(&f, &abi);
    assert_eq!(alone.strength, Strength::Inferred);
    assert_eq!(alone.support, 0);

    let mut seen = Observed {
        sites: 3,
        result_read: 3,
        ..Observed::default()
    };
    seen.set.insert(abi.integer_arguments[0], 3);
    let corroborated = conv::detect_with(&f, &abi, &seen);
    assert_eq!(corroborated.strength, Strength::Inferred);
    assert_eq!(corroborated.support, 3);
    // Better evidence sorts first.
    assert_eq!(
        corroborated.rank(&alone),
        std::cmp::Ordering::Less,
        "three agreeing call sites outrank one function's reads"
    );
}

#[test]
fn what_the_compiler_recorded_about_its_own_calls_is_the_strongest_gate() {
    let abi = abi::of(&Arch::X86_64);
    let f = reads(
        &abi,
        Arch::X86_64,
        &[abi.integer_arguments[0], abi.integer_arguments[1]],
    );

    // `DW_TAG_call_site_parameter` said rdi and rsi, which is what the reads
    // say, so this is stated by the file rather than derived from it.
    let recorded = Observed {
        sites: 2,
        result_read: 2,
        recorded: vec![
            vec![abi.integer_arguments[0], abi.integer_arguments[1]],
            vec![abi.integer_arguments[0], abi.integer_arguments[1]],
        ],
        ..Observed::default()
    };
    let d = conv::detect_with(&f, &abi, &recorded);
    assert_eq!(d.strength, Strength::Proven);
    assert_eq!(d.support, 2);
    assert_eq!(recorded.recorded_arity(), Some(2));

    // A record naming a register the function never reads means the reads are
    // measuring something else, and the claim drops back to a guess rather
    // than quietly winning.
    let disagreeing = Observed {
        sites: 1,
        recorded: vec![vec![abi.integer_arguments[4]]],
        ..Observed::default()
    };
    assert_eq!(
        conv::detect_with(&f, &abi, &disagreeing).strength,
        Strength::Heuristic
    );
}

#[test]
fn a_function_the_lifter_did_not_model_says_unknown_rather_than_guessing() {
    let abi = abi::of(&Arch::X86_64);
    let f = func(
        Arch::X86_64,
        vec![
            op(
                Op::Copy,
                Some(value(reg(abi.results[0]), 1)),
                vec![Operand::Undefined(reg(x86::gpr_offset(10)))],
            ),
            op(Op::Unimplemented, None, Vec::new()),
            ret(),
        ],
    );
    let d = conv::detect(&f, &abi);
    assert_eq!(d.convention, Convention::Unknown);
    assert_eq!(d.strength, Strength::Heuristic);
    assert_eq!(d.named, None);
}

#[test]
fn a_function_nothing_returns_from_says_so() {
    let abi = abi::of(&Arch::X86_64);
    let f = func(
        Arch::X86_64,
        vec![op(
            Op::Copy,
            Some(value(reg(abi.results[0]), 1)),
            vec![Operand::Const(0, 8)],
        )],
    );
    let d = conv::detect(&f, &abi);
    assert!(!d.returns_to_caller);
    assert!(d.departures.contains(&Departure::NeverReturns));
    // Recovering a result from a function that never comes back is
    // meaningless, so none is claimed.
    assert_eq!(d.result, None);
}

#[test]
fn an_object_pointer_is_recognised_by_what_is_done_with_it() {
    let abi = abi::of(&Arch::X86_64);
    let this = reg(abi.integer_arguments[0]);
    let result = reg(abi.results[0]);
    // A member function loads through its first argument and never treats it
    // as a number.
    let member = func(
        Arch::X86_64,
        vec![
            op(
                Op::Load,
                Some(value(result, 1)),
                vec![Operand::Undefined(this)],
            ),
            ret(),
        ],
    );
    assert_eq!(
        conv::detect(&member, &abi).this_register,
        Some(abi.integer_arguments[0])
    );

    // One that adds its first argument to something is doing arithmetic on it,
    // which an object is not.
    let arithmetic = reads(&abi, Arch::X86_64, &[abi.integer_arguments[0]]);
    assert_eq!(conv::detect(&arithmetic, &abi).this_register, None);
}

#[test]
fn what_the_callers_say_reaches_the_prototype() {
    let abi = abi::of(&Arch::X86_64);
    let f = reads(&abi, Arch::X86_64, &[abi.integer_arguments[0]]);
    let ignored = Observed {
        sites: 4,
        result_read: 0,
        ..Observed::default()
    };
    let p = r12e_ir::proto::recover_observed(&f, &abi, &ignored);
    assert_eq!(p.returns, None);
    assert_eq!(p.integer_arguments, 1);
    assert_eq!(p.detected.convention, Convention::Standard);

    // Recovery with nothing observed is unchanged: a function nothing calls
    // keeps its own answer.
    let alone = r12e_ir::proto::recover(&f, &abi);
    assert_eq!(alone.returns, Some(x86::gpr_offset(0)));
    assert_eq!(alone.detected.convention, Convention::Standard);
}

#[test]
fn observing_a_caller_records_what_it_filled_and_what_it_read_back() {
    let abi = abi::of(&Arch::X86_64);
    let target = Addr(0x2000);
    let rdi = reg(abi.integer_arguments[0]);
    let rax = reg(x86::gpr_offset(0));
    let caller = func(
        Arch::X86_64,
        vec![
            op(Op::Copy, Some(value(rdi, 1)), vec![Operand::Const(7, 8)]),
            op(
                Op::Call,
                Some(value(rax, 1)),
                vec![Operand::Const(target.0, 8)],
            ),
            op(
                Op::Copy,
                Some(value(rdi, 2)),
                vec![Operand::Value(value(rax, 1))],
            ),
            ret(),
        ],
    );
    let seen = conv::observe(&caller, &abi);
    let seen = seen.get(&target).expect("the call was seen");
    assert_eq!(seen.sites, 1);
    assert_eq!(seen.result_read, 1);
    assert_eq!(seen.set.get(&abi.integer_arguments[0]), Some(&1));
    assert!(!seen.is_empty());
}

#[test]
fn dwarf_register_numbers_are_not_the_encoding_order() {
    // The one that bites: DWARF 1 is rdx and DWARF 2 is rcx, where the
    // instruction encoding has them the other way round.
    assert_eq!(dwreg::offset(&Arch::X86_64, 1), Some(x86::gpr_offset(2)));
    assert_eq!(dwreg::offset(&Arch::X86_64, 2), Some(x86::gpr_offset(1)));
    // And the one every System V argument list starts with.
    assert_eq!(dwreg::offset(&Arch::X86_64, 5), Some(x86::gpr_offset(7)));
    assert_eq!(dwreg::offset(&Arch::X86_64, 4), Some(x86::gpr_offset(6)));
    assert_eq!(dwreg::offset(&Arch::X86_64, 17), Some(x86::vec_offset(0)));
    // 16 is the return address, which is not in the register file.
    assert_eq!(dwreg::offset(&Arch::X86_64, 16), None);

    assert_eq!(
        dwreg::offset(&Arch::AArch64, 0),
        Some(aarch64::gpr_offset(0))
    );
    assert_eq!(
        dwreg::offset(&Arch::AArch64, 31),
        Some(aarch64::sp_offset())
    );
    assert_eq!(
        dwreg::offset(&Arch::AArch64, 64),
        Some(aarch64::vec_offset(0))
    );
    assert_eq!(dwreg::offset(&Arch::AArch64, 32), None);

    for arch in [Arch::X86_64, Arch::AArch64, Arch::X86] {
        assert!(dwreg::known(&arch));
        for n in 0..96u16 {
            if let Some(offset) = dwreg::offset(&arch, n) {
                assert_eq!(
                    dwreg::number(&arch, offset),
                    Some(n),
                    "{arch:?} register {n}"
                );
            }
        }
    }
    assert!(!dwreg::known(&Arch::Unknown(0)));
}
