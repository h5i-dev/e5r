//! The gate on the loop this whole path exists for.
//!
//! An analyst looks at a decompilation, asserts a declaration, and looks
//! again. Before this, the assertion was stored and ignored: only `name` fed
//! back, so `annotate type` wrote a line the engine never read and 596 of
//! DecBench's 764 functions scored zero on type recovery because there was no
//! way to tell the tool anything about a type.
//!
//! The emitter is not reachable from this crate, so the gate is set where it
//! can be: assert a declaration, run prototype recovery, and check that the
//! resulting `Prototype` has the parameter count, widths, storage and return
//! type the declaration named, with the strength saying a person said so.
//!
//! Functions here are built by hand rather than lifted. What is under test is
//! the merge of an assertion with a recovery, and a hand-built function makes
//! the code's own answer exact instead of whatever a compiler happened to
//! emit.

use std::collections::BTreeMap;

use e5r_core::provenance::Strength;
use e5r_core::{Addr, Arch};
use e5r_ir::abi::{self, Abi};
use e5r_ir::op::{Op, Space};
use e5r_ir::proto::{self, Asserted, Conflict, Storage};
use e5r_ir::ssa::{Location, Operand, SsaBlock, SsaFunction, SsaKind, SsaOp, Value};

const ENTRY: Addr = Addr(0x1000);

fn reg(offset: u64) -> Location {
    Location {
        space: Space::Register,
        offset,
        size: 8,
    }
}

/// A function that reads `reads` argument registers and leaves a computed
/// value in the first result register.
fn function(abi: &Abi, reads: usize, leaves_result: bool) -> SsaFunction {
    let result = reg(abi.results[0]);
    let mut ops = Vec::new();
    for n in 0..reads {
        let version = n as u32 + 1;
        let source = Operand::Undefined(reg(abi.integer_arguments[n]));
        let inputs = if n == 0 {
            vec![source]
        } else {
            vec![
                Operand::Value(Value {
                    location: result,
                    version: version - 1,
                }),
                source,
            ]
        };
        ops.push(SsaOp {
            addr: ENTRY,
            kind: SsaKind::Op(if n == 0 { Op::Copy } else { Op::IntAdd }),
            out: Some(Value {
                location: result,
                version,
            }),
            inputs,
            size: 8,
        });
    }
    if !leaves_result {
        // Drop what was computed: a function with no result writes the
        // register on the way through and leaves nothing that reaches a
        // return.
        ops.clear();
    }
    ops.push(SsaOp {
        addr: ENTRY,
        kind: SsaKind::Op(Op::Return),
        out: None,
        inputs: Vec::new(),
        size: 8,
    });
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
        arch: Arch::X86_64,
        entry: ENTRY,
        blocks,
    }
}

#[test]
fn an_asserted_declaration_decides_the_parameters_and_says_who_decided() {
    let abi = abi::of(&Arch::X86_64);
    // The code reads four argument registers, which is what recovery sees.
    let f = function(&abi, 4, true);
    let machine = proto::recover(&f, &abi);
    assert_eq!(machine.integer_arguments, 4);
    assert_eq!(machine.origin.arguments, Strength::Inferred);
    assert!(machine.parameters.is_empty());

    let asserted = Asserted::parse(
        "int arith8(unsigned char a, unsigned char b)",
        &Arch::X86_64,
    )
    .expect("a declaration an analyst would type");
    let p = proto::recover_with(&f, &abi, Some(&asserted));

    // The count, the widths, the storage and the return type are the ones the
    // declaration named.
    assert_eq!(p.name.as_deref(), Some("arith8"));
    assert_eq!(p.parameters.len(), 2);
    assert_eq!(p.integer_arguments, 2);
    assert_eq!(p.float_arguments, 0);
    assert!(p.stack_arguments.is_empty());
    for (n, param) in p.parameters.iter().enumerate() {
        assert_eq!(param.size, 1, "an unsigned char is one byte");
        assert_eq!(param.storage, vec![Storage::Integer(n)]);
        assert_eq!(param.strength, Strength::Asserted);
    }
    assert_eq!(p.parameters[0].name.as_deref(), Some("a"));
    assert_eq!(p.parameters[1].name.as_deref(), Some("b"));
    assert_eq!(p.returns, Some(abi.results[0]));
    assert!(!p.returns_float);
    assert_eq!(asserted.types.size_of(p.return_type.unwrap()), Some(4));

    // And the output can say that a person is why it changed.
    assert_eq!(p.origin.arguments, Strength::Asserted);
    assert_eq!(p.origin.returns, Strength::Asserted);
    assert!(p.is_asserted());
    assert!(Strength::Asserted > Strength::Proven);
}

#[test]
fn a_declaration_that_contradicts_the_machine_wins_and_the_reads_are_kept() {
    let abi = abi::of(&Arch::X86_64);
    let f = function(&abi, 4, true);
    let asserted = Asserted::parse("int three(int a, int b, int c)", &Arch::X86_64).unwrap();
    let p = proto::recover_with(&f, &abi, Some(&asserted));

    assert_eq!(p.integer_arguments, 3, "the declaration is honoured");
    // The fourth read is not silently dropped: it is a recorded conflict and
    // the machine's own answer is still there to look at.
    assert_eq!(
        p.conflicts,
        vec![Conflict::ExtraArgument {
            register: abi.integer_arguments[3],
            slot: 3,
        }]
    );
    let recovered = p.recovered.as_ref().expect("what the code said");
    assert_eq!(recovered.integer_arguments, 4);
    assert_eq!(recovered.origin.arguments, Strength::Inferred);
    assert!(format!("{}", p.conflicts[0]).contains("does not name"));
}

#[test]
fn a_declaration_that_names_more_than_the_code_reads_says_so() {
    let abi = abi::of(&Arch::X86_64);
    let f = function(&abi, 1, true);
    let asserted = Asserted::parse("int f(int a, int b, int c)", &Arch::X86_64).unwrap();
    let p = proto::recover_with(&f, &abi, Some(&asserted));
    assert_eq!(p.integer_arguments, 3);
    assert!(p.conflicts.contains(&Conflict::UnreadArgument { index: 1 }));
    assert!(p.conflicts.contains(&Conflict::UnreadArgument { index: 2 }));
    assert!(!p.conflicts.contains(&Conflict::UnreadArgument { index: 0 }));
}

#[test]
fn a_void_declaration_over_a_function_that_leaves_a_value_is_a_conflict() {
    let abi = abi::of(&Arch::X86_64);
    let f = function(&abi, 1, true);
    let asserted = Asserted::parse("void f(int a)", &Arch::X86_64).unwrap();
    let p = proto::recover_with(&f, &abi, Some(&asserted));
    assert_eq!(p.returns, None);
    assert_eq!(p.return_type, None);
    assert_eq!(
        p.conflicts,
        vec![Conflict::ResultDiscarded {
            register: abi.results[0]
        }]
    );

    // And the other direction.
    let f = function(&abi, 1, false);
    let asserted = Asserted::parse("int f(int a)", &Arch::X86_64).unwrap();
    let p = proto::recover_with(&f, &abi, Some(&asserted));
    assert_eq!(p.returns, Some(abi.results[0]));
    assert!(p.conflicts.contains(&Conflict::ResultMissing));
}

#[test]
fn floating_point_parameters_and_results_go_to_the_vector_registers() {
    let abi = abi::of(&Arch::X86_64);
    let f = function(&abi, 1, true);
    let asserted =
        Asserted::parse("double scale(double x, int n, float y)", &Arch::X86_64).unwrap();
    let p = proto::recover_with(&f, &abi, Some(&asserted));
    assert_eq!(p.parameters[0].storage, vec![Storage::Float(0)]);
    assert_eq!(p.parameters[1].storage, vec![Storage::Integer(0)]);
    assert_eq!(p.parameters[2].storage, vec![Storage::Float(1)]);
    assert_eq!(p.float_arguments, 2);
    assert_eq!(p.integer_arguments, 1);
    assert!(p.returns_float);
    assert!(p.returns.unwrap() >= abi.vector_base);
}

#[test]
fn arguments_past_the_registers_land_on_the_stack_in_order() {
    let abi = abi::of(&Arch::X86_64);
    let f = function(&abi, 6, true);
    let asserted = Asserted::parse(
        "int many(int a, int b, int c, int d, int e, int f, int g, int h)",
        &Arch::X86_64,
    )
    .unwrap();
    let p = proto::recover_with(&f, &abi, Some(&asserted));
    assert_eq!(p.integer_arguments, 6, "System V has six of them");
    // x86 pushes the return address, so the first stack argument is one slot
    // past the entry pointer.
    assert_eq!(p.parameters[6].storage, vec![Storage::Stack(8)]);
    assert_eq!(p.parameters[7].storage, vec![Storage::Stack(16)]);
    assert_eq!(p.stack_arguments, vec![8, 16]);
}

#[test]
fn a_result_too_large_for_the_registers_takes_the_first_one_as_its_address() {
    let abi = abi::of(&Arch::X86_64);
    let f = function(&abi, 2, true);
    let asserted = Asserted::parse(
        "struct big { long a; long b; long c; } make(int n)",
        &Arch::X86_64,
    )
    .unwrap();
    let p = proto::recover_with(&f, &abi, Some(&asserted));
    // The hidden pointer shifts every declared parameter by one register,
    // which is the kind of thing that makes a decompilation wrong everywhere
    // if it is missed.
    assert_eq!(p.parameters[0].storage, vec![Storage::Integer(1)]);
    assert_eq!(p.integer_arguments, 2);

    // A structure that does fit is passed in the registers themselves.
    let asserted = Asserted::parse(
        "int take(struct pair { int a; int b; } p, int n)",
        &Arch::X86_64,
    )
    .unwrap();
    let p = proto::recover_with(&f, &abi, Some(&asserted));
    assert_eq!(p.parameters[0].storage, vec![Storage::Integer(0)]);
    assert_eq!(p.parameters[1].storage, vec![Storage::Integer(1)]);
}

#[test]
fn a_declaration_the_convention_cannot_satisfy_is_reported_and_not_a_crash() {
    let mut abi = abi::of(&Arch::X86_64);
    // A soft-float convention: the registers exist and arguments never go in
    // them. Declaring a double is then a real disagreement with the ABI.
    abi.float_arguments.clear();
    abi.results.retain(|r| *r < abi.vector_base);
    let f = function(&abi, 1, true);
    let asserted = Asserted::parse("double f(double x)", &Arch::X86_64).unwrap();
    let p = proto::recover_with(&f, &abi, Some(&asserted));

    assert!(
        p.conflicts
            .iter()
            .any(|c| matches!(c, Conflict::OffConvention { index: Some(0), .. })),
        "{:?}",
        p.conflicts
    );
    assert!(
        p.conflicts
            .iter()
            .any(|c| matches!(c, Conflict::OffConvention { index: None, .. })),
        "{:?}",
        p.conflicts
    );
    // It still produced an answer: the parameter went where it could.
    assert_eq!(p.parameters[0].storage, vec![Storage::Stack(8)]);
}

#[test]
fn a_varargs_declaration_is_recorded_as_one() {
    let abi = abi::of(&Arch::X86_64);
    let f = function(&abi, 2, true);
    let asserted = Asserted::parse("int printf(const char *fmt, ...)", &Arch::X86_64).unwrap();
    let p = proto::recover_with(&f, &abi, Some(&asserted));
    assert!(p.varargs);
    assert_eq!(p.origin.varargs, Strength::Asserted);
    assert_eq!(p.integer_arguments, 1);
}

#[test]
fn no_assertion_leaves_recovery_exactly_as_it_was() {
    let abi = abi::of(&Arch::X86_64);
    let f = function(&abi, 3, true);
    assert_eq!(
        proto::recover_with(&f, &abi, None),
        proto::recover(&f, &abi)
    );
    let p = proto::recover(&f, &abi);
    assert!(!p.is_asserted());
    assert!(p.recovered.is_none());
    assert_eq!(p.arity(), 3);
}

#[test]
fn the_type_model_follows_the_architecture() {
    // The same declaration is a different prototype on a 32-bit target,
    // because a `long` is not the same width there.
    let lp64 = Asserted::parse("int f(long x)", &Arch::X86_64).unwrap();
    assert_eq!(lp64.types.size_of(lp64.signature.parameters[0].1), Some(8));
    let ilp32 = Asserted::parse("int f(long x)", &Arch::X86).unwrap();
    assert_eq!(
        ilp32.types.size_of(ilp32.signature.parameters[0].1),
        Some(4)
    );
}

#[test]
fn a_declaration_that_is_not_a_function_is_refused_rather_than_believed() {
    assert!(Asserted::parse("int x", &Arch::X86_64).is_err());
    assert!(Asserted::parse("struct widget *p", &Arch::X86_64).is_err());
    let e = Asserted::parse("int f(frobnicate x)", &Arch::X86_64).unwrap_err();
    assert!(e.message.contains("frobnicate"), "{}", e.message);
}
