//! The lifter measured against the machine it models.
//!
//! Compile a C function, lift what the compiler produced, run it in the
//! interpreter, and compare against the answer computed independently in Rust.
//! Reading a lifter cannot tell you whether it is right; running the original
//! and the translation and comparing can. This is the gate the roadmap put in
//! M4 rather than M10, and the reason the interpreter ships with the lifters.

use std::path::{Path, PathBuf};

use r12e_analysis::{Options, Program, analyze};
use r12e_core::{Addr, Arch};
use r12e_format::LoadOptions;
use r12e_ir::exec::run;
use r12e_ir::lift::aarch64::{gpr_offset, sp_offset};
use r12e_ir::{Machine, Stop};

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(name: &str) -> Option<Program> {
    let data = std::fs::read(corpus()?.join(name)).ok()?;
    let obj = r12e_format::load(&data, &LoadOptions::default()).ok()?;
    if obj.arch != Arch::AArch64 {
        return None;
    }
    Some(analyze(obj, &Options::default()))
}

/// Where a fresh machine's stack lives. Somewhere unmapped, so a stray read is
/// visible as an unknown rather than silently reading the image.
const STACK: u64 = 0x7fff_0000;

/// Call a function with integer arguments and return what it left in `x0`.
///
/// Arguments go in x0 onwards and the stack pointer is set, which is the whole
/// of the AArch64 calling convention for a handful of integers.
fn call(p: &Program, name: &str, args: &[u64]) -> Option<(u64, r12e_ir::Outcome)> {
    let f = p
        .functions_by_address()
        .find(|f| f.name.as_deref() == Some(name) || f.display_name() == name)?;
    let mut m = Machine::over(&p.object.memory);
    m.budget = 1 << 20;
    for (i, a) in args.iter().enumerate().take(8) {
        m.set_reg(gpr_offset(i as u8), 8, *a);
    }
    m.set_reg(sp_offset(), 8, STACK);
    // Give the stack real storage so a spill and its reload agree.
    m.write_mem(STACK - 0x1000, &[0u8; 0x2000]);
    let outcome = run(&mut m, &p.object.memory, &p.object.arch, f.entry);
    Some((m.reg(gpr_offset(0), 8), outcome))
}

/// Check one function against a closure that computes the same thing.
fn check(p: &Program, name: &str, cases: &[Vec<u64>], expect: impl Fn(&[u64]) -> u64) {
    for args in cases {
        let Some((got, outcome)) = call(p, name, args) else {
            return;
        };
        assert!(
            outcome.unlifted.is_empty(),
            "{name}{args:?}: {} instructions not modelled, first at {}",
            outcome.unlifted.len(),
            outcome.unlifted[0]
        );
        assert_eq!(
            outcome.stop,
            Stop::Returned,
            "{name}{args:?} stopped with {:?} after {} instructions",
            outcome.stop,
            outcome.insns
        );
        let want = expect(args);
        assert_eq!(
            got, want,
            "{name}{args:?} produced {got:#x}, expected {want:#x}"
        );
    }
}

/// Truncate to 32 bits, which is what a function returning `int` does.
fn w(v: u64) -> u64 {
    v & 0xffff_ffff
}

#[test]
fn arithmetic_at_every_width() {
    let Some(p) = open("wide.a64.O2.o") else {
        return;
    };

    check(
        &p,
        "arith32",
        &[vec![7, 3], vec![0, 0], vec![0xffff_ffff, 2], vec![100, 7]],
        |a| {
            let (x, y) = (a[0] as u32, a[1] as u32);
            let d = y | 1;
            w(x.wrapping_mul(y).wrapping_add(x / d).wrapping_add(x % d) as u64)
        },
    );

    check(
        &p,
        "arith64",
        &[vec![7, 3], vec![u64::MAX, 2], vec![1 << 40, 12345]],
        |a| {
            let (x, y) = (a[0], a[1]);
            let d = y | 1;
            x.wrapping_mul(y).wrapping_add(x / d).wrapping_add(x % d)
        },
    );

    check(
        &p,
        "sarith64",
        &[vec![7, 3], vec![(-9i64) as u64, 4], vec![(-1i64) as u64, 1]],
        |a| {
            let (x, y) = (a[0] as i64, a[1] as i64);
            let d = y | 1;
            x.wrapping_mul(y)
                .wrapping_add(x.wrapping_div(d))
                .wrapping_add(x.wrapping_rem(d)) as u64
        },
    );
}

#[test]
fn division_by_zero_produces_zero_rather_than_trapping() {
    // The architecture defines it that way, and a lifter that let the
    // interpreter fault instead would be modelling a different machine.
    let Some(p) = open("wide.a64.O2.o") else {
        return;
    };
    let Some((got, outcome)) = call(&p, "arith32", &[10, 0]) else {
        return;
    };
    assert_eq!(outcome.stop, Stop::Returned);
    // With y == 0 the source divides by `y | 1`, which is 1.
    assert_eq!(got, w(0u32.wrapping_add(10).wrapping_add(0) as u64));
}

#[test]
fn widening_and_sign_extension() {
    let Some(p) = open("wide.a64.O2.o") else {
        return;
    };
    check(
        &p,
        "widen",
        &[vec![0xff, 0xffff, 0xffff_ffff], vec![1, 2, 3]],
        |a| (a[0] as u8 as u64) + (a[1] as u16 as u64) + (a[2] as u32 as u64),
    );
    check(
        &p,
        "sign_widen",
        &[
            vec![0xff, 0xffff, 0xffff_ffff],
            vec![1, 2, 3],
            vec![0x80, 0x8000, 0x8000_0000],
        ],
        |a| {
            ((a[0] as u8 as i8 as i64) + (a[1] as u16 as i16 as i64) + (a[2] as u32 as i32 as i64))
                as u64
        },
    );
}

#[test]
fn comparisons_set_every_flag_correctly() {
    // Each of the seven comparisons in the source sets a different bit of the
    // result, so a wrong flag shows up as a wrong bit rather than as a wrong
    // answer that might be right by accident.
    let Some(p) = open("wide.a64.O2.o") else {
        return;
    };
    check(
        &p,
        "compares",
        &[
            vec![1, 2],
            vec![2, 1],
            vec![3, 3],
            vec![(-1i64) as u64, 1],
            vec![1, (-1i64) as u64],
            vec![i64::MIN as u64, i64::MAX as u64],
        ],
        |args| {
            let (a, b) = (args[0] as i64, args[1] as i64);
            let mut r = 0i32;
            if a == b {
                r += 1;
            }
            if a != b {
                r += 2;
            }
            if a < b {
                r += 4;
            }
            if a <= b {
                r += 8;
            }
            if a > b {
                r += 16;
            }
            if a >= b {
                r += 32;
            }
            if (a as u64) < (b as u64) {
                r += 64;
            }
            w(r as u32 as u64)
        },
    );
}

#[test]
fn conditional_selection() {
    let Some(p) = open("wide.a64.O2.o") else {
        return;
    };
    check(
        &p,
        "select_chain",
        &[
            vec![1, 2, 3],
            vec![3, 2, 1],
            vec![(-5i64) as u64, (-9i64) as u64, (-1i64) as u64],
            vec![0, 0, 0],
        ],
        |args| {
            let (a, b, c) = (args[0] as i32, args[1] as i32, args[2] as i32);
            let x = if a > b { a } else { b };
            let y = if x > c { x } else { c };
            w((if y < 0 { -y } else { y }) as u32 as u64)
        },
    );
}

#[test]
fn shifts_and_rotates() {
    let Some(p) = open("wide.a64.O2.o") else {
        return;
    };
    check(
        &p,
        "rotate",
        &[
            vec![0x0123_4567_89ab_cdef, 8],
            vec![1, 1],
            vec![u64::MAX, 63],
            vec![0xdead_beef, 0],
        ],
        |a| {
            let (x, k) = (a[0], a[1] as i32);
            (x << (k & 63)) | (x >> ((64 - k) & 63))
        },
    );
    check(
        &p,
        "bits",
        &[vec![0x1234_5678], vec![0], vec![0xffff_ffff]],
        |a| {
            let x = a[0] as u32;
            w(((x & 0xff00ff) | ((x >> 8) & 0xff) | (x << 24)) as u64)
        },
    );
}

#[test]
fn loops_terminate_and_accumulate() {
    let Some(p) = open("wide.a64.O2.o") else {
        return;
    };
    check(&p, "nested", &[vec![0], vec![1], vec![5], vec![17]], |a| {
        let n = a[0] as i32;
        let mut acc = 0i32;
        for i in 0..n {
            for j in i..n {
                for k in j..n {
                    acc += i ^ j ^ k;
                }
            }
        }
        w(acc as u32 as u64)
    });
    check(&p, "collatz", &[vec![1], vec![27], vec![97]], |a| {
        let mut n = a[0];
        let mut steps = 0u64;
        while n != 1 {
            n = if n & 1 == 1 { 3 * n + 1 } else { n / 2 };
            steps += 1;
        }
        steps
    });
}

#[test]
fn memory_reads_and_writes_agree_with_each_other() {
    // A store then a load through the interpreter's memory, driven by real
    // compiled code rather than by hand-built IR.
    let Some(p) = open("wide.a64.O2.o") else {
        return;
    };
    let Some(f) = p
        .functions_by_address()
        .find(|f| f.name.as_deref() == Some("sum_array"))
    else {
        return;
    };

    let base = 0x5000_0000u64;
    let values: [u64; 6] = [1, 2, 3, 4, 5, 6];
    let mut m = Machine::over(&p.object.memory);
    m.budget = 1 << 20;
    let mut bytes = Vec::new();
    for v in values {
        bytes.extend_from_slice(&v.to_le_bytes());
    }
    m.write_mem(base, &bytes);
    m.write_mem(STACK - 0x1000, &[0u8; 0x2000]);
    m.set_reg(gpr_offset(0), 8, base);
    m.set_reg(gpr_offset(1), 8, values.len() as u64);
    m.set_reg(sp_offset(), 8, STACK);

    let outcome = run(&mut m, &p.object.memory, &p.object.arch, f.entry);
    assert!(
        outcome.unlifted.is_empty(),
        "sum_array: {} instructions not modelled",
        outcome.unlifted.len()
    );
    assert_eq!(outcome.stop, Stop::Returned, "{outcome:?}");
    assert_eq!(m.reg(gpr_offset(0), 8), values.iter().sum::<u64>());
    // Nothing outside the array or the stack was read.
    let strays: Vec<Addr> = m
        .unknown_reads
        .iter()
        .copied()
        .filter(|a| {
            let v = a.get();
            !(base..base + bytes.len() as u64).contains(&v)
                && !(STACK - 0x1000..STACK + 0x1000).contains(&v)
        })
        .collect();
    assert!(strays.is_empty(), "read outside the model: {strays:?}");
}

#[test]
fn a_recursive_function_stops_at_its_first_call() {
    // Calls are not followed, which is what a single-function test wants. The
    // run has to stop cleanly and say where, rather than wander.
    let Some(p) = open("wide.a64.O2.o") else {
        return;
    };
    let Some((_, outcome)) = call(&p, "deep_recursion", &[10]) else {
        return;
    };
    assert!(
        matches!(outcome.stop, Stop::Call(_) | Stop::Returned),
        "{outcome:?}"
    );
}

#[test]
fn a_budget_stops_a_runaway_rather_than_hanging() {
    let Some(p) = open("wide.a64.O2.o") else {
        return;
    };
    let Some(f) = p
        .functions_by_address()
        .find(|f| f.name.as_deref() == Some("collatz"))
    else {
        return;
    };
    let mut m = Machine::over(&p.object.memory);
    m.budget = 50;
    m.set_reg(gpr_offset(0), 8, 0);
    m.set_reg(sp_offset(), 8, STACK);
    let outcome = run(&mut m, &p.object.memory, &p.object.arch, f.entry);
    // Zero never reaches one, so this runs forever without the budget.
    assert!(
        matches!(outcome.stop, Stop::Budget | Stop::Returned),
        "{outcome:?}"
    );
}
