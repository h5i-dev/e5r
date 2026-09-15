//! Reciprocal division and remainder, recovered and checked.
//!
//! A compiler never divides by a constant: it multiplies by a fixed point
//! reciprocal and shifts, and only the magic number survives into the machine
//! code. `opt::divisions` recovers the divisor from it, and a divisor that is
//! wrong by one is a program that is silently wrong. So the recovery is tested
//! two ways that do not share an argument: against the true quotient at every
//! dividend of a narrow width, which says the closed form verifier is right,
//! and against the magic numbers an independent implementation of Granlund and
//! Montgomery's algorithm produces for a thousand divisors, which says the
//! recovery finds the divisor a compiler actually meant.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use e5r_analysis::{Options, Program, analyze};
use e5r_core::Addr;
use e5r_format::LoadOptions;
use e5r_ir::op::Op;
use e5r_ir::opt::{signed_divisor, unsigned_divisor};
use e5r_ir::ssa::{SsaFunction, SsaKind};
use e5r_ir::{func, opt, ssa, stack};

/// The unsigned magic number, its shift, and whether the sequence needs the
/// dividend added back, for a 32-bit divisor.
///
/// Hacker's Delight figure 10-3, which is Granlund and Montgomery's algorithm
/// written out. It is here rather than called into the crate on purpose: a test
/// that generated its inputs with the code under test would only say the code
/// agrees with itself.
fn magicu(d: u32) -> (u32, bool, u32) {
    assert!(d >= 3);
    let nc = u32::MAX - (0u32.wrapping_sub(d) % d);
    let mut add = false;
    let (mut p, mut q1, mut r1) = (31u32, 0x8000_0000u32 / nc, 0x8000_0000u32 % nc);
    let (mut q2, mut r2) = (0x7fff_ffffu32 / d, 0x7fff_ffffu32 % d);
    loop {
        p += 1;
        if r1 >= nc - r1 {
            q1 = 2 * q1 + 1;
            r1 = 2 * r1 - nc;
        } else {
            q1 *= 2;
            r1 *= 2;
        }
        if r2 + 1 >= d - r2 {
            add |= q2 >= 0x7fff_ffff;
            q2 = 2 * q2 + 1;
            r2 = 2 * r2 + 1 - d;
        } else {
            add |= q2 >= 0x8000_0000;
            q2 *= 2;
            r2 = 2 * r2 + 1;
        }
        let delta = d - 1 - r2;
        if p >= 64 || !(q1 < delta || (q1 == delta && r1 == 0)) {
            break;
        }
    }
    (q2 + 1, add, p - 32)
}

/// The signed magic number and its shift, for a 32-bit divisor.
///
/// Hacker's Delight figure 10-1. The multiplier comes back as an unsigned
/// pattern: when a compiler stores a reciprocal that does not fit in a signed
/// word it keeps the low half and adds the dividend back, and the exact
/// multiplier that sequence computes with is the pattern read unsigned.
fn magics(d: u32) -> (u32, u32) {
    assert!(d >= 3);
    let two31: u32 = 0x8000_0000;
    let ad = d;
    let t = two31 - 1;
    let anc = t - 1 - t % ad;
    let (mut p, mut q1, mut r1) = (31u32, two31 / anc, two31 % anc);
    let (mut q2, mut r2) = (two31 / ad, two31 % ad);
    loop {
        p += 1;
        q1 *= 2;
        r1 *= 2;
        if r1 >= anc {
            q1 += 1;
            r1 -= anc;
        }
        q2 *= 2;
        r2 *= 2;
        if r2 >= ad {
            q2 += 1;
            r2 -= ad;
        }
        let delta = ad - r2;
        if q1 >= delta || (q1 == delta && r1 == 0) {
            break;
        }
    }
    (q2.wrapping_add(1), p - 32)
}

/// Every divisor a compiler would turn into a reciprocal comes back as itself.
///
/// Three to a thousand rather than the seven the fixture happens to contain:
/// the recovery is arithmetic, so the cost of checking a thousand of them is
/// nothing and a divisor it is wrong about would otherwise wait for a fixture
/// that names it.
#[test]
fn every_unsigned_divisor_to_a_thousand_is_recovered() {
    for d in 3u32..=1000 {
        let (magic, add, s) = magicu(d);
        // Without the add the sequence is one multiply and one shift. With it
        // the reciprocal needed a bit more than the multiply holds, and the
        // dividend comes back in a halving add, so the exact multiplier is the
        // stored one plus the bit that did not fit.
        let (m, shift) = match add {
            false => (magic as u64, 32 + s),
            true => (magic as u64 + (1u64 << 32), 32 + s),
        };
        assert_eq!(
            unsigned_divisor(m, shift, u32::MAX as u64),
            Some(d as u64),
            "u32 / {d}: magic {magic:#x}, add {add}, shift {shift}"
        );
    }
}

/// The same for the signed sequence.
#[test]
fn every_signed_divisor_to_a_thousand_is_recovered() {
    for d in 3u32..=1000 {
        let (magic, s) = magics(d);
        assert_eq!(
            signed_divisor(magic as u64, 32 + s, 32),
            Some(d as u64),
            "i32 / {d}: magic {magic:#x}, shift {}",
            32 + s
        );
    }
}

/// An ordinary shift stays a shift.
///
/// `x / 8` on an unsigned value is one shift and no reciprocal, and printing it
/// as a division would bury whatever bit manipulation the code is really doing.
/// Nothing without a multiply in front of it is a candidate: a multiplier of
/// one is refused outright, and the fixture's plain shift keeps its shape.
#[test]
fn a_plain_shift_is_not_read_as_a_division() {
    for shift in 1u32..64 {
        assert_eq!(unsigned_divisor(1, shift, u32::MAX as u64), None);
        assert_eq!(unsigned_divisor(0, shift, u32::MAX as u64), None);
    }
    for build in arith_builds() {
        let Some(p) = open(&build) else { continue };
        let Some(s) = optimized(&p, "divu8") else {
            panic!("divu8: not recovered from {build}");
        };
        let found = quotients(&s);
        assert!(
            found.is_empty(),
            "divu8 in {build}: a shift was read as a division: {found:?}"
        );
    }
}

/// Whatever the recovery returns really is the quotient, at every dividend.
///
/// The verifier inside `unsigned_divisor` evaluates a handful of points and
/// argues that the rest cannot be worse. That argument is what is checked here,
/// by running the sequence on all 65,536 dividends of a sixteen-bit range for a
/// wide sweep of multipliers and shifts, valid ones and deliberately broken
/// ones alike. A magic it accepts must agree everywhere; one it refuses costs
/// only an unfolded multiply.
#[test]
fn an_accepted_divisor_agrees_at_every_dividend() {
    const MAX: u64 = u16::MAX as u64;
    let mut accepted = 0usize;
    for d in 3u64..=600 {
        for shift in 16u32..=34 {
            let exact = (1u128 << shift).div_ceil(d as u128);
            // The reciprocal itself, and its neighbours, which are the wrong
            // answers a formula that did not check would hand back.
            for delta in [-2i128, -1, 0, 1, 2] {
                let Some(m) = (exact as i128).checked_add(delta) else {
                    continue;
                };
                if m <= 1 || m > u64::MAX as i128 {
                    continue;
                }
                let Some(found) = unsigned_divisor(m as u64, shift, MAX) else {
                    continue;
                };
                accepted += 1;
                for x in 0..=MAX {
                    let got = ((x as u128 * m as u128) >> shift) as u64;
                    assert_eq!(
                        got,
                        x / found,
                        "magic {m:#x} shift {shift} was read as / {found}, but at {x} the \
                         sequence gives {got} and the division gives {}",
                        x / found
                    );
                }
            }
        }
    }
    assert!(accepted > 1000, "only {accepted} magic(s) were accepted");
}

/// The signed recovery, checked the same way over a sixteen-bit range.
#[test]
fn an_accepted_signed_divisor_agrees_at_every_dividend() {
    let mut accepted = 0usize;
    for d in 3u64..=600 {
        for shift in 16u32..=34 {
            let exact = (1u128 << shift).div_ceil(d as u128);
            for delta in [-2i128, -1, 0, 1, 2] {
                let Some(m) = (exact as i128).checked_add(delta) else {
                    continue;
                };
                if m <= 1 || m > u64::MAX as i128 {
                    continue;
                }
                let Some(found) = signed_divisor(m as u64, shift, 16) else {
                    continue;
                };
                accepted += 1;
                for x in i16::MIN as i64..=i16::MAX as i64 {
                    let product = (x as i128 * m) >> shift;
                    let got = product + i128::from(x < 0);
                    assert_eq!(
                        got,
                        (x / found as i64) as i128,
                        "magic {m:#x} shift {shift} was read as / {found}, and disagrees at {x}"
                    );
                }
            }
        }
    }
    assert!(accepted > 500, "only {accepted} magic(s) were accepted");
}

fn corpus() -> Option<PathBuf> {
    let d = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fixtures/build");
    d.is_dir().then(|| d.canonicalize().unwrap())
}

fn open(name: &str) -> Option<Program> {
    let data = std::fs::read(corpus()?.join(name)).ok()?;
    let obj = e5r_format::load(&data, &LoadOptions::default()).ok()?;
    Some(analyze(obj, &Options::default()))
}

/// One function of a fixture, lifted and optimized the way the decompiler gets
/// it.
fn optimized(p: &Program, name: &str) -> Option<SsaFunction> {
    let f = p
        .functions_by_address()
        .find(|f| f.name.as_deref() == Some(name))?;
    let blocks: BTreeMap<Addr, (Addr, Vec<Addr>)> = f
        .cfg
        .blocks
        .iter()
        .map(|(a, b)| (*a, (b.range.end(), b.successors.clone())))
        .collect();
    let mut ir = func::build(&p.object.memory, &p.object.arch, f.entry, &blocks);
    stack::promote(&mut ir);
    let mut s = ssa::build(&ir);
    opt::optimize(&mut s);
    Some(s)
}

/// Every division or remainder in a function, as the operation and its divisor.
fn quotients(s: &SsaFunction) -> Vec<(Op, u64)> {
    let mut out = Vec::new();
    for b in s.blocks.values() {
        for op in &b.ops {
            let SsaKind::Op(o) = op.kind else { continue };
            if !matches!(o, Op::IntDiv | Op::IntSDiv | Op::IntRem | Op::IntSRem) {
                continue;
            }
            if let Some(d) = op.inputs.get(1).and_then(|i| i.as_const()) {
                out.push((o, d));
            }
        }
    }
    out
}

/// The builds of the arithmetic fixture that exist here.
///
/// A missing fixture skips rather than fails: the corpus is gitignored and a
/// fresh checkout has not run `scripts/build-fixtures.sh`.
fn arith_builds() -> Vec<String> {
    let mut out = Vec::new();
    for arch in ["x64", "a64"] {
        for level in ["O1", "O2"] {
            let name = format!("dt-arith.{arch}.{level}");
            if corpus().map(|d| d.join(&name).is_file()).unwrap_or(false) {
                out.push(name);
            }
        }
    }
    out
}

/// The reciprocal divisions in the fixture are divisions in the IR, on both
/// architectures and at both optimization levels.
#[test]
fn fixture_reciprocals_fold_to_divisions() {
    let cases: &[(&str, Op, u64)] = &[
        ("divu81", Op::IntDiv, 81),
        ("divu89", Op::IntDiv, 89),
        ("divu91", Op::IntDiv, 91),
        ("divu99", Op::IntDiv, 99),
        ("divu101", Op::IntDiv, 101),
        // 112 is 16 times 7, and the compiler shifts by four first, so the
        // division that is left in the code really is by seven.
        ("divu112", Op::IntDiv, 7),
        ("divu125", Op::IntDiv, 125),
        ("divs81", Op::IntSDiv, 81),
        ("divs99", Op::IntSDiv, 99),
        ("divs125", Op::IntSDiv, 125),
    ];
    for build in arith_builds() {
        let Some(p) = open(&build) else { continue };
        for (name, op, d) in cases {
            let Some(s) = optimized(&p, name) else {
                panic!("{name}: not recovered from {build}");
            };
            let found = quotients(&s);
            assert!(
                found.contains(&(*op, *d)),
                "{name} in {build}: expected {op:?} by {d}, found {found:?}"
            );
        }
    }
}

/// The remainder forms built on the same reciprocal fold too.
///
/// x86-64 is left out of this one: there the multiply back is an `lea`, whose
/// result the lifter writes as an eight-byte temporary and reads back as a
/// four-byte one, and the SSA builder does not connect those two, so the
/// subtraction reads storage nothing defined. That is a defect below this pass
/// and no algebra here can see past it.
#[test]
fn fixture_remainders_fold_to_remainders() {
    let cases: &[(&str, Op, u64)] = &[
        ("modu10", Op::IntRem, 10),
        ("modu100", Op::IntRem, 100),
        ("mods3", Op::IntSRem, 3),
        ("mods7", Op::IntSRem, 7),
        ("mods10", Op::IntSRem, 10),
    ];
    for build in arith_builds().into_iter().filter(|b| b.contains("a64")) {
        let Some(p) = open(&build) else { continue };
        for (name, op, d) in cases {
            let Some(s) = optimized(&p, name) else {
                panic!("{name}: not recovered from {build}");
            };
            let found = quotients(&s);
            assert!(
                found.contains(&(*op, *d)),
                "{name} in {build}: expected {op:?} by {d}, found {found:?}"
            );
        }
    }
}

/// Signed division by a power of two is a division, not a rounding correction.
#[test]
fn fixture_signed_power_of_two_folds() {
    for build in arith_builds().into_iter().filter(|b| b.contains("a64")) {
        let Some(p) = open(&build) else { continue };
        let Some(s) = optimized(&p, "divs8") else {
            panic!("divs8: not recovered from {build}");
        };
        let found = quotients(&s);
        assert!(
            found.contains(&(Op::IntSDiv, 8)),
            "divs8 in {build}: expected a signed division by 8, found {found:?}"
        );
    }
}

/// The power of two identities the pattern rules stand on, at every dividend
/// of a sixteen-bit range.
///
/// These rules read a divisor straight off a mask or a shift, so there is no
/// magic number to recover and nothing for the reciprocal verifier to check.
/// What is left to be wrong is the algebra, and the algebra is small enough to
/// check by exhaustion: if any of these three identities failed, the rule built
/// on it would be emitting a division that is not the division the machine
/// computes.
#[test]
fn the_power_of_two_identities_hold() {
    for x in i16::MIN..=i16::MAX {
        let v = x as i32;
        // `x < 0 ? -(x & 1) : (x & 1)` is `x % 2`.
        let low = v & 1;
        let chosen = if v < 0 { -low } else { low };
        assert_eq!(chosen, v % 2, "low bit remainder at {x}");
        for k in 1u32..16 {
            // The bias a compiler adds so a shift truncates toward zero: the
            // sign smeared across the whole width, then cut back to `k` bits.
            let sign = (v >> 15) as u32 & 0xffff;
            let bias = (sign >> (16 - k)) as i32;
            let biased = v + bias;
            assert_eq!(
                ((biased << 16) >> 16) >> k,
                v / (1 << k),
                "biased shift quotient at {x} by 2^{k}"
            );
            let masked = ((biased & !((1 << k) - 1)) << 16) >> 16;
            assert_eq!(v - masked, v % (1 << k), "masked remainder at {x} by 2^{k}");
        }
    }
}

/// The power of two idioms in the fixture come out as a division and a
/// remainder, on both architectures.
#[test]
fn fixture_power_of_two_idioms_fold() {
    for build in arith_builds() {
        let Some(p) = open(&build) else { continue };
        let Some(s) = optimized(&p, "mods2") else {
            panic!("mods2: not recovered from {build}");
        };
        let found = quotients(&s);
        assert!(
            found.contains(&(Op::IntSRem, 2)),
            "mods2 in {build}: expected a signed remainder by 2, found {found:?}"
        );
    }
}
