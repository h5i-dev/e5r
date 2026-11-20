//! Conformance levels and the frame rules (docs/isa/v1.md): the committed
//! examples reach L2, and the v1 negative controls (criterion 6, checker
//! side) each drop `sum2` below L2 with the rule that names the fault, with
//! the partition declared (as recorded) and with it inferred.

use nocompiler::frame::Partition;
use nocompiler::profile::{self, Func, Level};

const SUM_ELF: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../../examples/elf/sum.elf");

fn sum2_and_entries() -> (
    Func,
    Vec<profile::Node>,
    Partition,
    std::collections::BTreeSet<u64>,
) {
    let bytes = std::fs::read(SUM_ELF).unwrap();
    let bin = nocompiler::load(&bytes).unwrap();
    let entries = bin.entries();
    let f = bin.funcs.iter().find(|f| f.name == "sum2").unwrap().clone();
    let c = profile::check_with(
        &f,
        &profile::recover(&f, &entries).unwrap(),
        None,
        None,
        &entries,
    )
    .unwrap();
    assert_eq!(c.meta.level, Level::L2, "{:?}", c.missed);
    let part = Partition {
        slots: c.meta.slots.clone(),
        ranges: c.meta.ranges.clone(),
    };
    (f, c.meta.nodes, part, entries)
}

/// The level and rules of `sum2` with the word at `addr` replaced.
fn mutant(addr: u64, word: u32, declared: bool) -> (Option<Level>, Vec<String>) {
    let (mut f, nodes, part, entries) = sum2_and_entries();
    let i = ((addr - f.entry) / 4) as usize;
    f.words[i] = word;
    let p = declared.then_some(&part);
    match profile::check_with(&f, &nodes, p, None, &entries) {
        Ok(c) => (
            Some(c.meta.level),
            c.missed
                .iter()
                .map(|v| format!("[{}] {}", v.rule, v.detail))
                .collect(),
        ),
        Err(e) => (
            e.level,
            e.violations
                .iter()
                .map(|v| format!("[{}] {}", v.rule, v.detail))
                .collect(),
        ),
    }
}

fn assert_mutant(what: &str, addr: u64, word: u32, level: Option<Level>, rule: &str) {
    for declared in [true, false] {
        let (got, why) = mutant(addr, word, declared);
        assert_eq!(got, level, "{what} (declared {declared}): {why:?}");
        assert!(
            why.iter().any(|w| w.starts_with(&format!("[{rule}"))),
            "{what} (declared {declared}): expected [{rule}], got {why:?}"
        );
    }
}

// sum2 (examples/elf/sum.elf), as clang -O2 compiled it:
//   111b4 addi sp, sp, -32      111d8 mv s2, a0       111f4 ld s0, 16(sp)
//   111b8 sd ra, 24(sp)         111dc mv a0, s1       111f8 ld s1, 8(sp)
//   111bc sd s0, 16(sp)         111e0 mv a1, s0       111fc ld s2, 0(sp)
//   111c0 sd s1, 8(sp)          111e4 auipc ra, 0     11200 addi sp, sp, 32
//   111c4 sd s2, 0(sp)          111e8 jalr -84(ra)    11204 ret
//   111c8 mv s0, a3             111ec add a0, a0, s2
//   111cc mv s1, a2             111f0 ld ra, 24(sp)
//   111d0 auipc ra, 0 / 111d4 jalr -64(ra)

const NOP: u32 = 0x0000_0013;

fn sd(rs2: u32, off: u32) -> u32 {
    ((off >> 5) << 25) | (rs2 << 20) | (2 << 15) | (3 << 12) | ((off & 31) << 7) | 0x23
}
fn addi(rd: u32, rs1: u32, imm: u32) -> u32 {
    (imm << 20) | (rs1 << 15) | (rd << 7) | 0x13
}

#[test]
fn the_examples_reach_l2() {
    for elf in [
        "examples/elf/sum.elf",
        "examples/elf/hello.elf",
        "examples/demo/elf/sum.b.elf",
        "examples/demo/elf/cobs.b.elf",
    ] {
        let bytes = std::fs::read(format!("{}/../../{elf}", env!("CARGO_MANIFEST_DIR"))).unwrap();
        let bin = nocompiler::load(&bytes).unwrap();
        for r in bin.check() {
            assert_eq!(
                r.level,
                Some(Level::L2),
                "{elf} {}: {:?} {:?}",
                r.name,
                r.result.err(),
                r.missed
            );
        }
    }
}

#[test]
fn the_inferred_partition_of_sum2_is_the_specs() {
    let (_, _, part, _) = sum2_and_entries();
    let s: Vec<String> = part
        .slots
        .iter()
        .map(|s| match s.kind {
            profile::SlotKind::Save(r) => format!("slot {} save {r}", s.off),
            profile::SlotKind::Spill => format!("slot {} spill", s.off),
        })
        .collect();
    assert_eq!(
        s,
        [
            "slot 0 save s2",
            "slot 8 save s1",
            "slot 16 save s0",
            "slot 24 save ra"
        ]
    );
    assert!(part.ranges.is_empty());
}

#[test]
fn removing_a_restore_misses_l2() {
    assert_mutant(
        "ld s0, 16(sp) removed",
        0x111f4,
        NOP,
        Some(Level::L1),
        "R6e save",
    );
}

#[test]
fn writing_a_save_slot_mid_function_misses_l2() {
    assert_mutant(
        "mv s2, a0 -> sd a0, 16(sp)",
        0x111d8,
        sd(10, 16),
        Some(Level::L1),
        "R6",
    );
    // With the partition declared, the fault is named exactly.
    let (_, why) = mutant(0x111d8, sd(10, 16), true);
    assert!(
        why.iter().any(|w| w.contains("writes the save slot of s0")),
        "{why:?}"
    );
}

#[test]
fn taking_a_slots_address_misses_l2() {
    assert_mutant(
        "mv a0, s1 -> addi a0, sp, 16",
        0x111dc,
        addi(10, 2, 16),
        Some(Level::L1),
        "R6",
    );
    let (_, why) = mutant(0x111dc, addi(10, 2, 16), true);
    assert!(
        why.iter()
            .any(|w| w.starts_with("[R6d address]") && w.contains("slot at 16")),
        "{why:?}"
    );
}

#[test]
fn breaking_a_calls_distance_is_not_even_l1() {
    // jalr -64(ra) -> jalr -60(ra): the call no longer reaches an entry.
    let (f, ..) = sum2_and_entries();
    let w = f.words[((0x111d4 - f.entry) / 4) as usize];
    let w2 = (w & 0x000f_ffff) | (((-60i32 as u32) & 0xfff) << 20);
    assert_mutant(
        "call distance +4",
        0x111d4,
        w2,
        Some(Level::L0),
        "R2 control",
    );
}

#[test]
fn writing_gp_or_storing_sp_misses_l2() {
    // mv s0, a3 -> addi gp, a3, 0
    assert_mutant(
        "writes gp",
        0x111c8,
        addi(3, 13, 0),
        Some(Level::L1),
        "R4 registers",
    );
    // mv s2, a0 -> sd sp, 0(a0): sp's value to memory (6a)
    let w = (2 << 20) | (10 << 15) | (3 << 12) | 0x23;
    assert_mutant("stores sp", 0x111d8, w, Some(Level::L1), "R6a sp");
}

#[test]
fn reading_outside_the_frame_misses_l2() {
    // ld ra, 24(sp) -> ld ra, 40(sp): past the entry sp (a stack argument).
    let w = (40 << 20) | (2 << 15) | (3 << 12) | (1 << 7) | 0x03;
    let (lvl, why) = mutant(0x111f0, w, true);
    assert_eq!(lvl, Some(Level::L1));
    assert!(why.iter().any(|w| w.starts_with("[R6c")), "{why:?}");
}

#[test]
fn a_wrong_declared_partition_misses_l2_and_nothing_worse() {
    let (f, nodes, mut part, entries) = sum2_and_entries();
    part.slots.retain(|s| s.off != 16); // forget s0's save slot
    let c = profile::check_with(&f, &nodes, Some(&part), None, &entries).unwrap();
    assert_eq!(c.meta.level, Level::L1);
    assert!(c.missed.iter().any(|v| v.rule.starts_with("R6")));
}
