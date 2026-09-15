//! G3 for ARM: the decoder against llvm-objdump over a swept encoding space
//! rather than only over compiled code.
//!
//! A compiler emits a narrow slice of an instruction set. The fixtures this
//! repository builds are C compiled at four optimization levels, so they reach
//! the arithmetic, the loads and the branches and nothing else: no barriers, no
//! system register moves, no DSP instructions, no coprocessor forms. Every one
//! of those is in real code -- firmware is full of the first two -- and a
//! decoder measured only against fixtures says nothing about them.
//!
//! So the corpus here is generated rather than compiled. Both instruction sets
//! are swept structurally, group by group, with the fields that select a form
//! varied inside each: what is covered is the shape of the encoding space, not
//! a sample of one program's instructions.
//!
//! Each candidate sits at the start of its own eight-byte slot padded with
//! `nop`, so a candidate that turns out to be two bytes rather than four still
//! leaves the next one on a boundary and the two disassemblers cannot
//! desynchronize.

use std::collections::BTreeMap;
use std::process::Command;

use e5r_arch::arm::{self, ItState, Mode};
use e5r_core::Addr;

/// Bytes per candidate: twice the longest instruction either set has.
const SLOT: usize = 8;

/// The share of what llvm decodes that this decoder also decodes.
///
/// A ratchet: it only rises. What is left is listed by mnemonic by
/// `arm_sweep_report`, which is the work list.
const MIN_A32: f64 = 0.87;
const MIN_T32: f64 = 0.96;

fn tool(names: &[&'static str]) -> Option<&'static str> {
    names
        .iter()
        .copied()
        .find(|c| Command::new(c).arg("--version").output().is_ok())
}

/// Every A32 candidate.
///
/// The architecture splits the word by bits 27:25 and then by the fields each
/// group uses, so the sweep walks those fields rather than the whole 2^32:
/// every top-level group, every operation within it, and a few values of each
/// register and immediate field, which is what selects between forms.
fn a32_candidates() -> Vec<u32> {
    let mut out = Vec::new();
    // Condition `al` for most, plus one conditional pass so the condition
    // field is exercised without multiplying the whole sweep by sixteen.
    for cond in [0xeu32, 0x0, 0xb] {
        let c = cond << 28;
        // Data processing, immediate and register forms, with and without S.
        for op in 0..16u32 {
            for s in 0..2u32 {
                for imm in [0u32, 1] {
                    for rn in [0u32, 5, 13, 15] {
                        for rd in [0u32, 5, 15] {
                            out.push(
                                c | imm << 25 | op << 21 | s << 20 | rn << 16 | rd << 12 | 0x12,
                            );
                        }
                    }
                }
            }
        }
        // Loads and stores, every P/U/B/W/L combination.
        for bits in 0..64u32 {
            for rn in [0u32, 13, 15] {
                out.push(c | 0x4 << 24 | bits << 20 | rn << 16 | 0x3004);
                out.push(c | 0x6 << 24 | bits << 20 | rn << 16 | 0x3004);
            }
        }
        // Load and store multiple.
        for bits in 0..32u32 {
            out.push(c | 0x8 << 24 | bits << 20 | 13 << 16 | 0x4030);
        }
        // Multiplies and the synchronization primitives, which share a space.
        for op in 0..32u32 {
            out.push(c | op << 20 | 0x9 << 4 | 0x0302_0001);
        }
        // The halfword and signed loads, and the extra load/store space.
        for op in 0..32u32 {
            for kind in [0xbu32, 0xd, 0xf] {
                out.push(c | op << 20 | kind << 4 | 0x0030_0001);
            }
        }
        // Coprocessor: `cdp`, `mcr`/`mrc`, `stc`/`ldc`, which firmware and
        // anything with a floating point unit both use.
        for op in 0..16u32 {
            out.push(c | 0xe << 24 | op << 20 | 0x3105);
            out.push(c | 0xe << 24 | op << 20 | 0x3115);
            out.push(c | 0xc << 24 | op << 20 | 0x3105);
            out.push(c | 0xd << 24 | op << 20 | 0x3105);
        }
        // The miscellaneous space: `bx`, `clz`, `msr`, `mrs`, the saturating
        // arithmetic and the breakpoints.
        for op in 0..16u32 {
            for kind in 0..8u32 {
                out.push(c | 0x1 << 24 | op << 20 | kind << 4 | 0x0f0f);
            }
        }
        // Media: the packing, saturating, reversing and DSP forms.
        for op1 in 0..32u32 {
            for op2 in 0..8u32 {
                out.push(c | 0x3 << 25 | op1 << 20 | op2 << 5 | 0x1 << 4 | 0x0203_0f04);
            }
        }
    }
    // The unconditional space, which is a second instruction space and not a
    // condition: barriers, `pli`, `blx` and the SIMD loads.
    for op in 0..64u32 {
        out.push(0xf000_0000 | op << 20 | 0x0f00_0050);
        out.push(0xf000_0000 | op << 20 | 0x0507_f000);
    }
    out.sort_unstable();
    out.dedup();
    out
}

/// Every T32 candidate, as one or two halfwords.
fn t32_candidates() -> Vec<Vec<u8>> {
    let mut out: Vec<Vec<u8>> = Vec::new();
    // The sixteen-bit space, swept whole: it is only 65,536 encodings and it
    // is where the common instructions live.
    for w in (0u32..=0xffff).step_by(7) {
        out.push((w as u16).to_le_bytes().to_vec());
    }
    // The thirty-two bit space, by group. The first halfword's bits 12:11
    // select the group and 10:4 the operation within it.
    for hi_op in 0..128u32 {
        for group in [0b01u32, 0b10, 0b11] {
            for rn in [0u32, 3, 13, 15] {
                let hw1 = 0xe000 | group << 11 | hi_op << 4 | rn;
                for lo in [0x0000u32, 0x8000, 0xf000, 0x3104, 0x2f01] {
                    let mut b = (hw1 as u16).to_le_bytes().to_vec();
                    b.extend_from_slice(&(lo as u16).to_le_bytes());
                    out.push(b);
                }
            }
        }
    }
    // The system and barrier rows specifically, which the stride above can
    // step over: these are what firmware is made of.
    for op in 0..16u32 {
        for rn in [0u32, 3, 8, 15] {
            let hw1 = 0xf380 | rn;
            let hw2 = 0x8800 | op << 4 | op;
            let mut b = (hw1 as u16).to_le_bytes().to_vec();
            b.extend_from_slice(&(hw2 as u16).to_le_bytes());
            out.push(b);
            let mut b = 0xf3bfu16.to_le_bytes().to_vec();
            b.extend_from_slice(&((0x8f00 | op << 4 | op) as u16).to_le_bytes());
            out.push(b);
        }
    }
    // The DSP and coprocessor rows, for the same reason.
    for op in 0..64u32 {
        for op2 in 0..8u32 {
            let mut b = ((0xfa00 | op << 4 | 2) as u16).to_le_bytes().to_vec();
            b.extend_from_slice(&((0xf000 | op2 << 4 | 12) as u16).to_le_bytes());
            out.push(b);
        }
        let mut b = ((0xec00 | op) as u16).to_le_bytes().to_vec();
        b.extend_from_slice(&0x3105u16.to_le_bytes());
        out.push(b);
        let mut b = ((0xee00 | op) as u16).to_le_bytes().to_vec();
        b.extend_from_slice(&0x3115u16.to_le_bytes());
        out.push(b);
    }
    out.sort();
    out.dedup();
    out
}

/// What llvm makes of each slot, by slot index.
///
/// `None` where llvm itself declines, which is most of a swept space and is
/// not a gap in this decoder.
fn oracle(bytes: &[u8], thumb: bool) -> Option<BTreeMap<usize, String>> {
    let cc = tool(&["clang-18", "clang"])?;
    let objdump = tool(&["llvm-objdump-18", "llvm-objdump"])?;
    let dir = std::env::temp_dir().join(format!(
        "e5r-armsweep-{}-{}",
        if thumb { "t32" } else { "a32" },
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).ok()?;
    let src = dir.join("s.s");
    let obj = dir.join("s.o");
    let mut text = String::from(if thumb {
        ".text\n.thumb\n.syntax unified\n"
    } else {
        ".text\n.arm\n"
    });
    for chunk in bytes.chunks(16) {
        text.push_str(".byte ");
        for (n, b) in chunk.iter().enumerate() {
            if n > 0 {
                text.push(',');
            }
            text.push_str(&format!("{b:#04x}"));
        }
        text.push('\n');
    }
    std::fs::write(&src, text).ok()?;
    let built = Command::new(cc)
        .args([
            "--target=arm-unknown-linux-gnueabi",
            "-march=armv7-a",
            "-c",
            "-o",
        ])
        .arg(&obj)
        .arg(&src)
        .output()
        .ok()?;
    if !built.status.success() {
        return None;
    }
    let triple = if thumb { "thumbv7em" } else { "armv7" };
    let out = Command::new(objdump)
        .args(["-d", &format!("--triple={triple}")])
        .arg(&obj)
        .output()
        .ok()?;
    let listing = String::from_utf8_lossy(&out.stdout);
    let mut by_slot = BTreeMap::new();
    for line in listing.lines() {
        let Some((head, rest)) = line.split_once(':') else {
            continue;
        };
        let Ok(addr) = usize::from_str_radix(head.trim(), 16) else {
            continue;
        };
        // Only what starts a slot is a candidate; the rest is padding, or the
        // tail of a candidate llvm read as longer than this decoder did.
        if addr % SLOT != 0 {
            continue;
        }
        let Some((_, asm)) = rest.split_once('\t') else {
            continue;
        };
        let asm = asm.trim();
        if asm.is_empty() || asm.starts_with("<unknown>") || asm.starts_with(".word") {
            continue;
        }
        by_slot.insert(addr / SLOT, asm.to_string());
    }
    let _ = std::fs::remove_dir_all(&dir);
    Some(by_slot)
}

/// Lay candidates out one per slot, padded with `nop`.
fn image(candidates: &[Vec<u8>], thumb: bool) -> Vec<u8> {
    // `nop` is `mov r0, r0` in A32 and `bf00` in Thumb; either is one
    // instruction that changes nothing and keeps the padding readable.
    let pad: [u8; 4] = if thumb {
        [0x00, 0xbf, 0x00, 0xbf]
    } else {
        [0x00, 0xf0, 0x20, 0xe3]
    };
    let mut out = Vec::with_capacity(candidates.len() * SLOT);
    for c in candidates {
        out.extend_from_slice(c);
        while out.len() % SLOT != 0 {
            let at = out.len() % 4;
            out.push(pad[at]);
        }
    }
    out
}

/// Compare the two decoders over a swept space.
///
/// Returns how many llvm decoded, how many this decoder also decoded, and what
/// it declined by mnemonic.
fn measure(
    candidates: Vec<Vec<u8>>,
    thumb: bool,
) -> Option<(usize, usize, BTreeMap<String, usize>)> {
    let bytes = image(&candidates, thumb);
    let want = oracle(&bytes, thumb)?;
    let mut ours = 0usize;
    let mut missing: BTreeMap<String, usize> = BTreeMap::new();
    for (slot, asm) in &want {
        let at = slot * SLOT;
        let window = &bytes[at..(at + SLOT).min(bytes.len())];
        let decoded = if thumb {
            arm::decode_in(Mode::T32, window, Addr(at as u64), ItState::default()).map(|(i, _)| i)
        } else {
            arm::decode(window, Addr(at as u64))
        };
        match decoded {
            Some(_) => ours += 1,
            None => {
                let m = asm.split_whitespace().next().unwrap_or("?").to_string();
                *missing.entry(m).or_default() += 1;
            }
        }
    }
    Some((want.len(), ours, missing))
}

fn check(thumb: bool, floor: f64, what: &str) {
    let candidates = if thumb {
        t32_candidates()
    } else {
        a32_candidates()
            .into_iter()
            .map(|w| w.to_le_bytes().to_vec())
            .collect()
    };
    let Some((total, ours, missing)) = measure(candidates, thumb) else {
        return; // no assembler or no objdump here
    };
    assert!(total > 2_000, "{what}: only {total} encodings to measure");
    let rate = ours as f64 / total as f64;
    let mut worst: Vec<_> = missing.iter().collect();
    worst.sort_by_key(|(_, n)| std::cmp::Reverse(**n));
    let summary: Vec<String> = worst
        .iter()
        .take(12)
        .map(|(m, n)| format!("{m} x{n}"))
        .collect();
    assert!(
        rate >= floor,
        "{what}: decoded {ours} of {total} ({:.2}%), floor {:.2}%\nbiggest gaps: {}",
        rate * 100.0,
        floor * 100.0,
        summary.join(", ")
    );
    eprintln!(
        "{what} sweep: {ours} of {total} llvm-decoded encodings, {:.2}%",
        rate * 100.0
    );
}

#[test]
fn a32_decodes_what_llvm_decodes() {
    check(false, MIN_A32, "A32");
}

#[test]
fn t32_decodes_what_llvm_decodes() {
    check(true, MIN_T32, "T32");
}

/// A work list, not a gate. Ignored by default.
#[test]
#[ignore = "a report of what the sweep declines, for choosing what to add next"]
fn arm_sweep_report() {
    for (thumb, what) in [(false, "A32"), (true, "T32")] {
        let candidates = if thumb {
            t32_candidates()
        } else {
            a32_candidates()
                .into_iter()
                .map(|w| w.to_le_bytes().to_vec())
                .collect()
        };
        let Some((total, ours, missing)) = measure(candidates, thumb) else {
            return;
        };
        eprintln!("--- {what} --- {ours} of {total}");
        let mut worst: Vec<_> = missing.iter().collect();
        worst.sort_by_key(|(_, n)| std::cmp::Reverse(**n));
        for (m, n) in worst.iter().take(30) {
            eprintln!("  {n:6}  {m}");
        }
    }
}
