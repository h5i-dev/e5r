//! ARM A32 and Thumb-2 decoder.
//!
//! A32 is fixed 32-bit and decodes from a word and an address, the way A64
//! does. T32 does not: an instruction is two or four bytes, and inside an IT
//! block it is conditional with nothing in its own halfwords saying so.
//! [`ItState`] carries that across a block and [`Mode`] is how a caller says
//! which instruction set an address holds, because the bytes never say.
//!
//! The condition is part of the mnemonic in every ARM listing, so mnemonics
//! come from per-opcode tables of sixteen spellings rather than from a suffix
//! glued on at print time: [`Insn::mnemonic`] is a `&'static str`.

// Encoding literals are grouped the way the architecture reference manual draws
// them, which is what makes them checkable against the manual.
#![allow(clippy::unusual_byte_groupings)]

use r12e_core::Addr;

use crate::insn::{Insn, Operand, Reg, RegClass, Shift, Width};

/// Bits `hi..=lo` of `w`.
#[inline]
pub(crate) const fn bits(w: u32, hi: u32, lo: u32) -> u32 {
    (w >> lo) & ((1u32 << (hi - lo + 1)) - 1)
}

/// Bit `n` of `w`.
#[inline]
pub(crate) const fn bit(w: u32, n: u32) -> u32 {
    (w >> n) & 1
}

/// Sign-extend the low `n` bits of `v`.
#[inline]
pub(crate) const fn sext(v: u32, n: u32) -> i64 {
    let s = 64 - n;
    ((v as u64) << s) as i64 >> s
}

/// The sixteen spellings of one mnemonic: `eq` through `le`, then `al`, which
/// is spelled by leaving the mnemonic alone, then the condition that has no
/// name, which only an IT block with an unpredictable first condition can
/// produce. A condition that prints inside the mnemonic and an `&'static str`
/// mnemonic together mean every opcode needs its own table; `concat!` builds
/// them at compile time.
macro_rules! conds {
    ($p:literal) => {
        conds!($p, "")
    };
    ($p:literal, $s:literal) => {
        &[
            concat!($p, "eq", $s),
            concat!($p, "ne", $s),
            concat!($p, "hs", $s),
            concat!($p, "lo", $s),
            concat!($p, "mi", $s),
            concat!($p, "pl", $s),
            concat!($p, "vs", $s),
            concat!($p, "vc", $s),
            concat!($p, "hi", $s),
            concat!($p, "ls", $s),
            concat!($p, "ge", $s),
            concat!($p, "lt", $s),
            concat!($p, "gt", $s),
            concat!($p, "le", $s),
            concat!($p, $s),
            concat!($p, "<und>", $s),
        ]
    };
}

/// `lsl r3` and the other 63: a shift by a register is not an operand kind, so
/// it rides as a name appended after the register it shifts.
macro_rules! shift_regs {
    ($s:literal) => {
        [
            concat!($s, " r0"),
            concat!($s, " r1"),
            concat!($s, " r2"),
            concat!($s, " r3"),
            concat!($s, " r4"),
            concat!($s, " r5"),
            concat!($s, " r6"),
            concat!($s, " r7"),
            concat!($s, " r8"),
            concat!($s, " r9"),
            concat!($s, " r10"),
            concat!($s, " r11"),
            concat!($s, " r12"),
            concat!($s, " sp"),
            concat!($s, " lr"),
            concat!($s, " pc"),
        ]
    };
}

pub mod a32;
pub mod t32;
pub mod text;
pub mod vfp;

pub use t32::ItState;
pub use text::format;

/// The `al` encoding, which prints as no suffix at all.
pub(crate) const AL: u32 = 14;

/// Pick a mnemonic's spelling for `cond` out of a [`conds!`] table.
#[inline]
pub(crate) fn cm(t: &'static [&'static str; 16], cond: u32) -> &'static str {
    t[(cond as usize) & 15]
}

const SHIFT_BY_REG: [[&str; 16]; 4] = [
    shift_regs!("lsl"),
    shift_regs!("lsr"),
    shift_regs!("asr"),
    shift_regs!("ror"),
];

/// The condition names as a listing spells them on their own, where `al` is
/// written out: the operand of an `it`.
pub(crate) const COND_NAMES: [&str; 16] = [
    "eq", "ne", "hs", "lo", "mi", "pl", "vs", "vc", "hi", "ls", "ge", "lt", "gt", "le", "al", "nv",
];

/// One of the sixteen core registers. Thirteen and fifteen get their own
/// classes so that stack and pc-relative analysis works without a table.
#[inline]
pub(crate) fn reg(n: u32) -> Reg {
    match n & 15 {
        13 => Reg {
            class: RegClass::Sp,
            num: 13,
            width: Width::W32,
        },
        15 => Reg {
            class: RegClass::Pc,
            num: 15,
            width: Width::W32,
        },
        n => Reg::gpr(n as u8, Width::W32),
    }
}

/// A single or double precision VFP register.
#[inline]
pub(crate) fn vreg(n: u32, double: bool) -> Reg {
    Reg::vec(n as u8, if double { Width::W64 } else { Width::W32 })
}

/// A core register list rides in [`Operand::Sys`], the one operand whose
/// meaning its decoder owns. Tag zero is a sixteen-bit core mask.
#[inline]
pub(crate) fn core_list(mask: u32) -> Operand {
    Operand::Sys(mask & 0xffff)
}

/// A VFP list is always a run: tag 1 single, tag 2 double, first register in
/// bits 15:8 and the count in bits 7:0.
#[inline]
pub(crate) fn vfp_list(double: bool, first: u32, count: u32) -> Operand {
    Operand::Sys((if double { 2 } else { 1 }) << 28 | (first & 0xff) << 8 | (count & 0xff))
}

/// The A32 modified immediate: an eight-bit value rotated right by twice the
/// four-bit field above it.
#[inline]
pub(crate) fn so_imm(imm12: u32) -> u32 {
    bits(imm12, 7, 0).rotate_right(bits(imm12, 11, 8) * 2)
}

/// How LLVM spells one. It prints the value when the encoding uses the
/// smallest rotate that can name it, and the encoded `#bits, #rot` pair when
/// it does not, because only the pair assembles back to these bits. The value
/// is signed except where a listing would rather read the bit pattern.
pub(crate) fn so_imm_ops(imm12: u32, unsigned: bool) -> (Operand, Option<Operand>) {
    let value = so_imm(imm12);
    if canonical_so_imm(value) == Some(imm12) {
        let v = if unsigned {
            value as i64
        } else {
            value as i32 as i64
        };
        return (Operand::Count(v), None);
    }
    (
        Operand::Count(bits(imm12, 7, 0) as i64),
        Some(Operand::Count(bits(imm12, 11, 8) as i64 * 2)),
    )
}

/// The canonical encoding of a value, if a single rotate can name it.
fn canonical_so_imm(v: u32) -> Option<u32> {
    if v <= 0xff {
        return Some(v);
    }
    let amt = so_imm_rotate(v);
    ((!255u32).rotate_right(amt) & v == 0).then(|| v.rotate_left(amt) | (amt >> 1) << 8)
}

/// The smallest even rotate that brings a value into eight bits, with the
/// retry LLVM does for patterns like `0xf000000f`.
fn so_imm_rotate(v: u32) -> u32 {
    if v & !255 == 0 {
        return 0;
    }
    let amt = v.trailing_zeros() & !1;
    if v.rotate_right(amt) & !255 == 0 {
        return (32 - amt) & 31;
    }
    if v & 63 != 0 {
        let amt = (v & !63).trailing_zeros() & !1;
        if v.rotate_right(amt) & !255 == 0 {
            return (32 - amt) & 31;
        }
    }
    0
}

/// `ThumbExpandImm`, which spends four of its twelve bits on byte-replication
/// patterns before falling back to a rotate.
pub(crate) fn t2_imm(v: u32) -> u32 {
    let b = bits(v, 7, 0);
    if bits(v, 11, 10) == 0 {
        match bits(v, 9, 8) {
            0 => b,
            1 => (b << 16) | b,
            2 => (b << 24) | (b << 8),
            _ => (b << 24) | (b << 16) | (b << 8) | b,
        }
    } else {
        (0x80 | bits(v, 6, 0)).rotate_right(v >> 7)
    }
}

/// ARM addresses are thirty-two bits, so a branch that runs off either end
/// wraps there and not in the sixty-four-bit [`Addr`].
#[inline]
pub(crate) fn target(addr: Addr, off: i64) -> Addr {
    Addr((addr.get() as u32).wrapping_add(off as u32) as u64)
}

/// The shift a two-bit type and a five-bit amount name. A zero amount means 32
/// for `lsr` and `asr`, and `rrx` for `ror`, which is [`Shift::Ror`] by zero.
pub(crate) fn decode_shift(ty: u32, imm5: u32) -> (Shift, u8) {
    match ty {
        0 => (Shift::Lsl, imm5 as u8),
        1 => (Shift::Lsr, if imm5 == 0 { 32 } else { imm5 as u8 }),
        2 => (Shift::Asr, if imm5 == 0 { 32 } else { imm5 as u8 }),
        _ => (Shift::Ror, imm5 as u8),
    }
}

/// A register with an immediate shift, as a data-processing source. `lsl #0`
/// is no shift at all and prints as the bare register.
pub(crate) fn shifted(rm: u32, ty: u32, imm5: u32) -> Operand {
    if ty == 0 && imm5 == 0 {
        return Operand::Reg(reg(rm));
    }
    let (sh, n) = decode_shift(ty, imm5);
    Operand::Shifted(reg(rm), sh, n)
}

/// The name for a shift by a register, to follow the register it shifts.
pub(crate) fn shift_by_reg(ty: u32, rs: u32) -> &'static str {
    SHIFT_BY_REG[(ty & 3) as usize][(rs & 15) as usize]
}

/// A base register with writeback, `r1!`, which is not an operand kind either.
const WB_REGS: [&str; 16] = [
    "r0!", "r1!", "r2!", "r3!", "r4!", "r5!", "r6!", "r7!", "r8!", "r9!", "r10!", "r11!", "r12!",
    "sp!", "lr!", "pc!",
];

/// The spelling of a base register that the instruction writes back.
#[inline]
pub(crate) fn wb_reg(n: u32) -> &'static str {
    WB_REGS[(n & 15) as usize]
}

/// Barrier options by their four-bit field; the unnamed ones print as numbers.
pub(crate) const BARRIERS: [&str; 16] = [
    "#0x0", "oshld", "oshst", "osh", "#0x4", "nshld", "nshst", "nsh", "#0x8", "ishld", "ishst",
    "ish", "#0xc", "ld", "st", "sy",
];

/// The status register field spellings of a `msr` mask, `SPSR` above `CPSR`.
pub(crate) const MSR_MASKS: [&str; 32] = [
    "CPSR",
    "CPSR_c",
    "CPSR_x",
    "CPSR_xc",
    "APSR_g",
    "CPSR_sc",
    "CPSR_sx",
    "CPSR_sxc",
    "APSR_nzcvq",
    "CPSR_fc",
    "CPSR_fx",
    "CPSR_fxc",
    "APSR_nzcvqg",
    "CPSR_fsc",
    "CPSR_fsx",
    "CPSR_fsxc",
    "SPSR",
    "SPSR_c",
    "SPSR_x",
    "SPSR_xc",
    "SPSR_s",
    "SPSR_sc",
    "SPSR_sx",
    "SPSR_sxc",
    "SPSR_f",
    "SPSR_fc",
    "SPSR_fx",
    "SPSR_fxc",
    "SPSR_fs",
    "SPSR_fsc",
    "SPSR_fsx",
    "SPSR_fsxc",
];

/// Which instruction set an address holds. Nothing in the bytes says, so the
/// caller does; in an ELF the `$a` and `$t` mapping symbols are where it comes
/// from, and the low bit of a branch target is where it changes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Mode {
    /// A32, four bytes per instruction.
    A32,
    /// T32, two or four.
    T32,
}

/// Decode one A32 instruction.
pub fn decode(bytes: &[u8], addr: Addr) -> Option<Insn> {
    let w = u32::from_le_bytes(bytes.get(..4)?.try_into().ok()?);
    decode_word(w, addr)
}

/// Decode one A32 instruction from its word, the way A64 does.
pub fn decode_word(w: u32, addr: Addr) -> Option<Insn> {
    a32::decode(w, addr)
}

/// Decode one T32 instruction under `it`, and report the IT state the next one
/// runs under.
pub fn decode_thumb(bytes: &[u8], addr: Addr, it: ItState) -> Option<(Insn, ItState)> {
    t32::decode(bytes, addr, it)
}

/// Decode in either instruction set. The IT state is ignored in A32, which has
/// a condition field in every word instead.
pub fn decode_in(mode: Mode, bytes: &[u8], addr: Addr, it: ItState) -> Option<(Insn, ItState)> {
    match mode {
        Mode::A32 => decode(bytes, addr).map(|i| (i, ItState::default())),
        Mode::T32 => decode_thumb(bytes, addr, it),
    }
}

/// A cursor over a run of T32 instructions, which is the only way to decode
/// one correctly: the IT state comes from the instructions before it.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Thumb {
    it: ItState,
}

impl Thumb {
    /// A cursor outside any IT block.
    pub fn new() -> Thumb {
        Thumb::default()
    }

    /// The IT state the next instruction will run under.
    pub fn state(self) -> ItState {
        self.it
    }

    /// Resume at a point whose IT state is known, or reset at a point where it
    /// is not: a branch target is never inside an IT block.
    pub fn resume(&mut self, it: ItState) {
        self.it = it;
    }

    /// Decode the next instruction and advance the IT state over it.
    pub fn decode(&mut self, bytes: &[u8], addr: Addr) -> Option<Insn> {
        let (i, next) = t32::decode(bytes, addr, self.it)?;
        self.it = next;
        Some(i)
    }
}
