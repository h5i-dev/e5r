//! AArch64 A64 decoder.
//!
//! Fixed 32-bit instructions, little-endian, so decoding is a pure function of
//! four bytes and the address. The top-level split follows the architecture
//! reference manual's decode tree on bits 28:25, and each group is a function.
//!
//! Aliases are resolved here rather than left to the formatter: `sbfm` with a
//! full-width extraction *is* `asr`, and analysis that has to recognize both
//! spellings is analysis with a bug waiting in it.

// Encoding literals are grouped the way the architecture reference manual draws
// them, which is what makes them checkable against the manual.
#![allow(clippy::unusual_byte_groupings)]

pub mod simd;
pub mod sysreg;
pub mod text;

pub use text::{Style, format};

use e5r_core::Addr;

use crate::insn::{AddrMode, Cond, Extend, Flow, Insn, Mem, Operand, Reg, RegClass, Shift, Width};

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
const fn sext(v: u32, n: u32) -> i64 {
    let shift = 64 - n;
    ((v as u64) << shift) as i64 >> shift
}

/// Register 31 is the zero register in most encodings.
#[inline]
fn r(num: u32, sf: bool) -> Reg {
    let width = if sf { Width::W64 } else { Width::W32 };
    if num == 31 {
        Reg {
            class: RegClass::Zr,
            num: 31,
            width,
        }
    } else {
        Reg::gpr(num as u8, width)
    }
}

/// Register 31 is the stack pointer in the rest.
#[inline]
fn rsp(num: u32, sf: bool) -> Reg {
    let width = if sf { Width::W64 } else { Width::W32 };
    if num == 31 {
        Reg {
            class: RegClass::Sp,
            num: 31,
            width,
        }
    } else {
        Reg::gpr(num as u8, width)
    }
}

/// Vector register at a given width.
#[inline]
fn v(num: u32, width: Width) -> Reg {
    Reg::vec(num as u8, width)
}

/// A general purpose register, for the SIMD module.
pub(crate) fn gpr_for(num: u32, wide: bool) -> Reg {
    r(num, wide)
}

/// A stack-pointer-capable register, for the SIMD module.
pub(crate) fn rsp_for(num: u32) -> Reg {
    rsp(num, true)
}

const COND_NAMES: [&str; 16] = [
    "eq", "ne", "cs", "cc", "mi", "pl", "vs", "vc", "hi", "ls", "ge", "lt", "gt", "le", "al", "nv",
];

/// The mnemonic for `b.<cond>`, as one static string so [`Insn`] stays `Copy`.
const B_COND: [&str; 16] = [
    "b.eq", "b.ne", "b.cs", "b.cc", "b.mi", "b.pl", "b.vs", "b.vc", "b.hi", "b.ls", "b.ge", "b.lt",
    "b.gt", "b.le", "b.al", "b.nv",
];

/// Barrier option names, indexed by `CRm`. The unnamed slots print as numbers.
const BARRIERS: [&str; 16] = [
    "#0x0", "oshld", "oshst", "osh", "#0x4", "nshld", "nshst", "nsh", "#0x8", "ishld", "ishst",
    "ish", "#0xc", "ld", "st", "sy",
];

/// Prefetch operation name for a 5-bit `Rt`.
///
/// The field is `type:target:policy`: pld/pli/pst, l1/l2/l3/slc, keep/strm.
/// The eight encodings with no type print as bare numbers, as objdump does.
fn prefetch_name(rt: u32) -> &'static str {
    const NAMES: [&str; 32] = [
        "pldl1keep",
        "pldl1strm",
        "pldl2keep",
        "pldl2strm",
        "pldl3keep",
        "pldl3strm",
        "pldslckeep",
        "pldslcstrm",
        "plil1keep",
        "plil1strm",
        "plil2keep",
        "plil2strm",
        "plil3keep",
        "plil3strm",
        "plislckeep",
        "plislcstrm",
        "pstl1keep",
        "pstl1strm",
        "pstl2keep",
        "pstl2strm",
        "pstl3keep",
        "pstl3strm",
        "pstslckeep",
        "pstslcstrm",
        "#0x18",
        "#0x19",
        "#0x1a",
        "#0x1b",
        "#0x1c",
        "#0x1d",
        "#0x1e",
        "#0x1f",
    ];
    NAMES[(rt & 31) as usize]
}

/// PSTATE field name for an `op1:op2` pair.
fn pstate_name(op1: u32, op2: u32) -> &'static str {
    match (op1, op2) {
        (0, 3) => "uao",
        (0, 4) => "pan",
        (0, 5) => "spsel",
        (3, 1) => "tco",
        (3, 2) => "ssbs",
        (3, 4) => "dit",
        (3, 6) => "daifset",
        (3, 7) => "daifclr",
        _ => "pstate",
    }
}

/// The DC, IC, AT and TLBI operations, by `op1:CRn:CRm:op2`.
fn sys_alias(op1: u32, crn: u32, crm: u32, op2: u32) -> Option<(&'static str, &'static str)> {
    Some(match (op1, crn, crm, op2) {
        (0, 7, 1, 0) => ("ic", "ialluis"),
        (0, 7, 5, 0) => ("ic", "iallu"),
        (3, 7, 5, 1) => ("ic", "ivau"),
        (0, 7, 6, 1) => ("dc", "ivac"),
        (0, 7, 6, 2) => ("dc", "isw"),
        (0, 7, 10, 2) => ("dc", "csw"),
        (0, 7, 14, 2) => ("dc", "cisw"),
        (3, 7, 4, 1) => ("dc", "zva"),
        (3, 7, 4, 3) => ("dc", "gva"),
        (3, 7, 4, 4) => ("dc", "gzva"),
        (3, 7, 10, 1) => ("dc", "cvac"),
        (3, 7, 11, 1) => ("dc", "cvau"),
        (3, 7, 12, 1) => ("dc", "cvap"),
        (3, 7, 13, 1) => ("dc", "cvadp"),
        (3, 7, 14, 1) => ("dc", "civac"),
        (0, 7, 8, 0) => ("at", "s1e1r"),
        (0, 7, 8, 1) => ("at", "s1e1w"),
        (0, 7, 8, 2) => ("at", "s1e0r"),
        (0, 7, 8, 3) => ("at", "s1e0w"),
        (0, 8, 3, 0) => ("tlbi", "vmalle1is"),
        (0, 8, 3, 1) => ("tlbi", "vae1is"),
        (0, 8, 3, 3) => ("tlbi", "vaae1is"),
        (0, 8, 7, 0) => ("tlbi", "vmalle1"),
        (0, 8, 7, 1) => ("tlbi", "vae1"),
        (0, 8, 7, 3) => ("tlbi", "vaae1"),
        _ => return None,
    })
}

/// Render a system register encoding, given bits 20:5 of the instruction.
pub fn sysreg_name(enc: u32) -> String {
    // Tagged values from the generic SYS form print as a bare `cN`.
    if enc & 0xffff_0000 != 0 {
        return format!("C{}", enc & 0xffff);
    }
    if let Ok(e) = u16::try_from(enc)
        && let Some(n) = sysreg::lookup(e)
    {
        return n.to_string();
    }
    // binutils prints op0 straight from bits 20:19, which is 2 or 3 for a
    // normal MRS and 0 or 1 for the encodings it does not consider one.
    let op0 = (enc >> 14) & 3;
    let op1 = (enc >> 11) & 7;
    let crn = (enc >> 7) & 15;
    let crm = (enc >> 3) & 15;
    let op2 = enc & 7;
    format!("s{op0}_{op1}_c{crn}_c{crm}_{op2}")
}

/// Name of a condition code.
pub fn cond_name(c: Cond) -> &'static str {
    COND_NAMES[(c.0 & 15) as usize]
}

/// Decode one instruction at `addr`.
///
/// Returns `None` when fewer than four bytes are available or the encoding is
/// not allocated. An unallocated encoding is not an error: it is data, or a
/// newer extension, and the caller decides which.
pub fn decode(bytes: &[u8], addr: Addr) -> Option<Insn> {
    if bytes.len() < 4 {
        return None;
    }
    let w = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
    decode_word(w, addr)
}

/// Decode from an already-assembled word.
pub fn decode_word(w: u32, addr: Addr) -> Option<Insn> {
    let op0 = bits(w, 28, 25);
    match op0 {
        0b1000 | 0b1001 => dp_immediate(w, addr),
        0b1010 | 0b1011 => branches(w, addr),
        0b0100 | 0b0110 | 0b1100 | 0b1110 => loads_stores(w, addr),
        0b0101 | 0b1101 => dp_register(w, addr),
        0b0111 | 0b1111 => dp_simd(w, addr),
        // 0b0000 is reserved; UDF #imm16 lives at the bottom of it.
        0b0000 if bits(w, 31, 16) == 0 => {
            let mut i = ins(addr, "udf", Flow::Trap);
            i.push(Operand::Count(bits(w, 15, 0) as i64));
            Some(i)
        }
        _ => None,
    }
}

fn ins(addr: Addr, mnemonic: &'static str, flow: Flow) -> Insn {
    Insn::new(addr, 4, mnemonic, flow)
}

// ---------------------------------------------------------------- immediates

fn dp_immediate(w: u32, addr: Addr) -> Option<Insn> {
    match bits(w, 25, 23) {
        0b000 | 0b001 => pc_rel(w, addr),
        0b010 => add_sub_imm(w, addr),
        0b011 => add_sub_imm_tags(w, addr),
        0b100 => logical_imm(w, addr),
        0b101 => move_wide(w, addr),
        0b110 => bitfield(w, addr),
        0b111 => extract(w, addr),
        _ => None,
    }
}

/// ADR and ADRP: the address-forming pair that makes a string reference.
fn pc_rel(w: u32, addr: Addr) -> Option<Insn> {
    let imm = (bits(w, 23, 5) << 2) | bits(w, 30, 29);
    let page = bit(w, 31) == 1;
    let (mnem, target) = if page {
        // ADRP shifts by 12 and drops the low 12 bits of the pc.
        let off = sext(imm, 21) << 12;
        ("adrp", Addr(addr.get() & !0xfff).wrapping_offset(off))
    } else {
        ("adr", addr.wrapping_offset(sext(imm, 21)))
    };
    let mut i = ins(addr, mnem, Flow::Next);
    i.push(Operand::Reg(r(bits(w, 4, 0), true)));
    i.push(Operand::Addr(target));
    Some(i)
}

fn add_sub_imm(w: u32, addr: Addr) -> Option<Insn> {
    let sf = bit(w, 31) == 1;
    let sub = bit(w, 30) == 1;
    let setflags = bit(w, 29) == 1;
    let sh = bit(w, 22) == 1;
    let imm12 = bits(w, 21, 10);
    let imm = imm12 as i64;
    let rd = bits(w, 4, 0);
    let rn = bits(w, 9, 5);

    // Aliases objdump prefers.
    if setflags && rd == 31 {
        let mut i = ins(addr, if sub { "cmp" } else { "cmn" }, Flow::Next);
        i.push(Operand::Reg(rsp(rn, sf)));
        i.push(Operand::Imm(imm));
        if sh {
            i.push(Operand::ShiftOp(Shift::Lsl, 12));
        }
        return Some(i);
    }
    if !sub && !setflags && !sh && imm == 0 && (rd == 31 || rn == 31) {
        let mut i = ins(addr, "mov", Flow::Next);
        i.push(Operand::Reg(rsp(rd, sf)));
        i.push(Operand::Reg(rsp(rn, sf)));
        return Some(i);
    }

    let mnem = match (sub, setflags) {
        (false, false) => "add",
        (false, true) => "adds",
        (true, false) => "sub",
        (true, true) => "subs",
    };
    let mut i = ins(addr, mnem, Flow::Next);
    i.push(Operand::Reg(if setflags { r(rd, sf) } else { rsp(rd, sf) }));
    i.push(Operand::Reg(rsp(rn, sf)));
    i.push(Operand::Imm(imm));
    if sh {
        i.push(Operand::ShiftOp(Shift::Lsl, 12));
    }
    Some(i)
}

/// ADDG and SUBG, the memory-tagging forms.
fn add_sub_imm_tags(w: u32, addr: Addr) -> Option<Insn> {
    if bit(w, 31) == 0 || bit(w, 29) == 1 {
        return None;
    }
    // Bit 22 set makes this the CSSC min/max immediate group instead.
    if bit(w, 22) == 1 {
        return min_max_imm(w, addr);
    }
    let mut i = ins(
        addr,
        if bit(w, 30) == 1 { "subg" } else { "addg" },
        Flow::Next,
    );
    i.push(Operand::Reg(rsp(bits(w, 4, 0), true)));
    i.push(Operand::Reg(rsp(bits(w, 9, 5), true)));
    i.push(Operand::Imm((bits(w, 21, 16) as i64) << 4));
    i.push(Operand::Imm(bits(w, 13, 10) as i64));
    Some(i)
}

/// SMAX, UMAX, SMIN and UMIN against an 8-bit immediate (FEAT_CSSC).
fn min_max_imm(w: u32, addr: Addr) -> Option<Insn> {
    let sf = bit(w, 31) == 1;
    let imm8 = bits(w, 17, 10);
    let (mnem, signed) = match bits(w, 21, 18) {
        0b0000 => ("smax", true),
        0b0001 => ("umax", false),
        0b0010 => ("smin", true),
        0b0011 => ("umin", false),
        _ => return None,
    };
    let mut i = ins(addr, mnem, Flow::Next);
    i.push(Operand::Reg(r(bits(w, 4, 0), sf)));
    i.push(Operand::Reg(r(bits(w, 9, 5), sf)));
    i.push(Operand::Count(if signed {
        sext(imm8, 8)
    } else {
        imm8 as i64
    }));
    Some(i)
}

/// The logical immediate encoding: a run of ones rotated within a power-of-two
/// element, packed into `N:immr:imms`. Returns `None` for the reserved patterns.
fn decode_bit_masks(n: u32, imms: u32, immr: u32, sf: bool) -> Option<u64> {
    let width = if sf { 64 } else { 32 };
    // The element size is found from the highest clear bit of `imms` under `n`.
    let combined = (n << 6) | (!imms & 0x3f);
    let len = 31 - (combined | 1).leading_zeros();
    if len == 0 || (1u32 << len) > width {
        return None;
    }
    let esize = 1u32 << len;
    let levels = esize - 1;
    // S = esize - 1 is reserved.
    if imms & levels == levels {
        return None;
    }
    let s = imms & levels;
    let r = immr & levels;
    let welem: u64 = if s + 1 >= 64 {
        u64::MAX
    } else {
        (1u64 << (s + 1)) - 1
    };
    // Rotate right within the element, then replicate to the full width.
    let elem = if r == 0 {
        welem
    } else {
        let e = esize as u64;
        let masked = welem & if e >= 64 { u64::MAX } else { (1u64 << e) - 1 };
        ((masked >> r) | (masked << (e - r as u64)))
            & if e >= 64 { u64::MAX } else { (1u64 << e) - 1 }
    };
    let mut out = 0u64;
    let mut pos = 0;
    while pos < width {
        out |= elem << pos;
        pos += esize;
    }
    Some(if sf { out } else { out & 0xffff_ffff })
}

/// Whether a `MOVZ` or `MOVN` would spell this bitmask immediate, in which
/// case `ORR Rd, ZR, #imm` keeps its own name rather than taking the MOV alias.
///
/// The ARM ARM defines the test as written here; it is the reason `orr x1,
/// xzr, #0x10` disassembles as itself while a value no move-wide can reach
/// disassembles as `mov`.
fn move_wide_preferred(sf: bool, n: u32, imms: u32, immr: u32) -> bool {
    let width = if sf { 64 } else { 32 };
    // The immediate's element size has to be the whole register.
    if sf && n != 1 {
        return false;
    }
    if !sf && (n != 0 || imms & 0x20 != 0) {
        return false;
    }
    if imms < 16 {
        // A MOVZ needs the ones to stay inside one halfword once rotated.
        return (16 - immr % 16) % 16 <= 15 - imms;
    }
    if imms >= width - 15 {
        // A MOVN needs the same of the zeros.
        return immr % 16 <= imms - width + 15;
    }
    false
}

fn logical_imm(w: u32, addr: Addr) -> Option<Insn> {
    let sf = bit(w, 31) == 1;
    let opc = bits(w, 30, 29);
    let n = bit(w, 22);
    if !sf && n == 1 {
        return None;
    }
    let imm = decode_bit_masks(n, bits(w, 15, 10), bits(w, 21, 16), sf)?;
    let rd = bits(w, 4, 0);
    let rn = bits(w, 9, 5);

    // ANDS with a discarded destination is TST; ORR from zr is MOV.
    if opc == 0b11 && rd == 31 {
        let mut i = ins(addr, "tst", Flow::Next);
        i.push(Operand::Reg(r(rn, sf)));
        i.push(Operand::UImm(imm));
        return Some(i);
    }
    if opc == 0b01 && rn == 31 && !move_wide_preferred(sf, n, bits(w, 15, 10), bits(w, 21, 16)) {
        let mut i = ins(addr, "mov", Flow::Next);
        i.push(Operand::Reg(rsp(rd, sf)));
        i.push(Operand::UImm(imm));
        return Some(i);
    }

    let mnem = match opc {
        0b00 => "and",
        0b01 => "orr",
        0b10 => "eor",
        _ => "ands",
    };
    let mut i = ins(addr, mnem, Flow::Next);
    i.push(Operand::Reg(if opc == 0b11 {
        r(rd, sf)
    } else {
        rsp(rd, sf)
    }));
    i.push(Operand::Reg(r(rn, sf)));
    i.push(Operand::UImm(imm));
    Some(i)
}

fn move_wide(w: u32, addr: Addr) -> Option<Insn> {
    let sf = bit(w, 31) == 1;
    let opc = bits(w, 30, 29);
    let hw = bits(w, 22, 21);
    if !sf && hw > 1 {
        return None;
    }
    let imm16 = bits(w, 20, 5) as u64;
    let shift = hw * 16;
    let rd = bits(w, 4, 0);

    match opc {
        0b00 => {
            // MOVN with a value that fits is spelled MOV by objdump.
            let val = !(imm16 << shift);
            let val = if sf { val } else { val & 0xffff_ffff };
            if !(imm16 == 0 && hw != 0) {
                let mut i = ins(addr, "mov", Flow::Next);
                i.push(Operand::Reg(r(rd, sf)));
                i.push(Operand::UImm(val));
                return Some(i);
            }
            let mut i = ins(addr, "movn", Flow::Next);
            i.push(Operand::Reg(r(rd, sf)));
            i.push(Operand::Imm(imm16 as i64));
            if shift != 0 {
                i.push(Operand::ShiftOp(Shift::Lsl, shift as u8));
            }
            Some(i)
        }
        0b10 => {
            if !(imm16 == 0 && hw != 0) {
                let mut i = ins(addr, "mov", Flow::Next);
                i.push(Operand::Reg(r(rd, sf)));
                i.push(Operand::UImm(imm16 << shift));
                return Some(i);
            }
            let mut i = ins(addr, "movz", Flow::Next);
            i.push(Operand::Reg(r(rd, sf)));
            i.push(Operand::Imm(imm16 as i64));
            // Only a zero immediate reaches here, so the shift is the whole
            // difference between this and any other encoding of the same
            // value, and dropping it printed four distinct instructions the
            // same way.
            if shift != 0 {
                i.push(Operand::ShiftOp(Shift::Lsl, shift as u8));
            }
            Some(i)
        }
        0b11 => {
            let mut i = ins(addr, "movk", Flow::Next);
            i.push(Operand::Reg(r(rd, sf)));
            i.push(Operand::Imm(imm16 as i64));
            if shift != 0 {
                i.push(Operand::ShiftOp(Shift::Lsl, shift as u8));
            }
            Some(i)
        }
        _ => None,
    }
}

fn bitfield(w: u32, addr: Addr) -> Option<Insn> {
    let sf = bit(w, 31) == 1;
    let opc = bits(w, 30, 29);
    let n = bit(w, 22);
    if n != bit(w, 31) {
        return None;
    }
    let immr = bits(w, 21, 16);
    let imms = bits(w, 15, 10);
    let rd = bits(w, 4, 0);
    let rn = bits(w, 9, 5);
    let width = if sf { 64 } else { 32 };

    let signed = opc == 0b00;
    let unsigned = opc == 0b10;

    // The alias set the manual defines, in the order objdump prefers them.
    // LSL is UBFM with imms = immr - 1. The signed encoding of that shape is
    // SBFIZ, not a shift, and falls through to the insert forms below.
    if unsigned && imms + 1 == immr {
        let mut i = ins(addr, "lsl", Flow::Next);
        i.push(Operand::Reg(r(rd, sf)));
        i.push(Operand::Reg(r(rn, sf)));
        i.push(Operand::Count((width - immr) as i64));
        return Some(i);
    }
    if imms == width - 1 && (signed || unsigned) {
        let mut i = ins(addr, if signed { "asr" } else { "lsr" }, Flow::Next);
        i.push(Operand::Reg(r(rd, sf)));
        i.push(Operand::Reg(r(rn, sf)));
        i.push(Operand::Count(immr as i64));
        return Some(i);
    }
    if immr == 0 && (signed || unsigned) {
        let ext = match (signed, imms) {
            (true, 7) => Some("sxtb"),
            (true, 15) => Some("sxth"),
            (true, 31) if sf => Some("sxtw"),
            // There is no 64-bit UXTB or UXTH: zero extending into an X
            // register is already what writing a W register does.
            (false, 7) if !sf => Some("uxtb"),
            (false, 15) if !sf => Some("uxth"),
            _ => None,
        };
        if let Some(m) = ext {
            let mut i = ins(addr, m, Flow::Next);
            i.push(Operand::Reg(r(rd, sf)));
            i.push(Operand::Reg(r(rn, false)));
            return Some(i);
        }
    }
    if imms < immr {
        // Insert forms.
        let mnem = match opc {
            0b00 => "sbfiz",
            0b01 => "bfi",
            _ => "ubfiz",
        };
        let mut i = ins(addr, mnem, Flow::Next);
        i.push(Operand::Reg(r(rd, sf)));
        i.push(Operand::Reg(r(rn, sf)));
        i.push(Operand::Count((width - immr) as i64));
        i.push(Operand::Count((imms + 1) as i64));
        return Some(i);
    }

    let mnem = match opc {
        0b00 => "sbfx",
        0b01 => "bfxil",
        _ => "ubfx",
    };
    let mut i = ins(addr, mnem, Flow::Next);
    i.push(Operand::Reg(r(rd, sf)));
    i.push(Operand::Reg(r(rn, sf)));
    i.push(Operand::Count(immr as i64));
    i.push(Operand::Count((imms - immr + 1) as i64));
    Some(i)
}

fn extract(w: u32, addr: Addr) -> Option<Insn> {
    let sf = bit(w, 31) == 1;
    if bits(w, 30, 29) != 0 || bit(w, 22) != bit(w, 31) {
        return None;
    }
    let rd = bits(w, 4, 0);
    let rn = bits(w, 9, 5);
    let rm = bits(w, 20, 16);
    let imms = bits(w, 15, 10);
    if rn == rm {
        let mut i = ins(addr, "ror", Flow::Next);
        i.push(Operand::Reg(r(rd, sf)));
        i.push(Operand::Reg(r(rn, sf)));
        i.push(Operand::Count(imms as i64));
        return Some(i);
    }
    let mut i = ins(addr, "extr", Flow::Next);
    i.push(Operand::Reg(r(rd, sf)));
    i.push(Operand::Reg(r(rn, sf)));
    i.push(Operand::Reg(r(rm, sf)));
    i.push(Operand::Count(imms as i64));
    Some(i)
}

// ------------------------------------------------------------------ branches

fn branches(w: u32, addr: Addr) -> Option<Insn> {
    let op0 = bits(w, 31, 29);

    // Conditional branch immediate.
    if op0 == 0b010 && bit(w, 25) == 0 {
        let cond = bits(w, 3, 0);
        if bit(w, 4) != 0 {
            return None;
        }
        let target = addr.wrapping_offset(sext(bits(w, 23, 5), 19) << 2);
        let mut i = ins(addr, B_COND[cond as usize], Flow::CondBranch(target));
        i.push(Operand::Addr(target));
        return Some(i);
    }

    // Exception generation. The whole 0xd4 page is this group; an extra
    // condition on op1 here silently dropped every svc and brk.
    if bits(w, 31, 24) == 0b1101_0100 {
        return exception(w, addr);
    }
    // System.
    if bits(w, 31, 22) == 0b1101_0101_00 {
        return system(w, addr);
    }
    // Unconditional branch register.
    if bits(w, 31, 25) == 0b1101_011 {
        return branch_register(w, addr);
    }
    // Unconditional branch immediate.
    if bits(w, 30, 26) == 0b00101 {
        let link = bit(w, 31) == 1;
        let target = addr.wrapping_offset(sext(bits(w, 25, 0), 26) << 2);
        let flow = if link {
            Flow::Call(target)
        } else {
            Flow::Branch(target)
        };
        let mut i = ins(addr, if link { "bl" } else { "b" }, flow);
        i.push(Operand::Addr(target));
        return Some(i);
    }
    // Compare and branch.
    if bits(w, 30, 25) == 0b011010 {
        let sf = bit(w, 31) == 1;
        let neg = bit(w, 24) == 1;
        let target = addr.wrapping_offset(sext(bits(w, 23, 5), 19) << 2);
        let mut i = ins(
            addr,
            if neg { "cbnz" } else { "cbz" },
            Flow::CondBranch(target),
        );
        i.push(Operand::Reg(r(bits(w, 4, 0), sf)));
        i.push(Operand::Addr(target));
        return Some(i);
    }
    // Test and branch.
    if bits(w, 30, 25) == 0b011011 {
        let neg = bit(w, 24) == 1;
        let b = (bit(w, 31) << 5) | bits(w, 23, 19);
        let target = addr.wrapping_offset(sext(bits(w, 18, 5), 14) << 2);
        let mut i = ins(
            addr,
            if neg { "tbnz" } else { "tbz" },
            Flow::CondBranch(target),
        );
        i.push(Operand::Reg(r(bits(w, 4, 0), b >= 32)));
        i.push(Operand::Count(b as i64));
        i.push(Operand::Addr(target));
        return Some(i);
    }
    None
}

fn exception(w: u32, addr: Addr) -> Option<Insn> {
    let opc = bits(w, 23, 21);
    let ll = bits(w, 1, 0);
    let imm16 = bits(w, 20, 5) as i64;
    let (mnem, flow) = match (opc, ll) {
        (0b000, 0b01) => ("svc", Flow::Syscall),
        (0b000, 0b10) => ("hvc", Flow::Syscall),
        (0b000, 0b11) => ("smc", Flow::Syscall),
        (0b001, 0b00) => ("brk", Flow::Trap),
        (0b010, 0b00) => ("hlt", Flow::Trap),
        (0b101, 0b01) => ("dcps1", Flow::Trap),
        (0b101, 0b10) => ("dcps2", Flow::Trap),
        (0b101, 0b11) => ("dcps3", Flow::Trap),
        _ => return None,
    };
    let mut i = ins(addr, mnem, flow);
    i.push(Operand::Imm(imm16));
    Some(i)
}

fn system(w: u32, addr: Addr) -> Option<Insn> {
    // Hint space: NOP and the pointer-authentication hints.
    if bits(w, 31, 12) == 0b1101_0101_0000_0011_0010 && bits(w, 4, 0) == 0b11111 {
        let crm = bits(w, 11, 8);
        let op2 = bits(w, 7, 5);
        let hint = (crm << 3) | op2;
        let mnem = match hint {
            0 => "nop",
            1 => "yield",
            2 => "wfe",
            3 => "wfi",
            4 => "sev",
            5 => "sevl",
            7 => "xpaclri",
            8 => "pacia1716",
            10 => "pacib1716",
            12 => "autia1716",
            14 => "autib1716",
            24 => "paciaz",
            25 => "paciasp",
            26 => "pacibz",
            27 => "pacibsp",
            28 => "autiaz",
            29 => "autiasp",
            30 => "autibz",
            31 => "autibsp",
            32 | 34 | 36 | 38 => "bti",
            _ => "hint",
        };
        let mut i = ins(addr, mnem, Flow::Next);
        if mnem == "hint" {
            i.push(Operand::Imm(hint as i64));
        } else if mnem == "bti" {
            i.push(Operand::Name(match op2 {
                2 => "c",
                4 => "j",
                6 => "jc",
                _ => "",
            }));
        }
        return Some(i);
    }
    // Barriers.
    if bits(w, 31, 12) == 0b1101_0101_0000_0011_0011 {
        let crm = bits(w, 11, 8);
        let mnem = match bits(w, 7, 5) {
            0b010 => "clrex",
            0b100 => "dsb",
            0b101 => "dmb",
            0b110 => "isb",
            0b111 => "sb",
            _ => return None,
        };
        let mut i = ins(addr, mnem, Flow::Next);
        if mnem != "sb" && mnem != "clrex" {
            i.push(Operand::Name(BARRIERS[crm as usize]));
        }
        return Some(i);
    }
    // MSR immediate to a pstate field.
    if bits(w, 31, 19) == 0b1101_0101_0000_0 && bits(w, 4, 0) == 0b11111 {
        let op1 = bits(w, 18, 16);
        let op2 = bits(w, 7, 5);
        let crm = bits(w, 11, 8);
        // SMSTART and SMSTOP are PSTATE writes with their own spelling.
        if op1 == 0b011 && op2 == 0b011 {
            let start = crm & 1 == 1;
            let mut i = ins(addr, if start { "smstart" } else { "smstop" }, Flow::Next);
            match crm >> 1 {
                0b001 => i.push(Operand::Name("sm")),
                0b010 => i.push(Operand::Name("za")),
                _ => &mut i,
            };
            return Some(i);
        }
        let mut i = ins(addr, "msr", Flow::Next);
        i.push(Operand::Name(pstate_name(op1, op2)));
        i.push(Operand::Imm(crm as i64));
        return Some(i);
    }
    // SYS and SYSL: cache, TLB and address translation maintenance, which
    // assemblers spell as DC, IC, AT and TLBI.
    if bits(w, 31, 22) == 0b1101_0101_00 && bits(w, 20, 19) == 0b01 {
        let op1 = bits(w, 18, 16);
        let crn = bits(w, 15, 12);
        let crm = bits(w, 11, 8);
        let op2 = bits(w, 7, 5);
        let rt = bits(w, 4, 0);
        if let Some((mnem, arg)) = sys_alias(op1, crn, crm, op2) {
            let mut i = ins(addr, mnem, Flow::Next);
            i.push(Operand::Name(arg));
            i.push(Operand::Reg(r(rt, true)));
            return Some(i);
        }
        let mut i = ins(
            addr,
            if bit(w, 21) == 1 { "sysl" } else { "sys" },
            Flow::Next,
        );
        i.push(Operand::Count(op1 as i64));
        i.push(Operand::Sys(0x1_0000 | crn));
        i.push(Operand::Sys(0x2_0000 | crm));
        i.push(Operand::Count(op2 as i64));
        i.push(Operand::Reg(r(rt, true)));
        return Some(i);
    }

    // MRS and MSR register. Bit 21 is L, and it alone gives the direction.
    if bits(w, 31, 22) == 0b1101_0101_00 {
        let read = bit(w, 21) == 1;
        let sysreg = bits(w, 20, 5);
        let rt = bits(w, 4, 0);
        let mut i = ins(addr, if read { "mrs" } else { "msr" }, Flow::Next);
        if read {
            i.push(Operand::Reg(r(rt, true)));
            i.push(Operand::Sys(sysreg));
        } else {
            i.push(Operand::Sys(sysreg));
            i.push(Operand::Reg(r(rt, true)));
        }
        return Some(i);
    }
    None
}

fn branch_register(w: u32, addr: Addr) -> Option<Insn> {
    let opc = bits(w, 24, 21);
    let op2 = bits(w, 20, 16);
    let op3 = bits(w, 15, 10);
    let rn = bits(w, 9, 5);
    let op4 = bits(w, 4, 0);
    if op2 != 0b11111 {
        return None;
    }

    // Pointer-authenticated forms carry a modifier in op3.
    let authed = op3 & 0b111110 == 0b000010;
    match (opc, op3, op4) {
        (0b0000, 0, 0) => {
            let mut i = ins(addr, "br", Flow::IndirectBranch);
            i.push(Operand::Reg(r(rn, true)));
            Some(i)
        }
        (0b0001, 0, 0) => {
            let mut i = ins(addr, "blr", Flow::IndirectCall);
            i.push(Operand::Reg(r(rn, true)));
            Some(i)
        }
        (0b0010, 0, 0) => {
            let mut i = ins(addr, "ret", Flow::Return);
            // objdump prints the register only when it is not x30.
            if rn != 30 {
                i.push(Operand::Reg(r(rn, true)));
            }
            Some(i)
        }
        (0b0100, 0, 0) if rn == 31 => Some(ins(addr, "eret", Flow::Return)),
        (0b0101, 0, 0) if rn == 31 => Some(ins(addr, "drps", Flow::Trap)),
        (0b0000, _, _) if authed => {
            let mut i = ins(
                addr,
                if bit(w, 10) == 1 { "braa" } else { "braaz" },
                Flow::IndirectBranch,
            );
            i.push(Operand::Reg(r(rn, true)));
            Some(i)
        }
        (0b0001, _, _) if authed => {
            let mut i = ins(
                addr,
                if bit(w, 10) == 1 { "blraa" } else { "blraaz" },
                Flow::IndirectCall,
            );
            i.push(Operand::Reg(r(rn, true)));
            Some(i)
        }
        (0b0010, _, _) if authed => Some(ins(addr, "retaa", Flow::Return)),
        _ => None,
    }
}

// ----------------------------------------------------------- loads and stores

fn loads_stores(w: u32, addr: Addr) -> Option<Insn> {
    // Load register (literal): a pc-relative load, and the only load whose
    // target address analysis can resolve without dataflow.
    if bits(w, 29, 27) == 0b011 && bit(w, 25) == 0 && bits(w, 24, 24) == 0 {
        let opc = bits(w, 31, 30);
        let simd = bit(w, 26) == 1;
        let target = addr.wrapping_offset(sext(bits(w, 23, 5), 19) << 2);
        let rt = bits(w, 4, 0);
        let (mnem, reg) = match (opc, simd) {
            (0b00, false) => ("ldr", r(rt, false)),
            (0b01, false) => ("ldr", r(rt, true)),
            (0b10, false) => ("ldrsw", r(rt, true)),
            (0b11, false) => ("prfm", r(rt, true)),
            (0b00, true) => ("ldr", v(rt, Width::W32)),
            (0b01, true) => ("ldr", v(rt, Width::W64)),
            (0b10, true) => ("ldr", v(rt, Width::W128)),
            _ => return None,
        };
        let mut i = ins(addr, mnem, Flow::Next);
        if mnem == "prfm" {
            i.push(Operand::Name(prefetch_name(rt)));
        } else {
            i.push(Operand::Reg(reg));
        }
        i.push(Operand::Addr(target));
        return Some(i);
    }

    // Load/store pair, in its three addressing modes.
    if bits(w, 29, 27) == 0b101 {
        return load_store_pair(w, addr);
    }
    // Load/store register, all forms.
    if bits(w, 29, 27) == 0b111 {
        return load_store_reg(w, addr);
    }
    // Load/store exclusive.
    if bits(w, 29, 24) == 0b001000 {
        return load_store_exclusive(w, addr);
    }
    None
}

/// Element size and mnemonic base for a pair instruction.
fn pair_form(w: u32) -> Option<(Reg, Reg, u64, &'static str)> {
    let opc = bits(w, 31, 30);
    let simd = bit(w, 26) == 1;
    let load = bit(w, 22) == 1;
    let rt = bits(w, 4, 0);
    let rt2 = bits(w, 14, 10);
    let (a, b, size) = match (opc, simd) {
        (0b00, false) => (r(rt, false), r(rt2, false), 4),
        // opc 01 without SIMD is LDPSW when loading and STGP when storing.
        // LDPSW writes 64-bit registers but transfers 4 bytes; STGP scales by
        // the 16-byte tag granule.
        (0b01, false) => (r(rt, true), r(rt2, true), if load { 4 } else { 16 }),
        (0b10, false) => (r(rt, true), r(rt2, true), 8),
        (0b00, true) => (v(rt, Width::W32), v(rt2, Width::W32), 4),
        (0b01, true) => (v(rt, Width::W64), v(rt2, Width::W64), 8),
        (0b10, true) => (v(rt, Width::W128), v(rt2, Width::W128), 16),
        _ => return None,
    };
    let mnem = if opc == 0b01 && !simd {
        if load { "ldpsw" } else { "stgp" }
    } else if load {
        "ldp"
    } else {
        "stp"
    };
    Some((a, b, size, mnem))
}

fn load_store_pair(w: u32, addr: Addr) -> Option<Insn> {
    let (rt, rt2, size, mnem) = pair_form(w)?;
    let mode = match bits(w, 24, 23) {
        0b00 => AddrMode::Offset, // no-allocate, printed the same
        0b01 => AddrMode::PostIndex,
        0b10 => AddrMode::Offset,
        0b11 => AddrMode::PreIndex,
        _ => return None,
    };
    let mnem = if bits(w, 24, 23) == 0b00 {
        if mnem == "ldp" { "ldnp" } else { "stnp" }
    } else {
        mnem
    };
    let imm7 = sext(bits(w, 21, 15), 7) * size as i64;
    let mut i = ins(addr, mnem, Flow::Next);
    i.push(Operand::Reg(rt));
    i.push(Operand::Reg(rt2));
    i.push(Operand::Mem(Mem {
        seg: None,
        base: Some(rsp(bits(w, 9, 5), true)),
        index: None,
        disp: imm7,
        mode,
        size: size * 2,
    }));
    Some(i)
}

/// Mnemonic and transfer size for a scalar load or store.
fn reg_form(size: u32, opc: u32, simd: bool, rt: u32) -> Option<(&'static str, Reg, u64)> {
    if simd {
        let width = match (size, bit_of(opc, 1)) {
            (0b00, 0) => Width::W8,
            (0b01, 0) => Width::W16,
            (0b10, 0) => Width::W32,
            (0b11, 0) => Width::W64,
            (0b00, 1) => Width::W128,
            _ => return None,
        };
        let load = opc & 1 == 1;
        return Some((
            if load { "ldr" } else { "str" },
            v(rt, width),
            width.bytes(),
        ));
    }
    Some(match (size, opc) {
        (0b00, 0b00) => ("strb", r(rt, false), 1),
        (0b00, 0b01) => ("ldrb", r(rt, false), 1),
        (0b00, 0b10) => ("ldrsb", r(rt, true), 1),
        (0b00, 0b11) => ("ldrsb", r(rt, false), 1),
        (0b01, 0b00) => ("strh", r(rt, false), 2),
        (0b01, 0b01) => ("ldrh", r(rt, false), 2),
        (0b01, 0b10) => ("ldrsh", r(rt, true), 2),
        (0b01, 0b11) => ("ldrsh", r(rt, false), 2),
        (0b10, 0b00) => ("str", r(rt, false), 4),
        (0b10, 0b01) => ("ldr", r(rt, false), 4),
        (0b10, 0b10) => ("ldrsw", r(rt, true), 4),
        (0b11, 0b00) => ("str", r(rt, true), 8),
        (0b11, 0b01) => ("ldr", r(rt, true), 8),
        (0b11, 0b10) => ("prfm", r(rt, true), 8),
        _ => return None,
    })
}

#[inline]
const fn bit_of(v: u32, n: u32) -> u32 {
    (v >> n) & 1
}

fn load_store_reg(w: u32, addr: Addr) -> Option<Insn> {
    let size = bits(w, 31, 30);
    let simd = bit(w, 26) == 1;
    let opc = bits(w, 23, 22);
    let rt = bits(w, 4, 0);
    let rn = bits(w, 9, 5);
    let (mnem, reg, xfer) = reg_form(size, opc, simd, rt)?;

    // Unsigned immediate offset, the common form.
    if bit(w, 24) == 1 {
        let imm = (bits(w, 21, 10) as i64) * xfer as i64;
        let mut i = ins(addr, mnem, Flow::Next);
        if mnem == "prfm" {
            i.push(Operand::Name(prefetch_name(rt)));
        } else {
            i.push(Operand::Reg(reg));
        }
        i.push(Operand::Mem(Mem {
            seg: None,
            base: Some(rsp(rn, true)),
            index: None,
            disp: imm,
            mode: AddrMode::Offset,
            size: xfer,
        }));
        return Some(i);
    }

    // Atomic memory operations share the register-offset slot, distinguished
    // by bit 21. Without this they decode as LDUR/STUR of the wrong register.
    if bit(w, 21) == 1 && bits(w, 11, 10) == 0 && !simd {
        return atomic_memory(w, addr);
    }
    // LDRAA and LDRAB: authenticated loads with a scaled 10-bit offset.
    if size == 0b11 && !simd && bit(w, 21) == 1 && bit(w, 10) == 1 {
        let offset = sext((bit(w, 22) << 9) | bits(w, 20, 12), 10) * 8;
        let writeback = bit(w, 11) == 1;
        let mut i = ins(
            addr,
            if bit(w, 23) == 1 { "ldrab" } else { "ldraa" },
            Flow::Next,
        );
        i.push(Operand::Reg(r(rt, true)));
        i.push(Operand::Mem(Mem {
            seg: None,
            base: Some(rsp(rn, true)),
            index: None,
            disp: offset,
            mode: if writeback {
                AddrMode::PreIndex
            } else {
                AddrMode::Offset
            },
            size: 8,
        }));
        return Some(i);
    }

    let imm9 = sext(bits(w, 20, 12), 9);
    match bits(w, 11, 10) {
        // Unscaled immediate: LDUR and friends.
        0b00 => {
            let unscaled: &'static str = match mnem {
                "ldr" => "ldur",
                "str" => "stur",
                "ldrb" => "ldurb",
                "strb" => "sturb",
                "ldrh" => "ldurh",
                "strh" => "sturh",
                "ldrsb" => "ldursb",
                "ldrsh" => "ldursh",
                "ldrsw" => "ldursw",
                "prfm" => "prfum",
                other => other,
            };
            let mut i = ins(addr, unscaled, Flow::Next);
            if unscaled == "prfum" {
                i.push(Operand::Name(prefetch_name(rt)));
            } else {
                i.push(Operand::Reg(reg));
            }
            i.push(Operand::Mem(Mem {
                seg: None,
                base: Some(rsp(rn, true)),
                index: None,
                disp: imm9,
                mode: AddrMode::Offset,
                size: xfer,
            }));
            Some(i)
        }
        0b01 | 0b11 => {
            let mode = if bits(w, 11, 10) == 0b01 {
                AddrMode::PostIndex
            } else {
                AddrMode::PreIndex
            };
            let mut i = ins(addr, mnem, Flow::Next);
            i.push(Operand::Reg(reg));
            i.push(Operand::Mem(Mem {
                seg: None,
                base: Some(rsp(rn, true)),
                index: None,
                disp: imm9,
                mode,
                size: xfer,
            }));
            Some(i)
        }
        // Unprivileged access: the register-offset slot with bit 21 clear.
        0b10 if bit(w, 21) == 0 => {
            let unpriv: &'static str = match mnem {
                "ldr" => "ldtr",
                "str" => "sttr",
                "ldrb" => "ldtrb",
                "strb" => "sttrb",
                "ldrh" => "ldtrh",
                "strh" => "sttrh",
                "ldrsb" => "ldtrsb",
                "ldrsh" => "ldtrsh",
                "ldrsw" => "ldtrsw",
                other => other,
            };
            let mut i = ins(addr, unpriv, Flow::Next);
            i.push(Operand::Reg(reg));
            i.push(Operand::Mem(Mem {
                seg: None,
                base: Some(rsp(rn, true)),
                index: None,
                disp: imm9,
                mode: AddrMode::Offset,
                size: xfer,
            }));
            Some(i)
        }
        // Register offset.
        0b10 => {
            let option = bits(w, 15, 13);
            let s = bit(w, 12);
            let rm = bits(w, 20, 16);
            let extend = match option {
                0b010 => Extend::Uxtw,
                0b011 => Extend::Lsl,
                0b110 => Extend::Sxtw,
                0b111 => Extend::Sxtx,
                _ => return None,
            };
            // With S set objdump prints the shift even when it is zero,
            // which for a byte access it always is.
            let amount = if s == 1 {
                xfer.trailing_zeros() as u8
            } else {
                0
            };
            let explicit_zero_shift = s == 1 && amount == 0 && extend == Extend::Lsl;
            let index_wide = matches!(extend, Extend::Lsl | Extend::Sxtx);
            let mut i = ins(addr, mnem, Flow::Next);
            if mnem == "prfm" {
                i.push(Operand::Name(prefetch_name(rt)));
            } else {
                i.push(Operand::Reg(reg));
            }
            i.push(Operand::Mem(Mem {
                seg: None,
                base: Some(rsp(rn, true)),
                index: Some((
                    r(rm, index_wide),
                    if explicit_zero_shift {
                        Extend::LslZero
                    } else {
                        extend
                    },
                    amount,
                )),
                disp: 0,
                mode: AddrMode::Offset,
                size: xfer,
            }));
            Some(i)
        }
        _ => None,
    }
}

/// Atomic compare-and-swap, which shares the exclusive group's encoding space.
fn compare_and_swap(w: u32, addr: Addr) -> Option<Insn> {
    let size = bits(w, 31, 30);
    if bits(w, 14, 10) != 0b11111 {
        return None;
    }
    let sf = size == 0b11;
    let acquire = bit(w, 22) == 1;
    let release = bit(w, 15) == 1;
    let mnem: &'static str = match (acquire, release, size) {
        (false, false, 0b00) => "casb",
        (false, true, 0b00) => "caslb",
        (true, false, 0b00) => "casab",
        (true, true, 0b00) => "casalb",
        (false, false, 0b01) => "cash",
        (false, true, 0b01) => "caslh",
        (true, false, 0b01) => "casah",
        (true, true, 0b01) => "casalh",
        (false, false, _) => "cas",
        (false, true, _) => "casl",
        (true, false, _) => "casa",
        (true, true, _) => "casal",
    };
    let narrow = size < 0b10;
    let width = sf && !narrow;
    let mut i = ins(addr, mnem, Flow::Next);
    i.push(Operand::Reg(r(bits(w, 20, 16), width)));
    i.push(Operand::Reg(r(bits(w, 4, 0), width)));
    i.push(Operand::Mem(Mem {
        seg: None,
        base: Some(rsp(bits(w, 9, 5), true)),
        index: None,
        disp: 0,
        mode: AddrMode::Offset,
        size: 1u64 << size,
    }));
    Some(i)
}

/// LDADD and the rest of the atomic read-modify-write family, plus SWP.
fn atomic_memory(w: u32, addr: Addr) -> Option<Insn> {
    let size = bits(w, 31, 30);
    let a = bit(w, 23) == 1;
    let rl = bit(w, 22) == 1;
    let o3 = bit(w, 15) == 1;
    let opc = bits(w, 14, 12);
    let rs = bits(w, 20, 16);
    let rt = bits(w, 4, 0);
    let rn = bits(w, 9, 5);
    let sf = size == 0b11;
    let narrow = match size {
        0b00 => Some("b"),
        0b01 => Some("h"),
        _ => None,
    };

    // LDAPR is the one o3 form that takes no source register.
    if o3 && opc == 0b100 {
        if rs != 31 {
            return None;
        }
        let mnem: &'static str = match narrow {
            Some("b") => "ldaprb",
            Some("h") => "ldaprh",
            _ => "ldapr",
        };
        let mut i = ins(addr, mnem, Flow::Next);
        i.push(Operand::Reg(r(rt, sf)));
        i.push(Operand::Mem(Mem {
            seg: None,
            base: Some(rsp(rn, true)),
            index: None,
            disp: 0,
            mode: AddrMode::Offset,
            size: 1u64 << size,
        }));
        return Some(i);
    }

    let base: &'static str = if o3 {
        if opc != 0 {
            return None;
        }
        "swp"
    } else {
        match opc {
            0b000 => "ldadd",
            0b001 => "ldclr",
            0b010 => "ldeor",
            0b011 => "ldset",
            0b100 => "ldsmax",
            0b101 => "ldsmin",
            0b110 => "ldumax",
            _ => "ldumin",
        }
    };
    // Discarding the loaded value has an ST alias, which is how a compiler
    // spells an atomic increment whose old value nobody wants.
    let store_alias = !o3 && rt == 31 && !a;
    let mnem = atomic_mnemonic(base, store_alias, a, rl, narrow)?;

    let mut i = ins(addr, mnem, Flow::Next);
    i.push(Operand::Reg(r(rs, sf)));
    if !store_alias {
        i.push(Operand::Reg(r(rt, sf)));
    }
    i.push(Operand::Mem(Mem {
        seg: None,
        base: Some(rsp(rn, true)),
        index: None,
        disp: 0,
        mode: AddrMode::Offset,
        size: 1u64 << size,
    }));
    Some(i)
}

/// Assemble an atomic mnemonic from its parts. Every combination is a distinct
/// static string, so [`Insn`] stays `Copy` and allocation-free.
fn atomic_mnemonic(
    base: &'static str,
    store: bool,
    acquire: bool,
    release: bool,
    narrow: Option<&'static str>,
) -> Option<&'static str> {
    macro_rules! table {
        ($($b:literal),* $(,)?) => {
            match (base, store, acquire, release, narrow) {
                $(
                    ($b, false, false, false, None) => Some(concat!($b)),
                    ($b, false, false, true, None) => Some(concat!($b, "l")),
                    ($b, false, true, false, None) => Some(concat!($b, "a")),
                    ($b, false, true, true, None) => Some(concat!($b, "al")),
                    ($b, false, false, false, Some("b")) => Some(concat!($b, "b")),
                    ($b, false, false, true, Some("b")) => Some(concat!($b, "lb")),
                    ($b, false, true, false, Some("b")) => Some(concat!($b, "ab")),
                    ($b, false, true, true, Some("b")) => Some(concat!($b, "alb")),
                    ($b, false, false, false, Some("h")) => Some(concat!($b, "h")),
                    ($b, false, false, true, Some("h")) => Some(concat!($b, "lh")),
                    ($b, false, true, false, Some("h")) => Some(concat!($b, "ah")),
                    ($b, false, true, true, Some("h")) => Some(concat!($b, "alh")),
                )*
                _ => None,
            }
        };
    }
    if store {
        // st<op>[l][b|h]: the alias drops the leading `ld`.
        let short = base.strip_prefix("ld")?;
        return match (short, release, narrow) {
            ("add", false, None) => Some("stadd"),
            ("add", true, None) => Some("staddl"),
            ("add", false, Some("b")) => Some("staddb"),
            ("add", true, Some("b")) => Some("staddlb"),
            ("add", false, Some("h")) => Some("staddh"),
            ("add", true, Some("h")) => Some("staddlh"),
            ("clr", false, None) => Some("stclr"),
            ("clr", true, None) => Some("stclrl"),
            ("eor", false, None) => Some("steor"),
            ("eor", true, None) => Some("steorl"),
            ("set", false, None) => Some("stset"),
            ("set", true, None) => Some("stsetl"),
            ("smax", false, None) => Some("stsmax"),
            ("smax", true, None) => Some("stsmaxl"),
            ("smin", false, None) => Some("stsmin"),
            ("smin", true, None) => Some("stsminl"),
            ("umax", false, None) => Some("stumax"),
            ("umax", true, None) => Some("stumaxl"),
            ("umin", false, None) => Some("stumin"),
            ("umin", true, None) => Some("stuminl"),
            _ => None,
        };
    }
    table!(
        "ldadd", "ldclr", "ldeor", "ldset", "ldsmax", "ldsmin", "ldumax", "ldumin", "swp"
    )
}

fn load_store_exclusive(w: u32, addr: Addr) -> Option<Insn> {
    // o2 and o1 together mean compare-and-swap rather than exclusive access.
    if bit(w, 23) == 1 && bit(w, 21) == 1 {
        return compare_and_swap(w, addr);
    }
    let size = bits(w, 31, 30);
    let load = bit(w, 22) == 1;
    let pair = bit(w, 21) == 1;
    let o0 = bit(w, 15);
    let rt = bits(w, 4, 0);
    let rn = bits(w, 9, 5);
    let rs = bits(w, 20, 16);
    let rt2 = bits(w, 14, 10);
    let sf = size == 0b11;
    let xfer = 1u64 << size;

    let suffix = match size {
        0b00 => "b",
        0b01 => "h",
        _ => "",
    };
    // Ordered accesses with no status register: LDAR/STLR, or the limited
    // ordering LDLAR/STLLR when o0 is clear.
    if !pair && bit(w, 23) == 1 {
        let mnem: &'static str = match (load, o0, suffix) {
            (true, 1, "b") => "ldarb",
            (true, 1, "h") => "ldarh",
            (true, 1, _) => "ldar",
            (false, 1, "b") => "stlrb",
            (false, 1, "h") => "stlrh",
            (false, 1, _) => "stlr",
            (true, _, "b") => "ldlarb",
            (true, _, "h") => "ldlarh",
            (true, _, _) => "ldlar",
            (false, _, "b") => "stllrb",
            (false, _, "h") => "stllrh",
            (false, _, _) => "stllr",
        };
        let mut i = ins(addr, mnem, Flow::Next);
        i.push(Operand::Reg(r(rt, sf)));
        i.push(Operand::Mem(Mem {
            seg: None,
            base: Some(rsp(rn, true)),
            index: None,
            disp: 0,
            mode: AddrMode::Offset,
            size: xfer,
        }));
        return Some(i);
    }

    let mnem: &'static str = match (load, pair, o0, suffix) {
        (true, false, 0, "b") => "ldxrb",
        (true, false, 0, "h") => "ldxrh",
        (true, false, 0, _) => "ldxr",
        (true, false, 1, "b") => "ldaxrb",
        (true, false, 1, "h") => "ldaxrh",
        (true, false, 1, _) => "ldaxr",
        (false, false, 0, "b") => "stxrb",
        (false, false, 0, "h") => "stxrh",
        (false, false, 0, _) => "stxr",
        (false, false, 1, "b") => "stlxrb",
        (false, false, 1, "h") => "stlxrh",
        (false, false, 1, _) => "stlxr",
        (true, true, 0, _) => "ldxp",
        (true, true, 1, _) => "ldaxp",
        (false, true, 0, _) => "stxp",
        (false, true, 1, _) => "stlxp",
        _ => return None,
    };
    let mut i = ins(addr, mnem, Flow::Next);
    if !load {
        i.push(Operand::Reg(r(rs, false)));
    }
    i.push(Operand::Reg(r(rt, sf)));
    if pair {
        i.push(Operand::Reg(r(rt2, sf)));
    }
    i.push(Operand::Mem(Mem {
        seg: None,
        base: Some(rsp(rn, true)),
        index: None,
        disp: 0,
        mode: AddrMode::Offset,
        size: if pair { xfer * 2 } else { xfer },
    }));
    Some(i)
}

// ------------------------------------------------------- register arithmetic

fn dp_register(w: u32, addr: Addr) -> Option<Insn> {
    let op0 = bit(w, 30);
    let op1 = bit(w, 28);
    let op2 = bits(w, 24, 21);

    if op1 == 1 {
        return match op2 {
            0b0000 if bits(w, 15, 10) == 0 => add_sub_carry(w, addr),
            0b0010 if bit(w, 11) == 0 => cond_compare(w, addr, false),
            0b0010 if bit(w, 11) == 1 => cond_compare(w, addr, true),
            0b0100 => cond_select(w, addr),
            0b0110 => {
                if op0 == 1 {
                    dp_1source(w, addr)
                } else {
                    dp_2source(w, addr)
                }
            }
            0b1000..=0b1111 => dp_3source(w, addr),
            _ => None,
        };
    }
    // Logical and arithmetic, shifted or extended register.
    if bits(w, 28, 24) == 0b01010 {
        return logical_shifted(w, addr);
    }
    if bits(w, 28, 24) == 0b01011 {
        if bit(w, 21) == 1 {
            return add_sub_extended(w, addr);
        }
        return add_sub_shifted(w, addr);
    }
    None
}

fn shift_kind(v: u32) -> Option<Shift> {
    Some(match v {
        0b00 => Shift::Lsl,
        0b01 => Shift::Lsr,
        0b10 => Shift::Asr,
        0b11 => Shift::Ror,
        _ => return None,
    })
}

fn logical_shifted(w: u32, addr: Addr) -> Option<Insn> {
    let sf = bit(w, 31) == 1;
    let opc = bits(w, 30, 29);
    let n = bit(w, 21);
    let shift = shift_kind(bits(w, 23, 22))?;
    let amount = bits(w, 15, 10);
    if !sf && amount >= 32 {
        return None;
    }
    let rd = bits(w, 4, 0);
    let rn = bits(w, 9, 5);
    let rm = bits(w, 20, 16);

    // ORR from zr with no shift is MOV; ANDS to zr is TST; ORN from zr is MVN.
    if opc == 0b01 && n == 0 && rn == 31 && amount == 0 && shift == Shift::Lsl {
        let mut i = ins(addr, "mov", Flow::Next);
        i.push(Operand::Reg(r(rd, sf)));
        i.push(Operand::Reg(r(rm, sf)));
        return Some(i);
    }
    if opc == 0b01 && n == 1 && rn == 31 {
        let mut i = ins(addr, "mvn", Flow::Next);
        i.push(Operand::Reg(r(rd, sf)));
        push_shifted(&mut i, r(rm, sf), shift, amount);
        return Some(i);
    }
    if opc == 0b11 && n == 0 && rd == 31 {
        let mut i = ins(addr, "tst", Flow::Next);
        i.push(Operand::Reg(r(rn, sf)));
        push_shifted(&mut i, r(rm, sf), shift, amount);
        return Some(i);
    }

    let mnem = match (opc, n) {
        (0b00, 0) => "and",
        (0b00, 1) => "bic",
        (0b01, 0) => "orr",
        (0b01, 1) => "orn",
        (0b10, 0) => "eor",
        (0b10, 1) => "eon",
        (0b11, 0) => "ands",
        _ => "bics",
    };
    let mut i = ins(addr, mnem, Flow::Next);
    i.push(Operand::Reg(r(rd, sf)));
    i.push(Operand::Reg(r(rn, sf)));
    push_shifted(&mut i, r(rm, sf), shift, amount);
    Some(i)
}

fn push_shifted(i: &mut Insn, reg: Reg, shift: Shift, amount: u32) {
    if amount == 0 && shift == Shift::Lsl {
        i.push(Operand::Reg(reg));
    } else {
        i.push(Operand::Shifted(reg, shift, amount as u8));
    }
}

fn add_sub_shifted(w: u32, addr: Addr) -> Option<Insn> {
    let sf = bit(w, 31) == 1;
    let sub = bit(w, 30) == 1;
    let setflags = bit(w, 29) == 1;
    let shift = shift_kind(bits(w, 23, 22))?;
    if shift == Shift::Ror {
        return None;
    }
    let amount = bits(w, 15, 10);
    if !sf && amount >= 32 {
        return None;
    }
    let rd = bits(w, 4, 0);
    let rn = bits(w, 9, 5);
    let rm = bits(w, 20, 16);

    if setflags && rd == 31 {
        let mut i = ins(addr, if sub { "cmp" } else { "cmn" }, Flow::Next);
        i.push(Operand::Reg(r(rn, sf)));
        push_shifted(&mut i, r(rm, sf), shift, amount);
        return Some(i);
    }
    if sub && rn == 31 {
        let mut i = ins(addr, if setflags { "negs" } else { "neg" }, Flow::Next);
        i.push(Operand::Reg(r(rd, sf)));
        push_shifted(&mut i, r(rm, sf), shift, amount);
        return Some(i);
    }

    let mnem = match (sub, setflags) {
        (false, false) => "add",
        (false, true) => "adds",
        (true, false) => "sub",
        (true, true) => "subs",
    };
    let mut i = ins(addr, mnem, Flow::Next);
    i.push(Operand::Reg(r(rd, sf)));
    i.push(Operand::Reg(r(rn, sf)));
    push_shifted(&mut i, r(rm, sf), shift, amount);
    Some(i)
}

fn add_sub_extended(w: u32, addr: Addr) -> Option<Insn> {
    let sf = bit(w, 31) == 1;
    let sub = bit(w, 30) == 1;
    let setflags = bit(w, 29) == 1;
    if bits(w, 23, 22) != 0 {
        return None;
    }
    let option = bits(w, 15, 13);
    let amount = bits(w, 12, 10);
    if amount > 4 {
        return None;
    }
    let extend = match option {
        0 => Extend::Uxtb,
        1 => Extend::Uxth,
        2 => Extend::Uxtw,
        3 => Extend::Uxtx,
        4 => Extend::Sxtb,
        5 => Extend::Sxth,
        6 => Extend::Sxtw,
        _ => Extend::Sxtx,
    };
    let rd = bits(w, 4, 0);
    let rn = bits(w, 9, 5);
    let rm = bits(w, 20, 16);
    // The operand register is 64-bit only for the x-extending options.
    // objdump keeps the operand at the instruction's own width; only the
    // 64-bit variant names an X register for the x-extending options.
    let rm_wide = sf && matches!(extend, Extend::Uxtx | Extend::Sxtx);
    // UXTX (64-bit) and UXTW (32-bit) print as LSL, but only when the
    // instruction actually involves SP; otherwise the extend is spelled out.
    let sp_involved = rd == 31 || rn == 31;
    let prints_lsl =
        sp_involved && ((sf && extend == Extend::Uxtx) || (!sf && extend == Extend::Uxtw));
    let shown = if prints_lsl { Extend::Lsl } else { extend };

    if setflags && rd == 31 {
        let mut i = ins(addr, if sub { "cmp" } else { "cmn" }, Flow::Next);
        i.push(Operand::Reg(rsp(rn, sf)));
        push_extended(&mut i, r(rm, rm_wide), shown, amount, prints_lsl);
        return Some(i);
    }

    let mnem = match (sub, setflags) {
        (false, false) => "add",
        (false, true) => "adds",
        (true, false) => "sub",
        (true, true) => "subs",
    };
    let mut i = ins(addr, mnem, Flow::Next);
    i.push(Operand::Reg(if setflags { r(rd, sf) } else { rsp(rd, sf) }));
    i.push(Operand::Reg(rsp(rn, sf)));
    push_extended(&mut i, r(rm, rm_wide), shown, amount, prints_lsl);
    Some(i)
}

fn push_extended(i: &mut Insn, reg: Reg, extend: Extend, amount: u32, prints_lsl: bool) {
    if amount == 0 && prints_lsl {
        i.push(Operand::Reg(reg));
    } else {
        i.push(Operand::Extended(reg, extend, amount as u8));
    }
}

fn add_sub_carry(w: u32, addr: Addr) -> Option<Insn> {
    let sf = bit(w, 31) == 1;
    let sub = bit(w, 30) == 1;
    let setflags = bit(w, 29) == 1;
    let rd = bits(w, 4, 0);
    let rn = bits(w, 9, 5);
    let rm = bits(w, 20, 16);
    if sub && rn == 31 {
        let mut i = ins(addr, if setflags { "ngcs" } else { "ngc" }, Flow::Next);
        i.push(Operand::Reg(r(rd, sf)));
        i.push(Operand::Reg(r(rm, sf)));
        return Some(i);
    }
    let mnem = match (sub, setflags) {
        (false, false) => "adc",
        (false, true) => "adcs",
        (true, false) => "sbc",
        (true, true) => "sbcs",
    };
    let mut i = ins(addr, mnem, Flow::Next);
    i.push(Operand::Reg(r(rd, sf)));
    i.push(Operand::Reg(r(rn, sf)));
    i.push(Operand::Reg(r(rm, sf)));
    Some(i)
}

fn cond_compare(w: u32, addr: Addr, imm_form: bool) -> Option<Insn> {
    let sf = bit(w, 31) == 1;
    let sub = bit(w, 30) == 1;
    if bit(w, 29) != 1 || bit(w, 4) != 0 || bit(w, 10) != 0 {
        return None;
    }
    let mut i = ins(addr, if sub { "ccmp" } else { "ccmn" }, Flow::Next);
    i.push(Operand::Reg(r(bits(w, 9, 5), sf)));
    if imm_form {
        i.push(Operand::Imm(bits(w, 20, 16) as i64));
    } else {
        i.push(Operand::Reg(r(bits(w, 20, 16), sf)));
    }
    i.push(Operand::Imm(bits(w, 3, 0) as i64));
    i.push(Operand::Cond(Cond(bits(w, 15, 12) as u8)));
    Some(i)
}

fn cond_select(w: u32, addr: Addr) -> Option<Insn> {
    let sf = bit(w, 31) == 1;
    let op = bit(w, 30);
    let o2 = bit(w, 10);
    if bit(w, 29) != 0 {
        return None;
    }
    let rd = bits(w, 4, 0);
    let rn = bits(w, 9, 5);
    let rm = bits(w, 20, 16);
    let cond = bits(w, 15, 12);

    // CSINC/CSINV/CSNEG with both sources zr and an invertible condition are
    // the cset family, which is how a compiler materializes a boolean.
    let invertible = cond != 0b1110 && cond != 0b1111;
    if rn == 31 && rm == 31 && invertible {
        let mnem = match (op, o2) {
            (0, 1) => Some("cset"),
            (1, 0) => Some("csetm"),
            _ => None,
        };
        if let Some(m) = mnem {
            let mut i = ins(addr, m, Flow::Next);
            i.push(Operand::Reg(r(rd, sf)));
            i.push(Operand::Cond(Cond((cond ^ 1) as u8)));
            return Some(i);
        }
    }
    if rn == rm && rn != 31 && invertible {
        let mnem = match (op, o2) {
            (0, 1) => Some("cinc"),
            (1, 0) => Some("cinv"),
            (1, 1) => Some("cneg"),
            _ => None,
        };
        if let Some(m) = mnem {
            let mut i = ins(addr, m, Flow::Next);
            i.push(Operand::Reg(r(rd, sf)));
            i.push(Operand::Reg(r(rn, sf)));
            i.push(Operand::Cond(Cond((cond ^ 1) as u8)));
            return Some(i);
        }
    }

    let mnem = match (op, o2) {
        (0, 0) => "csel",
        (0, 1) => "csinc",
        (1, 0) => "csinv",
        _ => "csneg",
    };
    let mut i = ins(addr, mnem, Flow::Next);
    i.push(Operand::Reg(r(rd, sf)));
    i.push(Operand::Reg(r(rn, sf)));
    i.push(Operand::Reg(r(rm, sf)));
    i.push(Operand::Cond(Cond(cond as u8)));
    Some(i)
}

fn dp_1source(w: u32, addr: Addr) -> Option<Insn> {
    let sf = bit(w, 31) == 1;
    if bit(w, 29) != 0 {
        return None;
    }
    let opcode2 = bits(w, 20, 16);
    let opcode = bits(w, 15, 10);
    let rd = bits(w, 4, 0);
    let rn = bits(w, 9, 5);
    if opcode2 != 0 {
        return None;
    }
    let mnem = match opcode {
        0b000000 => "rbit",
        0b000001 => "rev16",
        0b000010 => {
            if sf {
                "rev32"
            } else {
                "rev"
            }
        }
        0b000011 if sf => "rev",
        0b000100 => "clz",
        0b000101 => "cls",
        _ => return None,
    };
    let mut i = ins(addr, mnem, Flow::Next);
    i.push(Operand::Reg(r(rd, sf)));
    i.push(Operand::Reg(r(rn, sf)));
    Some(i)
}

fn dp_2source(w: u32, addr: Addr) -> Option<Insn> {
    let sf = bit(w, 31) == 1;
    if bit(w, 29) != 0 {
        return None;
    }
    let opcode = bits(w, 15, 10);
    let rd = bits(w, 4, 0);
    let rn = bits(w, 9, 5);
    let rm = bits(w, 20, 16);
    let mnem = match opcode {
        0b000010 => "udiv",
        0b000011 => "sdiv",
        0b001000 => "lslv",
        0b001001 => "lsrv",
        0b001010 => "asrv",
        0b001011 => "rorv",
        0b010000 => "crc32b",
        0b010001 => "crc32h",
        0b010010 => "crc32w",
        0b010011 => "crc32x",
        0b010100 => "crc32cb",
        0b010101 => "crc32ch",
        0b010110 => "crc32cw",
        0b010111 => "crc32cx",
        _ => return None,
    };
    // objdump prints the variable shifts without the trailing v.
    let shown: &'static str = match mnem {
        "lslv" => "lsl",
        "lsrv" => "lsr",
        "asrv" => "asr",
        "rorv" => "ror",
        other => other,
    };
    let mut i = ins(addr, shown, Flow::Next);
    i.push(Operand::Reg(r(rd, sf)));
    i.push(Operand::Reg(r(rn, sf)));
    i.push(Operand::Reg(r(rm, sf)));
    Some(i)
}

fn dp_3source(w: u32, addr: Addr) -> Option<Insn> {
    let sf = bit(w, 31) == 1;
    if bits(w, 30, 29) != 0 {
        return None;
    }
    let op31 = bits(w, 23, 21);
    let o0 = bit(w, 15);
    let rd = bits(w, 4, 0);
    let rn = bits(w, 9, 5);
    let rm = bits(w, 20, 16);
    let ra = bits(w, 14, 10);

    let (mnem, wide_operands) = match (op31, o0, sf) {
        (0b000, 0, _) => ("madd", sf),
        (0b000, 1, _) => ("msub", sf),
        (0b001, 0, true) => ("smaddl", false),
        (0b001, 1, true) => ("smsubl", false),
        (0b010, 0, true) => ("smulh", true),
        (0b101, 0, true) => ("umaddl", false),
        (0b101, 1, true) => ("umsubl", false),
        (0b110, 0, true) => ("umulh", true),
        _ => return None,
    };

    // With a zero accumulator these are the multiply aliases.
    if ra == 31 {
        let alias: Option<&'static str> = match mnem {
            "madd" => Some("mul"),
            "msub" => Some("mneg"),
            "smaddl" => Some("smull"),
            "smsubl" => Some("smnegl"),
            "umaddl" => Some("umull"),
            "umsubl" => Some("umnegl"),
            _ => None,
        };
        if let Some(a) = alias {
            let mut i = ins(addr, a, Flow::Next);
            i.push(Operand::Reg(r(rd, sf)));
            i.push(Operand::Reg(r(rn, wide_operands)));
            i.push(Operand::Reg(r(rm, wide_operands)));
            return Some(i);
        }
    }

    let mut i = ins(addr, mnem, Flow::Next);
    i.push(Operand::Reg(r(rd, sf)));
    i.push(Operand::Reg(r(rn, wide_operands)));
    i.push(Operand::Reg(r(rm, wide_operands)));
    if mnem != "smulh" && mnem != "umulh" {
        i.push(Operand::Reg(r(ra, sf)));
    }
    Some(i)
}

// -------------------------------------------------------------- FP and SIMD

/// Expand an 8-bit FP immediate to a double, per `VFPExpandImm`.
///
/// The encoding is `sign : NOT(b6) : Replicate(b6, 8) : b5 b4 : frac`, which
/// covers the small set of constants a compiler materializes inline. Every
/// width expands to the same real value, so one double is enough.
pub(crate) fn vfp_expand_imm(imm8: u8) -> u64 {
    let sign = (imm8 >> 7) as u64 & 1;
    let b6 = (imm8 >> 6) as u64 & 1;
    let b54 = (imm8 >> 4) as u64 & 3;
    let frac = imm8 as u64 & 0xf;
    // 11-bit exponent: one inverted bit, eight copies, then two literal bits.
    let exp = ((1 - b6) << 10) | (if b6 == 1 { 0xffu64 } else { 0 } << 2) | b54;
    (sign << 63) | (exp << 52) | (frac << 48)
}

/// A deliberately shallow slice of the FP and SIMD space.
///
/// Enough to keep a listing readable and to keep the sweep aligned: scalar
/// moves, the FP arithmetic a compiler emits for `double`, and the compares.
/// Anything else returns `None` and prints as an unknown word, which is honest.
fn dp_simd(w: u32, addr: Addr) -> Option<Insn> {
    // Floating point data processing, three source: the fused multiply-adds.
    if bits(w, 31, 24) == 0b0001_1111 {
        let width = match bits(w, 23, 22) {
            0b00 => Width::W32,
            0b01 => Width::W64,
            0b11 => Width::W16,
            _ => return None,
        };
        let mnem = match (bit(w, 21), bit(w, 15)) {
            (0, 0) => "fmadd",
            (0, 1) => "fmsub",
            (1, 0) => "fnmadd",
            _ => "fnmsub",
        };
        let mut i = ins(addr, mnem, Flow::Next);
        i.push(Operand::Reg(v(bits(w, 4, 0), width)));
        i.push(Operand::Reg(v(bits(w, 9, 5), width)));
        i.push(Operand::Reg(v(bits(w, 20, 16), width)));
        i.push(Operand::Reg(v(bits(w, 14, 10), width)));
        return Some(i);
    }
    // Floating point data processing, one and two source.
    if bits(w, 31, 24) == 0b0001_1110 && bit(w, 21) == 1 {
        let ftype = bits(w, 23, 22);
        let width = match ftype {
            0b00 => Width::W32,
            0b01 => Width::W64,
            0b11 => Width::W16,
            _ => return None,
        };
        let rd = bits(w, 4, 0);
        let rn = bits(w, 9, 5);
        let rm = bits(w, 20, 16);

        // Two source.
        if bits(w, 11, 10) == 0b10 {
            let mnem = match bits(w, 15, 12) {
                0b0000 => "fmul",
                0b0001 => "fdiv",
                0b0010 => "fadd",
                0b0011 => "fsub",
                0b0100 => "fmax",
                0b0101 => "fmin",
                0b0110 => "fmaxnm",
                0b0111 => "fminnm",
                0b1000 => "fnmul",
                _ => return None,
            };
            let mut i = ins(addr, mnem, Flow::Next);
            i.push(Operand::Reg(v(rd, width)));
            i.push(Operand::Reg(v(rn, width)));
            i.push(Operand::Reg(v(rm, width)));
            return Some(i);
        }
        // Floating point immediate, which must be tried before the one-source
        // group because both have bit 12 clear.
        if bits(w, 12, 10) == 0b100 && bits(w, 9, 5) == 0 {
            let mut i = ins(addr, "fmov", Flow::Next);
            i.push(Operand::Reg(v(rd, width)));
            i.push(Operand::FpImm(vfp_expand_imm(bits(w, 20, 13) as u8)));
            return Some(i);
        }
        // Precision conversion, whose destination width differs from its
        // source width and so cannot share the one-source path.
        if bits(w, 14, 10) == 0b10000 && bits(w, 20, 17) == 0b0001 {
            let to = match bits(w, 16, 15) {
                0b00 => Width::W32,
                0b01 => Width::W64,
                0b11 => Width::W16,
                _ => return None,
            };
            if to == width {
                return None;
            }
            let mut i = ins(addr, "fcvt", Flow::Next);
            i.push(Operand::Reg(v(rd, to)));
            i.push(Operand::Reg(v(rn, width)));
            return Some(i);
        }
        // One source.
        if bits(w, 14, 10) == 0b10000 {
            let mnem = match bits(w, 20, 15) {
                0b000000 => "fmov",
                0b000001 => "fabs",
                0b000010 => "fneg",
                0b000011 => "fsqrt",
                0b001000 => "frintn",
                0b001001 => "frintp",
                0b001010 => "frintm",
                0b001011 => "frintz",
                0b001100 => "frinta",
                0b001110 => "frintx",
                0b001111 => "frinti",
                _ => return None,
            };
            let mut i = ins(addr, mnem, Flow::Next);
            i.push(Operand::Reg(v(rd, width)));
            i.push(Operand::Reg(v(rn, width)));
            return Some(i);
        }
        // Compare.
        if bits(w, 13, 10) == 0b1000 {
            let with_zero = bit(w, 3) == 1;
            let mnem = if bit(w, 4) == 1 { "fcmpe" } else { "fcmp" };
            let mut i = ins(addr, mnem, Flow::Next);
            i.push(Operand::Reg(v(rn, width)));
            if with_zero {
                i.push(Operand::Name("#0.0"));
            } else {
                i.push(Operand::Reg(v(rm, width)));
            }
            return Some(i);
        }
        // Conditional select.
        if bits(w, 11, 10) == 0b11 {
            let mut i = ins(addr, "fcsel", Flow::Next);
            i.push(Operand::Reg(v(rd, width)));
            i.push(Operand::Reg(v(rn, width)));
            i.push(Operand::Reg(v(rm, width)));
            i.push(Operand::Cond(Cond(bits(w, 15, 12) as u8)));
            return Some(i);
        }
    }

    // Advanced SIMD, which is most of this space.
    if let Some(i) = simd::decode(w, addr) {
        return Some(i);
    }

    // Conversion between floating point and integer.
    if bits(w, 30, 24) == 0b0011110 && bit(w, 21) == 1 && bits(w, 11, 10) == 0 {
        let sf = bit(w, 31) == 1;
        let ftype = bits(w, 23, 22);
        let fwidth = match ftype {
            0b00 => Width::W32,
            0b01 => Width::W64,
            0b11 => Width::W16,
            _ => return None,
        };
        let rmode = bits(w, 20, 19);
        let opcode = bits(w, 18, 16);
        let rd = bits(w, 4, 0);
        let rn = bits(w, 9, 5);
        let (mnem, to_int) = match (rmode, opcode) {
            (0b00, 0b010) => ("scvtf", false),
            (0b00, 0b011) => ("ucvtf", false),
            (0b00, 0b000) => ("fcvtns", true),
            (0b00, 0b001) => ("fcvtnu", true),
            (0b01, 0b000) => ("fcvtps", true),
            (0b01, 0b001) => ("fcvtpu", true),
            (0b10, 0b000) => ("fcvtms", true),
            (0b10, 0b001) => ("fcvtmu", true),
            (0b11, 0b000) => ("fcvtzs", true),
            (0b11, 0b001) => ("fcvtzu", true),
            (0b00, 0b110) => ("fmov", true),
            (0b00, 0b111) => ("fmov", false),
            _ => return None,
        };
        let mut i = ins(addr, mnem, Flow::Next);
        if to_int {
            i.push(Operand::Reg(r(rd, sf)));
            i.push(Operand::Reg(v(rn, fwidth)));
        } else {
            i.push(Operand::Reg(v(rd, fwidth)));
            i.push(Operand::Reg(r(rn, sf)));
        }
        return Some(i);
    }
    None
}
