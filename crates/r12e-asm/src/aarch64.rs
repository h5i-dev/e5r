//! AArch64 encoding: one [`Insn`] to one 32-bit word.
//!
//! Written against the architecture reference manual's field layouts, and
//! checked against the decoder in `r12e-arch`, which is the inverse function.
//! Where the decoder resolves an alias (`asr` for the right `sbfm`), this
//! lowers the same alias back to the same encoding, so the round trip is the
//! identity on bytes rather than only on meaning.

// Encoding literals are grouped the way the manual draws them.
#![allow(clippy::unusual_byte_groupings)]

use r12e_arch::insn::{AddrMode, Extend, Insn, Operand, Reg, RegClass, Shift, Width};
use r12e_core::Addr;

use crate::Encoded;
use crate::error::AsmError;

/// Every mnemonic this encoder accepts, as the static strings [`Insn`] holds.
const MNEMONICS: &[&str] = &[
    "adc",
    "adcs",
    "add",
    "adds",
    "adr",
    "adrp",
    "and",
    "ands",
    "asr",
    "asrv",
    "autia1716",
    "autiasp",
    "autiaz",
    "autib1716",
    "autibsp",
    "autibz",
    "b",
    "b.al",
    "b.cc",
    "b.cs",
    "b.eq",
    "b.ge",
    "b.gt",
    "b.hi",
    "b.hs",
    "b.le",
    "b.lo",
    "b.ls",
    "b.lt",
    "b.mi",
    "b.ne",
    "b.nv",
    "b.pl",
    "b.vc",
    "b.vs",
    "bfi",
    "bfm",
    "bfxil",
    "bic",
    "bics",
    "bl",
    "blr",
    "br",
    "brk",
    "bti",
    "cbnz",
    "cbz",
    "ccmn",
    "ccmp",
    "cinc",
    "cinv",
    "cls",
    "clz",
    "cmn",
    "cmp",
    "cneg",
    "csel",
    "cset",
    "csetm",
    "csinc",
    "csinv",
    "csneg",
    "dmb",
    "dsb",
    "eon",
    "eor",
    "eret",
    "extr",
    "hint",
    "hlt",
    "hvc",
    "isb",
    "ldnp",
    "ldp",
    "ldpsw",
    "ldr",
    "ldrb",
    "ldrh",
    "ldrsb",
    "ldrsh",
    "ldrsw",
    "ldur",
    "ldurb",
    "ldurh",
    "ldursb",
    "ldursh",
    "ldursw",
    "lsl",
    "lslv",
    "lsr",
    "lsrv",
    "madd",
    "mneg",
    "mov",
    "movk",
    "movn",
    "movz",
    "msub",
    "mul",
    "mvn",
    "neg",
    "negs",
    "ngc",
    "ngcs",
    "nop",
    "orn",
    "orr",
    "pacia1716",
    "paciasp",
    "paciaz",
    "pacib1716",
    "pacibsp",
    "pacibz",
    "prfm",
    "prfum",
    "rbit",
    "ret",
    "rev",
    "rev16",
    "rev32",
    "ror",
    "rorv",
    "sbc",
    "sbcs",
    "sbfiz",
    "sbfm",
    "sbfx",
    "sdiv",
    "sev",
    "sevl",
    "smaddl",
    "smc",
    "smnegl",
    "smsubl",
    "smulh",
    "smull",
    "stnp",
    "stp",
    "str",
    "strb",
    "strh",
    "stur",
    "sturb",
    "sturh",
    "sub",
    "subs",
    "svc",
    "sxtb",
    "sxth",
    "sxtw",
    "tbnz",
    "tbz",
    "tst",
    "ubfiz",
    "ubfm",
    "ubfx",
    "udf",
    "udiv",
    "umaddl",
    "umnegl",
    "umsubl",
    "umulh",
    "umull",
    "uxtb",
    "uxth",
    "wfe",
    "wfi",
    "xpaclri",
    "yield",
];

/// Resolve a mnemonic to the static string an [`Insn`] can hold.
pub(crate) fn intern(s: &str) -> Option<&'static str> {
    MNEMONICS.binary_search(&s).ok().map(|n| MNEMONICS[n])
}

/// Names that appear as bare words in an operand position.
const NAMES: &[&str] = &[
    "c",
    "ish",
    "ishld",
    "ishst",
    "j",
    "jc",
    "ld",
    "nsh",
    "nshld",
    "nshst",
    "osh",
    "oshld",
    "oshst",
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
    "st",
    "sy",
];

pub(crate) fn name(s: &str) -> Option<&'static str> {
    NAMES.binary_search(&s).ok().map(|n| NAMES[n])
}

/// Barrier option value for a name, `CRm` in the encoding.
fn barrier_crm(s: &str) -> Option<u32> {
    Some(match s {
        "oshld" => 1,
        "oshst" => 2,
        "osh" => 3,
        "nshld" => 5,
        "nshst" => 6,
        "nsh" => 7,
        "ishld" => 9,
        "ishst" => 10,
        "ish" => 11,
        "ld" => 13,
        "st" => 14,
        "sy" => 15,
        _ => return None,
    })
}

/// The prefetch operation number a name stands for.
fn prefetch_num(s: &str) -> Option<u32> {
    let (kind, rest) = if let Some(r) = s.strip_prefix("pld") {
        (0u32, r)
    } else if let Some(r) = s.strip_prefix("pli") {
        (1, r)
    } else {
        (2, s.strip_prefix("pst")?)
    };
    let (target, rest) = if let Some(r) = rest.strip_prefix("l1") {
        (0u32, r)
    } else if let Some(r) = rest.strip_prefix("l2") {
        (1, r)
    } else if let Some(r) = rest.strip_prefix("l3") {
        (2, r)
    } else {
        (3, rest.strip_prefix("slc")?)
    };
    let policy = match rest {
        "keep" => 0u32,
        "strm" => 1,
        _ => return None,
    };
    Some((kind << 3) | (target << 1) | policy)
}

/// Parse a register name.
pub(crate) fn register(s: &str) -> Option<Reg> {
    match s {
        "sp" => {
            return Some(Reg {
                class: RegClass::Sp,
                num: 31,
                width: Width::W64,
            });
        }
        "wsp" => {
            return Some(Reg {
                class: RegClass::Sp,
                num: 31,
                width: Width::W32,
            });
        }
        "xzr" => {
            return Some(Reg {
                class: RegClass::Zr,
                num: 31,
                width: Width::W64,
            });
        }
        "wzr" => {
            return Some(Reg {
                class: RegClass::Zr,
                num: 31,
                width: Width::W32,
            });
        }
        _ => {}
    }
    let (head, rest) = s.split_at_checked(1)?;
    let num: u32 = if rest.len() <= 2 && !rest.is_empty() {
        rest.parse().ok()?
    } else {
        return None;
    };
    let width = match head {
        "x" => Width::W64,
        "w" => Width::W32,
        "b" => Width::W8,
        "h" => Width::W16,
        "s" => Width::W32,
        "d" => Width::W64,
        "q" => Width::W128,
        _ => return None,
    };
    if matches!(head, "x" | "w") {
        if num > 30 {
            return None;
        }
        Some(Reg::gpr(num as u8, width))
    } else {
        if num > 31 {
            return None;
        }
        Some(Reg::vec(num as u8, width))
    }
}

/// The condition code a name stands for.
pub(crate) fn condition(s: &str) -> Option<u8> {
    Some(match s {
        "eq" => 0,
        "ne" => 1,
        "cs" | "hs" => 2,
        "cc" | "lo" => 3,
        "mi" => 4,
        "pl" => 5,
        "vs" => 6,
        "vc" => 7,
        "hi" => 8,
        "ls" => 9,
        "ge" => 10,
        "lt" => 11,
        "gt" => 12,
        "le" => 13,
        "al" => 14,
        "nv" => 15,
        _ => return None,
    })
}

// ------------------------------------------------------------------ helpers

fn form(i: &Insn, detail: &'static str) -> AsmError {
    AsmError::UnsupportedForm {
        mnemonic: i.mnemonic.to_string(),
        detail,
    }
}

/// The register number, with 31 standing for both `sp` and the zero register.
fn num(i: &Insn, r: Reg) -> Result<u32, AsmError> {
    match r.class {
        RegClass::Gpr => Ok(r.num as u32 & 31),
        RegClass::Sp | RegClass::Zr => Ok(31),
        _ => Err(form(i, "expected a general purpose register")),
    }
}

fn gpr_op(i: &Insn, n: usize) -> Result<Reg, AsmError> {
    match i.operands().get(n) {
        Some(Operand::Reg(r)) if matches!(r.class, RegClass::Gpr | RegClass::Sp | RegClass::Zr) => {
            Ok(*r)
        }
        _ => Err(form(i, "expected a general purpose register operand")),
    }
}

fn sf_of(r: Reg) -> Result<u32, AsmError> {
    match r.width {
        Width::W64 => Ok(1),
        Width::W32 => Ok(0),
        _ => Err(AsmError::UnsupportedForm {
            mnemonic: String::new(),
            detail: "a general purpose operand is 32 or 64 bits",
        }),
    }
}

/// An immediate, however the parser or the decoder chose to spell it.
fn imm_of(op: &Operand) -> Option<i64> {
    match op {
        Operand::Imm(v) | Operand::Count(v) => Some(*v),
        Operand::UImm(v) => Some(*v as i64),
        _ => None,
    }
}

fn uimm_of(op: &Operand) -> Option<u64> {
    match op {
        Operand::Imm(v) | Operand::Count(v) => Some(*v as u64),
        Operand::UImm(v) => Some(*v),
        _ => None,
    }
}

fn addr_of(op: &Operand) -> Option<Addr> {
    match op {
        Operand::Addr(a) => Some(*a),
        Operand::Imm(v) | Operand::Count(v) => Some(Addr(*v as u64)),
        Operand::UImm(v) => Some(Addr(*v)),
        _ => None,
    }
}

fn fits(value: i64, bits: u32, what: &'static str) -> Result<u32, AsmError> {
    let low = -(1i64 << (bits - 1));
    let high = (1i64 << (bits - 1)) - 1;
    if value < low || value > high {
        return Err(AsmError::Range {
            what,
            value,
            low,
            high,
        });
    }
    Ok((value as u64 & ((1u64 << bits) - 1)) as u32)
}

fn unsigned_fits(value: i64, bits: u32, what: &'static str) -> Result<u32, AsmError> {
    let high = (1i64 << bits) - 1;
    if !(0..=high).contains(&value) {
        return Err(AsmError::Range {
            what,
            value,
            low: 0,
            high,
        });
    }
    Ok(value as u32)
}

/// A branch displacement in bytes, checked for range and alignment.
fn displacement(i: &Insn, to: Addr, bits: u32) -> Result<u32, AsmError> {
    let delta = to.get().wrapping_sub(i.addr.get()) as i64;
    let high = ((1i64 << (bits - 1)) - 1) * 4;
    let low = -(1i64 << (bits - 1)) * 4;
    if delta % 4 != 0 {
        return Err(AsmError::Unaligned {
            what: "branch target",
            value: delta,
            align: 4,
        });
    }
    if delta < low || delta > high {
        return Err(AsmError::BranchRange {
            mnemonic: i.mnemonic.to_string(),
            from: i.addr.get(),
            to: to.get(),
            low,
            high,
        });
    }
    Ok(((delta >> 2) as u64 & ((1u64 << bits) - 1)) as u32)
}

// -------------------------------------------------------- logical immediates

fn mask_bits(n: u32) -> u64 {
    if n >= 64 { u64::MAX } else { (1u64 << n) - 1 }
}

/// The inverse of the architecture's `DecodeBitMasks`: `N:immr:imms` for a
/// value, or `None` when no rotated run of ones produces it.
pub(crate) fn encode_bitmask(value: u64, sf: bool) -> Option<(u32, u32, u32)> {
    if !sf && value >> 32 != 0 {
        return None;
    }
    // Work at 64 bits with the 32-bit case replicated, which is what the
    // architecture does, so one search covers both.
    let val = if sf {
        value
    } else {
        (value & 0xffff_ffff) | (value << 32)
    };
    if val == 0 || val == u64::MAX {
        return None;
    }
    // The element size is the smallest power of two the value repeats at.
    let mut size = 64u32;
    while size > 2 {
        let half = size / 2;
        let m = mask_bits(half);
        let mut repeats = true;
        let mut pos = 0;
        while pos < 64 {
            if ((val >> pos) & m) != (val & m) {
                repeats = false;
                break;
            }
            pos += half;
        }
        if !repeats {
            break;
        }
        size = half;
    }
    let elem = val & mask_bits(size);
    let ones = elem.count_ones();
    if ones == 0 || ones == size {
        return None;
    }
    // The set bits have to be contiguous once rotated left by `immr`.
    let target = mask_bits(ones);
    let mut immr = None;
    for r in 0..size {
        let rotated = ((elem << r) | (elem >> (size - r).min(63))) & mask_bits(size);
        let rotated = if r == 0 { elem } else { rotated };
        if rotated == target {
            immr = Some(r);
            break;
        }
    }
    let immr = immr?;
    let n = u32::from(size == 64);
    let imms = (!((size << 1) - 1) & 0x3f) | (ones - 1);
    Some((n, immr, imms))
}

// ------------------------------------------------------------------- encode

/// Encode one instruction.
pub fn encode(i: &Insn) -> Result<Encoded, AsmError> {
    let w = word(i)?;
    Ok(Encoded::from_u32_le(w))
}

fn word(i: &Insn) -> Result<u32, AsmError> {
    match i.mnemonic {
        "add" | "adds" | "sub" | "subs" => add_sub(i),
        "cmp" | "cmn" => cmp(i),
        "neg" | "negs" => neg(i),
        "and" | "ands" | "orr" | "eor" | "bic" | "bics" | "orn" | "eon" => logical(i),
        "tst" => tst(i),
        "mvn" => mvn(i),
        "mov" => mov(i),
        "movz" | "movn" | "movk" => move_wide(i),
        "adr" | "adrp" => pc_rel(i),
        "b" | "bl" => branch_imm(i),
        m if m.starts_with("b.") => b_cond(i),
        "cbz" | "cbnz" => cmp_branch(i),
        "tbz" | "tbnz" => test_branch(i),
        "br" | "blr" | "ret" => branch_reg(i),
        "eret" => Ok(0xd69f_03e0),
        "svc" | "hvc" | "smc" | "brk" | "hlt" => exception(i),
        "nop" | "yield" | "wfe" | "wfi" | "sev" | "sevl" | "hint" | "xpaclri" | "pacia1716"
        | "pacib1716" | "autia1716" | "autib1716" | "paciaz" | "paciasp" | "pacibz" | "pacibsp"
        | "autiaz" | "autiasp" | "autibz" | "autibsp" => hint(i),
        "bti" => bti(i),
        "dmb" | "dsb" | "isb" => barrier(i),
        "ldr" | "str" | "ldrb" | "strb" | "ldrh" | "strh" | "ldrsb" | "ldrsh" | "ldrsw"
        | "ldur" | "stur" | "ldurb" | "sturb" | "ldurh" | "sturh" | "ldursb" | "ldursh"
        | "ldursw" | "prfm" | "prfum" => load_store(i),
        "ldp" | "stp" | "ldnp" | "stnp" | "ldpsw" => load_store_pair(i),
        "lsl" | "lsr" | "asr" | "ror" => shift(i),
        "lslv" | "lsrv" | "asrv" | "rorv" | "udiv" | "sdiv" => dp2(i),
        "ubfm" | "sbfm" | "bfm" => bfm_raw(i),
        "ubfx" | "sbfx" | "bfxil" | "ubfiz" | "sbfiz" | "bfi" => bitfield(i),
        "sxtb" | "sxth" | "sxtw" | "uxtb" | "uxth" => extend_op(i),
        "mul" | "madd" | "msub" | "mneg" | "smull" | "umull" | "smaddl" | "umaddl" | "smsubl"
        | "umsubl" | "smnegl" | "umnegl" | "smulh" | "umulh" => multiply(i),
        "csel" | "csinc" | "csinv" | "csneg" => csel(i),
        "cset" | "csetm" => cset(i),
        "cinc" | "cinv" | "cneg" => cinc(i),
        "ccmp" | "ccmn" => ccmp(i),
        "adc" | "adcs" | "sbc" | "sbcs" => adc(i),
        "ngc" | "ngcs" => ngc(i),
        "extr" => extr(i),
        "rbit" | "rev" | "rev16" | "rev32" | "clz" | "cls" => dp1(i),
        "udf" => udf(i),
        _ => Err(form(i, "no encoder for this mnemonic")),
    }
}

fn add_sub(i: &Insn) -> Result<u32, AsmError> {
    let sub = u32::from(i.mnemonic.starts_with("sub"));
    let s = u32::from(i.mnemonic.ends_with('s'));
    let rd = gpr_op(i, 0)?;
    let rn = gpr_op(i, 1)?;
    let sf = sf_of(rd).map_err(|_| form(i, "a destination is 32 or 64 bits"))?;
    let third = i.operands().get(2).ok_or(form(i, "needs three operands"))?;
    encode_add_sub(
        i,
        sf,
        sub,
        s,
        num(i, rd)?,
        num(i, rn)?,
        third,
        3,
        is_sp(rd) || is_sp(rn),
    )
}

fn is_sp(r: Reg) -> bool {
    r.class == RegClass::Sp
}

/// The shared tail of add, sub, cmp, cmn and neg.
///
/// Long because the callers have already decided every field between them:
/// gathering them into a struct would move the argument list rather than
/// shorten it.
#[allow(clippy::too_many_arguments)]
fn encode_add_sub(
    i: &Insn,
    sf: u32,
    sub: u32,
    s: u32,
    rd: u32,
    rn: u32,
    third: &Operand,
    next: usize,
    sp_involved: bool,
) -> Result<u32, AsmError> {
    match third {
        Operand::Imm(_) | Operand::UImm(_) | Operand::Count(_) => {
            let v = imm_of(third).unwrap_or(0);
            let mut sh = 0u32;
            let mut imm = v;
            if let Some(qualifier) = i.operands().get(next) {
                match qualifier {
                    Operand::ShiftOp(Shift::Lsl, 12) => sh = 1,
                    Operand::ShiftOp(Shift::Lsl, 0) => sh = 0,
                    _ => return Err(form(i, "an add or subtract immediate shifts by 12 only")),
                }
            } else if !(0..=0xfff).contains(&v)
                && v & 0xfff == 0
                && (0..=0xfff).contains(&(v >> 12))
            {
                // A wide multiple of 4096 is what `lsl #12` is for.
                sh = 1;
                imm = v >> 12;
            }
            let imm12 = unsigned_fits(imm, 12, "add or subtract immediate")?;
            Ok((sf << 31)
                | (sub << 30)
                | (s << 29)
                | (0b100010 << 23)
                | (sh << 22)
                | (imm12 << 10)
                | (rn << 5)
                | rd)
        }
        Operand::Reg(rm) if sp_involved => {
            let option = if sf == 1 { 0b011 } else { 0b010 };
            Ok(extended(sf, sub, s, option, 0, num(i, *rm)?, rn, rd))
        }
        Operand::Reg(rm) => {
            let rm = num(i, *rm)?;
            Ok(
                (sf << 31)
                    | (sub << 30)
                    | (s << 29)
                    | (0b01011 << 24)
                    | (rm << 16)
                    | (rn << 5)
                    | rd,
            )
        }
        Operand::Shifted(rm, kind, amount) => {
            let shift = match kind {
                Shift::Lsl => 0,
                Shift::Lsr => 1,
                Shift::Asr => 2,
                _ => return Err(form(i, "an add or subtract shifts by lsl, lsr or asr")),
            };
            let limit = if sf == 1 { 63 } else { 31 };
            if *amount as i64 > limit {
                return Err(AsmError::Range {
                    what: "shift amount",
                    value: *amount as i64,
                    low: 0,
                    high: limit,
                });
            }
            Ok((sf << 31)
                | (sub << 30)
                | (s << 29)
                | (0b01011 << 24)
                | (shift << 22)
                | (num(i, *rm)? << 16)
                | ((*amount as u32) << 10)
                | (rn << 5)
                | rd)
        }
        Operand::Extended(rm, ext, amount) => {
            let option = match ext {
                Extend::Uxtb => 0,
                Extend::Uxth => 1,
                Extend::Uxtw => 2,
                Extend::Uxtx => 3,
                Extend::Sxtb => 4,
                Extend::Sxth => 5,
                Extend::Sxtw => 6,
                Extend::Sxtx => 7,
                // `lsl` on an extended operand is the no-op extension.
                Extend::Lsl | Extend::LslZero => {
                    if sf == 1 {
                        3
                    } else {
                        2
                    }
                }
            };
            if *amount > 4 {
                return Err(AsmError::Range {
                    what: "extend shift",
                    value: *amount as i64,
                    low: 0,
                    high: 4,
                });
            }
            Ok(extended(
                sf,
                sub,
                s,
                option,
                *amount as u32,
                num(i, *rm)?,
                rn,
                rd,
            ))
        }
        _ => Err(form(i, "expected a register or an immediate")),
    }
}

#[allow(clippy::too_many_arguments)]
fn extended(sf: u32, sub: u32, s: u32, option: u32, amount: u32, rm: u32, rn: u32, rd: u32) -> u32 {
    (sf << 31)
        | (sub << 30)
        | (s << 29)
        | (0b01011 << 24)
        | (1 << 21)
        | (rm << 16)
        | (option << 13)
        | (amount << 10)
        | (rn << 5)
        | rd
}

fn cmp(i: &Insn) -> Result<u32, AsmError> {
    let sub = u32::from(i.mnemonic == "cmp");
    let rn = gpr_op(i, 0)?;
    let sf = sf_of(rn).map_err(|_| form(i, "a compare is 32 or 64 bits"))?;
    let second = i.operands().get(1).ok_or(form(i, "needs two operands"))?;
    encode_add_sub(i, sf, sub, 1, 31, num(i, rn)?, second, 2, is_sp(rn))
}

fn neg(i: &Insn) -> Result<u32, AsmError> {
    let s = u32::from(i.mnemonic.ends_with('s'));
    let rd = gpr_op(i, 0)?;
    let sf = sf_of(rd).map_err(|_| form(i, "a negate is 32 or 64 bits"))?;
    let second = i.operands().get(1).ok_or(form(i, "needs two operands"))?;
    encode_add_sub(i, sf, 1, s, num(i, rd)?, 31, second, 2, false)
}

fn logical_bits(m: &str) -> (u32, u32) {
    match m {
        "and" => (0b00, 0),
        "bic" => (0b00, 1),
        "orr" => (0b01, 0),
        "orn" => (0b01, 1),
        "eor" => (0b10, 0),
        "eon" => (0b10, 1),
        "ands" => (0b11, 0),
        _ => (0b11, 1),
    }
}

fn logical(i: &Insn) -> Result<u32, AsmError> {
    let (opc, n) = logical_bits(i.mnemonic);
    let rd = gpr_op(i, 0)?;
    let rn = gpr_op(i, 1)?;
    let sf = sf_of(rd).map_err(|_| form(i, "a logical operation is 32 or 64 bits"))?;
    let third = i.operands().get(2).ok_or(form(i, "needs three operands"))?;
    encode_logical(i, sf, opc, n, num(i, rd)?, num(i, rn)?, third)
}

fn encode_logical(
    i: &Insn,
    sf: u32,
    opc: u32,
    n: u32,
    rd: u32,
    rn: u32,
    third: &Operand,
) -> Result<u32, AsmError> {
    if let Some(v) = uimm_of(third) {
        if n == 1 {
            return Err(form(i, "the inverted logical operations take no immediate"));
        }
        let (bn, immr, imms) = encode_bitmask(v, sf == 1).ok_or_else(|| AsmError::NoEncoding {
            mnemonic: i.mnemonic.to_string(),
            value: v,
            what: "logical immediate: a rotated run of ones in a repeated element",
        })?;
        return Ok((sf << 31)
            | (opc << 29)
            | (0b100100 << 23)
            | (bn << 22)
            | (immr << 16)
            | (imms << 10)
            | (rn << 5)
            | rd);
    }
    let (rm, shift, amount) = match third {
        Operand::Reg(r) => (*r, 0u32, 0u32),
        Operand::Shifted(r, kind, amount) => (
            *r,
            match kind {
                Shift::Lsl => 0,
                Shift::Lsr => 1,
                Shift::Asr => 2,
                Shift::Ror => 3,
                Shift::Msl => return Err(form(i, "msl is a SIMD shift")),
            },
            *amount as u32,
        ),
        _ => return Err(form(i, "expected a register or an immediate")),
    };
    let limit = if sf == 1 { 63 } else { 31 };
    if amount as i64 > limit {
        return Err(AsmError::Range {
            what: "shift amount",
            value: amount as i64,
            low: 0,
            high: limit,
        });
    }
    Ok((sf << 31)
        | (opc << 29)
        | (0b01010 << 24)
        | (shift << 22)
        | (n << 21)
        | (num(i, rm)? << 16)
        | (amount << 10)
        | (rn << 5)
        | rd)
}

fn tst(i: &Insn) -> Result<u32, AsmError> {
    let rn = gpr_op(i, 0)?;
    let sf = sf_of(rn).map_err(|_| form(i, "a test is 32 or 64 bits"))?;
    let second = i.operands().get(1).ok_or(form(i, "needs two operands"))?;
    encode_logical(i, sf, 0b11, 0, 31, num(i, rn)?, second)
}

fn mvn(i: &Insn) -> Result<u32, AsmError> {
    let rd = gpr_op(i, 0)?;
    let sf = sf_of(rd).map_err(|_| form(i, "a move-not is 32 or 64 bits"))?;
    let second = i.operands().get(1).ok_or(form(i, "needs two operands"))?;
    encode_logical(i, sf, 0b01, 1, num(i, rd)?, 31, second)
}

fn mov(i: &Insn) -> Result<u32, AsmError> {
    let rd = gpr_op(i, 0)?;
    let sf = sf_of(rd).map_err(|_| form(i, "a move is 32 or 64 bits"))?;
    let second = *i.operands().get(1).ok_or(form(i, "needs two operands"))?;
    if let Operand::Reg(rm) = second {
        if is_sp(rd) || is_sp(rm) {
            // Moving to or from the stack pointer is `add Rd, Rn, #0`.
            return Ok((sf << 31) | (0b100010 << 23) | (num(i, rm)? << 5) | num(i, rd)?);
        }
        return encode_logical(i, sf, 0b01, 0, num(i, rd)?, 31, &second);
    }
    let v = uimm_of(&second).ok_or(form(i, "expected a register or an immediate"))?;
    let width = if sf == 1 { 64 } else { 32 };
    let v = if sf == 1 { v } else { v & 0xffff_ffff };
    let rd_n = num(i, rd)?;
    // MOVZ first, then MOVN, then the logical immediate: the same order the
    // decoder's alias rules assume, so the round trip keeps the bytes.
    for hw in 0..(width / 16) {
        let shift = hw * 16;
        if v & !(0xffffu64 << shift) == 0 {
            let imm16 = ((v >> shift) & 0xffff) as u32;
            return Ok((sf << 31)
                | (0b10 << 29)
                | (0b100101 << 23)
                | (hw << 21)
                | (imm16 << 5)
                | rd_n);
        }
    }
    let inv = if sf == 1 { !v } else { (!v) & 0xffff_ffff };
    for hw in 0..(width / 16) {
        let shift = hw * 16;
        if inv & !(0xffffu64 << shift) == 0 {
            let imm16 = ((inv >> shift) & 0xffff) as u32;
            if imm16 == 0 && hw != 0 {
                continue;
            }
            return Ok((sf << 31) | (0b100101 << 23) | (hw << 21) | (imm16 << 5) | rd_n);
        }
    }
    if let Some((bn, immr, imms)) = encode_bitmask(v, sf == 1) {
        return Ok((sf << 31)
            | (0b01 << 29)
            | (0b100100 << 23)
            | (bn << 22)
            | (immr << 16)
            | (imms << 10)
            | (31 << 5)
            | rd_n);
    }
    Err(AsmError::NoEncoding {
        mnemonic: i.mnemonic.to_string(),
        value: v,
        what: "value one move-wide or logical immediate can build; \
               build it with movz and movk",
    })
}

fn move_wide(i: &Insn) -> Result<u32, AsmError> {
    let rd = gpr_op(i, 0)?;
    let sf = sf_of(rd).map_err(|_| form(i, "a move-wide is 32 or 64 bits"))?;
    let v = imm_of(i.operands().get(1).ok_or(form(i, "needs an immediate"))?)
        .ok_or(form(i, "expected an immediate"))?;
    let imm16 = unsigned_fits(v, 16, "move-wide immediate")?;
    let mut hw = 0u32;
    if let Some(Operand::ShiftOp(Shift::Lsl, amount)) = i.operands().get(2) {
        if amount % 16 != 0 {
            return Err(form(i, "a move-wide shifts by 0, 16, 32 or 48"));
        }
        hw = *amount as u32 / 16;
    }
    if hw >= if sf == 1 { 4 } else { 2 } {
        return Err(AsmError::Range {
            what: "move-wide shift",
            value: (hw * 16) as i64,
            low: 0,
            high: if sf == 1 { 48 } else { 16 },
        });
    }
    let opc = match i.mnemonic {
        "movn" => 0b00,
        "movz" => 0b10,
        _ => 0b11,
    };
    Ok((sf << 31) | (opc << 29) | (0b100101 << 23) | (hw << 21) | (imm16 << 5) | num(i, rd)?)
}

fn pc_rel(i: &Insn) -> Result<u32, AsmError> {
    let rd = gpr_op(i, 0)?;
    let target = addr_of(i.operands().get(1).ok_or(form(i, "needs a target"))?)
        .ok_or(form(i, "expected an address"))?;
    let page = i.mnemonic == "adrp";
    let delta = if page {
        let from = i.addr.get() & !0xfff;
        if target.get() & 0xfff != 0 {
            return Err(AsmError::Unaligned {
                what: "adrp target",
                value: target.get() as i64,
                align: 4096,
            });
        }
        (target.get().wrapping_sub(from) as i64) >> 12
    } else {
        target.get().wrapping_sub(i.addr.get()) as i64
    };
    if !(-(1i64 << 20)..(1i64 << 20)).contains(&delta) {
        let scale = if page { 4096 } else { 1 };
        return Err(AsmError::BranchRange {
            mnemonic: i.mnemonic.to_string(),
            from: i.addr.get(),
            to: target.get(),
            low: -(1i64 << 20) * scale,
            high: ((1i64 << 20) - 1) * scale,
        });
    }
    let imm = delta as u32 & 0x1f_ffff;
    Ok((u32::from(page) << 31)
        | ((imm & 3) << 29)
        | (0b10000 << 24)
        | ((imm >> 2) << 5)
        | num(i, rd)?)
}

fn branch_imm(i: &Insn) -> Result<u32, AsmError> {
    let target = addr_of(i.operands().first().ok_or(form(i, "needs a target"))?)
        .ok_or(form(i, "expected an address"))?;
    let imm = displacement(i, target, 26)?;
    Ok((u32::from(i.mnemonic == "bl") << 31) | (0b00101 << 26) | imm)
}

fn b_cond(i: &Insn) -> Result<u32, AsmError> {
    let cond = condition(&i.mnemonic[2..]).ok_or(form(i, "unknown condition"))? as u32;
    let target = addr_of(i.operands().first().ok_or(form(i, "needs a target"))?)
        .ok_or(form(i, "expected an address"))?;
    let imm = displacement(i, target, 19)?;
    Ok((0b0101010 << 25) | (imm << 5) | cond)
}

fn cmp_branch(i: &Insn) -> Result<u32, AsmError> {
    let rt = gpr_op(i, 0)?;
    let sf = sf_of(rt).map_err(|_| form(i, "a compare-and-branch is 32 or 64 bits"))?;
    let target = addr_of(i.operands().get(1).ok_or(form(i, "needs a target"))?)
        .ok_or(form(i, "expected an address"))?;
    let imm = displacement(i, target, 19)?;
    Ok((sf << 31)
        | (0b011010 << 25)
        | (u32::from(i.mnemonic == "cbnz") << 24)
        | (imm << 5)
        | num(i, rt)?)
}

fn test_branch(i: &Insn) -> Result<u32, AsmError> {
    let rt = gpr_op(i, 0)?;
    let bit = imm_of(i.operands().get(1).ok_or(form(i, "needs a bit number"))?)
        .ok_or(form(i, "expected a bit number"))?;
    let bit = unsigned_fits(bit, 6, "bit number")?;
    let target = addr_of(i.operands().get(2).ok_or(form(i, "needs a target"))?)
        .ok_or(form(i, "expected an address"))?;
    let imm = displacement(i, target, 14)?;
    Ok(((bit >> 5) << 31)
        | (0b011011 << 25)
        | (u32::from(i.mnemonic == "tbnz") << 24)
        | ((bit & 31) << 19)
        | (imm << 5)
        | num(i, rt)?)
}

fn branch_reg(i: &Insn) -> Result<u32, AsmError> {
    let (opc, default) = match i.mnemonic {
        "br" => (0b0000u32, None),
        "blr" => (0b0001, None),
        _ => (0b0010, Some(30u32)),
    };
    let rn = match i.operands().first() {
        Some(Operand::Reg(r)) => num(i, *r)?,
        None => default.ok_or(form(i, "needs a register"))?,
        _ => return Err(form(i, "expected a register")),
    };
    Ok((0b1101011 << 25) | (opc << 21) | (0b11111 << 16) | (rn << 5))
}

fn exception(i: &Insn) -> Result<u32, AsmError> {
    let (opc, ll) = match i.mnemonic {
        "svc" => (0b000u32, 0b01u32),
        "hvc" => (0b000, 0b10),
        "smc" => (0b000, 0b11),
        "brk" => (0b001, 0b00),
        _ => (0b010, 0b00),
    };
    let v = match i.operands().first() {
        Some(op) => imm_of(op).ok_or(form(i, "expected an immediate"))?,
        None => 0,
    };
    let imm16 = unsigned_fits(v, 16, "exception immediate")?;
    Ok((0b1101_0100 << 24) | (opc << 21) | (imm16 << 5) | ll)
}

fn hint(i: &Insn) -> Result<u32, AsmError> {
    let hint = match i.mnemonic {
        "nop" => 0u32,
        "yield" => 1,
        "wfe" => 2,
        "wfi" => 3,
        "sev" => 4,
        "sevl" => 5,
        // The pointer-authentication hints. They open and close nearly every
        // function a modern toolchain emits, so a patch that pastes a prologue
        // back needs them even though nothing here authenticates anything.
        "xpaclri" => 7,
        "pacia1716" => 8,
        "pacib1716" => 10,
        "autia1716" => 12,
        "autib1716" => 14,
        "paciaz" => 24,
        "paciasp" => 25,
        "pacibz" => 26,
        "pacibsp" => 27,
        "autiaz" => 28,
        "autiasp" => 29,
        "autibz" => 30,
        "autibsp" => 31,
        _ => {
            let v = imm_of(i.operands().first().ok_or(form(i, "needs a hint number"))?)
                .ok_or(form(i, "expected an immediate"))?;
            unsigned_fits(v, 7, "hint number")?
        }
    };
    Ok(0xd503_201f | ((hint >> 3) << 8) | ((hint & 7) << 5))
}

fn bti(i: &Insn) -> Result<u32, AsmError> {
    let op2 = match i.operands().first() {
        None => 0b100u32,
        Some(Operand::Name("c")) => 0b010,
        Some(Operand::Name("j")) => 0b100,
        Some(Operand::Name("jc")) => 0b110,
        _ => return Err(form(i, "bti takes c, j or jc")),
    };
    Ok(0xd503_201f | (0b0100 << 8) | (op2 << 5))
}

fn barrier(i: &Insn) -> Result<u32, AsmError> {
    let op2 = match i.mnemonic {
        "dsb" => 0b100u32,
        "dmb" => 0b101,
        _ => 0b110,
    };
    let crm = match i.operands().first() {
        None => 15,
        Some(Operand::Name(n)) => barrier_crm(n).ok_or(form(i, "unknown barrier option"))?,
        Some(op) => {
            let v = imm_of(op).ok_or(form(i, "expected a barrier option"))?;
            unsigned_fits(v, 4, "barrier option")?
        }
    };
    Ok(0xd503_3000 | (crm << 8) | (op2 << 5) | 0b11111)
}

fn udf(i: &Insn) -> Result<u32, AsmError> {
    let v = match i.operands().first() {
        Some(op) => imm_of(op).ok_or(form(i, "expected an immediate"))?,
        None => 0,
    };
    unsigned_fits(v, 16, "udf immediate")
}

// --------------------------------------------------------- loads and stores

/// `size`, `opc`, the SIMD bit, and the bytes one access transfers.
struct LsForm {
    size: u32,
    opc: u32,
    v: u32,
    bytes: u64,
}

/// The unscaled mnemonics are the scaled ones with a different immediate
/// field, so they share every other decision.
fn unscaled_base(m: &str) -> Option<&'static str> {
    Some(match m {
        "ldur" => "ldr",
        "stur" => "str",
        "ldurb" => "ldrb",
        "sturb" => "strb",
        "ldurh" => "ldrh",
        "sturh" => "strh",
        "ldursb" => "ldrsb",
        "ldursh" => "ldrsh",
        "ldursw" => "ldrsw",
        "prfum" => "prfm",
        _ => return None,
    })
}

fn ls_form(i: &Insn, m: &str, rt: Option<Reg>) -> Result<LsForm, AsmError> {
    let load = !m.starts_with("st");
    if m == "prfm" {
        return Ok(LsForm {
            size: 0b11,
            opc: 0b10,
            v: 0,
            bytes: 8,
        });
    }
    let rt = rt.ok_or(form(i, "needs a register operand"))?;
    if rt.class == RegClass::Vec {
        let (size, wide, bytes) = match rt.width {
            Width::W8 => (0b00u32, false, 1u64),
            Width::W16 => (0b01, false, 2),
            Width::W32 => (0b10, false, 4),
            Width::W64 => (0b11, false, 8),
            Width::W128 => (0b00, true, 16),
        };
        let opc = (u32::from(wide) << 1) | u32::from(load);
        return Ok(LsForm {
            size,
            opc,
            v: 1,
            bytes,
        });
    }
    let wide = rt.width == Width::W64;
    Ok(match m {
        "strb" => LsForm {
            size: 0,
            opc: 0b00,
            v: 0,
            bytes: 1,
        },
        "ldrb" => LsForm {
            size: 0,
            opc: 0b01,
            v: 0,
            bytes: 1,
        },
        "ldrsb" => LsForm {
            size: 0,
            opc: if wide { 0b10 } else { 0b11 },
            v: 0,
            bytes: 1,
        },
        "strh" => LsForm {
            size: 1,
            opc: 0b00,
            v: 0,
            bytes: 2,
        },
        "ldrh" => LsForm {
            size: 1,
            opc: 0b01,
            v: 0,
            bytes: 2,
        },
        "ldrsh" => LsForm {
            size: 1,
            opc: if wide { 0b10 } else { 0b11 },
            v: 0,
            bytes: 2,
        },
        "ldrsw" => LsForm {
            size: 0b10,
            opc: 0b10,
            v: 0,
            bytes: 4,
        },
        "str" => LsForm {
            size: if wide { 0b11 } else { 0b10 },
            opc: 0b00,
            v: 0,
            bytes: if wide { 8 } else { 4 },
        },
        "ldr" => LsForm {
            size: if wide { 0b11 } else { 0b10 },
            opc: 0b01,
            v: 0,
            bytes: if wide { 8 } else { 4 },
        },
        _ => return Err(form(i, "no encoder for this load or store")),
    })
}

fn load_store(i: &Insn) -> Result<u32, AsmError> {
    let forced_unscaled = unscaled_base(i.mnemonic);
    let m = forced_unscaled.unwrap_or(i.mnemonic);
    let first = i.operands().first().ok_or(form(i, "needs operands"))?;
    let (rt_reg, rt_num) = match first {
        Operand::Reg(r) => (Some(*r), num_any(i, *r)?),
        Operand::Name(n) => (
            None,
            prefetch_num(n).ok_or(form(i, "unknown prefetch operation"))?,
        ),
        op => {
            // `prfm #0x18, [x0]` for the unnamed operations.
            let v = imm_of(op).ok_or(form(i, "expected a register"))?;
            (None, unsigned_fits(v, 5, "prefetch operation")?)
        }
    };
    let f = ls_form(i, m, rt_reg)?;
    let second = i.operands().get(1).ok_or(form(i, "needs an address"))?;

    if let Some(target) = match second {
        Operand::Addr(_) => addr_of(second),
        _ => None,
    } {
        // Load register (literal).
        if forced_unscaled.is_some() {
            return Err(form(i, "an unscaled load has no literal form"));
        }
        let (opc, v) = match (m, rt_reg.map(|r| (r.class, r.width))) {
            ("prfm", _) => (0b11u32, 0u32),
            ("ldrsw", _) => (0b10, 0),
            ("ldr", Some((RegClass::Vec, Width::W32))) => (0b00, 1),
            ("ldr", Some((RegClass::Vec, Width::W64))) => (0b01, 1),
            ("ldr", Some((RegClass::Vec, Width::W128))) => (0b10, 1),
            ("ldr", Some((_, Width::W32))) => (0b00, 0),
            ("ldr", Some((_, Width::W64))) => (0b01, 0),
            _ => return Err(form(i, "this mnemonic has no pc-relative form")),
        };
        let imm = displacement(i, target, 19)?;
        return Ok((opc << 30) | (0b011 << 27) | (v << 26) | (imm << 5) | rt_num);
    }

    let mem = match second {
        Operand::Mem(m) => *m,
        _ => return Err(form(i, "expected a memory operand")),
    };
    let rn = mem.base.ok_or(form(i, "a memory operand needs a base"))?;
    let rn = num(i, rn)?;

    if let Some((index, ext, amount)) = mem.index {
        if mem.mode != AddrMode::Offset {
            return Err(form(i, "an indexed address takes no writeback"));
        }
        let option = match ext {
            Extend::Uxtw => 0b010u32,
            Extend::Lsl | Extend::LslZero => 0b011,
            Extend::Sxtw => 0b110,
            Extend::Sxtx => 0b111,
            _ => return Err(form(i, "an index extends by uxtw, lsl, sxtw or sxtx")),
        };
        let scale = f.bytes.trailing_zeros();
        let s = if ext == Extend::LslZero {
            1
        } else if amount == 0 {
            0
        } else if amount as u32 == scale {
            1
        } else {
            return Err(AsmError::Range {
                what: "index shift, which is either zero or the access size",
                value: amount as i64,
                low: 0,
                high: scale as i64,
            });
        };
        return Ok((f.size << 30)
            | (0b111 << 27)
            | (f.v << 26)
            | (f.opc << 22)
            | (1 << 21)
            | (num(i, index)? << 16)
            | (option << 13)
            | (s << 12)
            | (0b10 << 10)
            | (rn << 5)
            | rt_num);
    }

    let disp = mem.disp;
    let scaled_ok = mem.mode == AddrMode::Offset
        && forced_unscaled.is_none()
        && disp >= 0
        && f.bytes != 0
        && disp % f.bytes as i64 == 0
        && disp / f.bytes as i64 <= 0xfff;
    if scaled_ok {
        let imm12 = (disp / f.bytes as i64) as u32;
        return Ok((f.size << 30)
            | (0b111 << 27)
            | (f.v << 26)
            | (1 << 24)
            | (f.opc << 22)
            | (imm12 << 10)
            | (rn << 5)
            | rt_num);
    }
    let imm9 = fits(disp, 9, "load or store offset")?;
    let mode_bits = match mem.mode {
        AddrMode::Offset => 0b00u32,
        AddrMode::PostIndex => 0b01,
        AddrMode::PreIndex => 0b11,
    };
    Ok((f.size << 30)
        | (0b111 << 27)
        | (f.v << 26)
        | (f.opc << 22)
        | (imm9 << 12)
        | (mode_bits << 10)
        | (rn << 5)
        | rt_num)
}

/// A register number that also accepts the vector bank.
fn num_any(i: &Insn, r: Reg) -> Result<u32, AsmError> {
    match r.class {
        RegClass::Vec => Ok(r.num as u32 & 31),
        _ => num(i, r),
    }
}

fn load_store_pair(i: &Insn) -> Result<u32, AsmError> {
    let rt = match i.operands().first() {
        Some(Operand::Reg(r)) => *r,
        _ => return Err(form(i, "needs two register operands")),
    };
    let rt2 = match i.operands().get(1) {
        Some(Operand::Reg(r)) => *r,
        _ => return Err(form(i, "needs two register operands")),
    };
    let mem = match i.operands().get(2) {
        Some(Operand::Mem(m)) => *m,
        _ => return Err(form(i, "expected a memory operand")),
    };
    let load = i.mnemonic.starts_with("ld");
    let (opc, v, bytes) = if rt.class == RegClass::Vec {
        match rt.width {
            Width::W32 => (0b00u32, 1u32, 4u64),
            Width::W64 => (0b01, 1, 8),
            Width::W128 => (0b10, 1, 16),
            _ => return Err(form(i, "a vector pair is s, d or q")),
        }
    } else if i.mnemonic == "ldpsw" {
        (0b01, 0, 4)
    } else {
        match rt.width {
            Width::W32 => (0b00, 0, 4),
            Width::W64 => (0b10, 0, 8),
            _ => return Err(form(i, "a register pair is 32 or 64 bits")),
        }
    };
    let mode_bits = match (i.mnemonic, mem.mode) {
        ("ldnp" | "stnp", AddrMode::Offset) => 0b00u32,
        ("ldnp" | "stnp", _) => return Err(form(i, "a non-temporal pair has no writeback")),
        (_, AddrMode::PostIndex) => 0b01,
        (_, AddrMode::Offset) => 0b10,
        (_, AddrMode::PreIndex) => 0b11,
    };
    if mem.index.is_some() {
        return Err(form(i, "a pair takes no index register"));
    }
    if mem.disp % bytes as i64 != 0 {
        return Err(AsmError::Unaligned {
            what: "pair offset",
            value: mem.disp,
            align: bytes as u32,
        });
    }
    let imm7 = fits(
        mem.disp / bytes as i64,
        7,
        "pair offset in units of the access size",
    )?;
    let rn = num(i, mem.base.ok_or(form(i, "a memory operand needs a base"))?)?;
    Ok((opc << 30)
        | (0b101 << 27)
        | (v << 26)
        | (mode_bits << 23)
        | (u32::from(load) << 22)
        | (imm7 << 15)
        | (num_any(i, rt2)? << 10)
        | (rn << 5)
        | num_any(i, rt)?)
}

// ------------------------------------------------------- bitfields and math

fn bfm(sf: u32, opc: u32, immr: u32, imms: u32, rn: u32, rd: u32) -> u32 {
    (sf << 31)
        | (opc << 29)
        | (0b100110 << 23)
        | (sf << 22)
        | (immr << 16)
        | (imms << 10)
        | (rn << 5)
        | rd
}

fn shift(i: &Insn) -> Result<u32, AsmError> {
    let rd = gpr_op(i, 0)?;
    let rn = gpr_op(i, 1)?;
    let sf = sf_of(rd).map_err(|_| form(i, "a shift is 32 or 64 bits"))?;
    let width = if sf == 1 { 64u32 } else { 32 };
    let third = *i.operands().get(2).ok_or(form(i, "needs three operands"))?;
    if let Operand::Reg(rm) = third {
        let opcode = match i.mnemonic {
            "lsl" => 0b001000u32,
            "lsr" => 0b001001,
            "asr" => 0b001010,
            _ => 0b001011,
        };
        return Ok((sf << 31)
            | (0b11010110 << 21)
            | (num(i, rm)? << 16)
            | (opcode << 10)
            | (num(i, rn)? << 5)
            | num(i, rd)?);
    }
    let v = imm_of(&third).ok_or(form(i, "expected a shift amount"))?;
    let n = unsigned_fits(v, 6, "shift amount")?;
    if n >= width {
        return Err(AsmError::Range {
            what: "shift amount",
            value: v,
            low: 0,
            high: width as i64 - 1,
        });
    }
    let (rd, rn) = (num(i, rd)?, num(i, rn)?);
    Ok(match i.mnemonic {
        "lsl" => bfm(sf, 0b10, (width - n) % width, width - 1 - n, rn, rd),
        "lsr" => bfm(sf, 0b10, n, width - 1, rn, rd),
        "asr" => bfm(sf, 0b00, n, width - 1, rn, rd),
        // A rotate is an extract from a register and itself.
        _ => (sf << 31) | (0b100111 << 23) | (sf << 22) | (rn << 16) | (n << 10) | (rn << 5) | rd,
    })
}

fn dp2(i: &Insn) -> Result<u32, AsmError> {
    let rd = gpr_op(i, 0)?;
    let rn = gpr_op(i, 1)?;
    let rm = gpr_op(i, 2)?;
    let sf = sf_of(rd).map_err(|_| form(i, "this operation is 32 or 64 bits"))?;
    let opcode = match i.mnemonic {
        "udiv" => 0b000010u32,
        "sdiv" => 0b000011,
        "lslv" => 0b001000,
        "lsrv" => 0b001001,
        "asrv" => 0b001010,
        _ => 0b001011,
    };
    Ok((sf << 31)
        | (0b11010110 << 21)
        | (num(i, rm)? << 16)
        | (opcode << 10)
        | (num(i, rn)? << 5)
        | num(i, rd)?)
}

fn dp1(i: &Insn) -> Result<u32, AsmError> {
    let rd = gpr_op(i, 0)?;
    let rn = gpr_op(i, 1)?;
    let sf = sf_of(rd).map_err(|_| form(i, "this operation is 32 or 64 bits"))?;
    let opcode = match (i.mnemonic, sf) {
        ("rbit", _) => 0b000000u32,
        ("rev16", _) => 0b000001,
        ("rev32", 1) => 0b000010,
        ("rev", 0) => 0b000010,
        ("rev", 1) => 0b000011,
        ("clz", _) => 0b000100,
        ("cls", _) => 0b000101,
        _ => return Err(form(i, "this width has no such reverse")),
    };
    Ok((sf << 31)
        | (1 << 30)
        | (0b11010110 << 21)
        | (opcode << 10)
        | (num(i, rn)? << 5)
        | num(i, rd)?)
}

fn bfm_raw(i: &Insn) -> Result<u32, AsmError> {
    let rd = gpr_op(i, 0)?;
    let rn = gpr_op(i, 1)?;
    let sf = sf_of(rd).map_err(|_| form(i, "a bitfield move is 32 or 64 bits"))?;
    let immr = imm_of(i.operands().get(2).ok_or(form(i, "needs immr"))?)
        .ok_or(form(i, "expected immr"))?;
    let imms = imm_of(i.operands().get(3).ok_or(form(i, "needs imms"))?)
        .ok_or(form(i, "expected imms"))?;
    let opc = match i.mnemonic {
        "sbfm" => 0b00u32,
        "bfm" => 0b01,
        _ => 0b10,
    };
    Ok(bfm(
        sf,
        opc,
        unsigned_fits(immr, 6, "immr")?,
        unsigned_fits(imms, 6, "imms")?,
        num(i, rn)?,
        num(i, rd)?,
    ))
}

fn bitfield(i: &Insn) -> Result<u32, AsmError> {
    let rd = gpr_op(i, 0)?;
    let rn = gpr_op(i, 1)?;
    let sf = sf_of(rd).map_err(|_| form(i, "a bitfield operation is 32 or 64 bits"))?;
    let regsize = if sf == 1 { 64u32 } else { 32 };
    let lsb = imm_of(i.operands().get(2).ok_or(form(i, "needs a bit position"))?)
        .ok_or(form(i, "expected a bit position"))?;
    let width = imm_of(i.operands().get(3).ok_or(form(i, "needs a width"))?)
        .ok_or(form(i, "expected a width"))?;
    let lsb = unsigned_fits(lsb, 6, "bit position")?;
    if lsb >= regsize {
        return Err(AsmError::Range {
            what: "bit position",
            value: lsb as i64,
            low: 0,
            high: regsize as i64 - 1,
        });
    }
    if width < 1 || width as u32 > regsize - lsb {
        return Err(AsmError::Range {
            what: "bitfield width",
            value: width,
            low: 1,
            high: (regsize - lsb) as i64,
        });
    }
    let width = width as u32;
    let opc = match i.mnemonic {
        "sbfx" | "sbfiz" => 0b00u32,
        "bfxil" | "bfi" => 0b01,
        _ => 0b10,
    };
    let insert = matches!(i.mnemonic, "sbfiz" | "ubfiz" | "bfi");
    let (immr, imms) = if insert {
        ((regsize - lsb) % regsize, width - 1)
    } else {
        (lsb, lsb + width - 1)
    };
    Ok(bfm(sf, opc, immr, imms, num(i, rn)?, num(i, rd)?))
}

fn extend_op(i: &Insn) -> Result<u32, AsmError> {
    let rd = gpr_op(i, 0)?;
    let rn = gpr_op(i, 1)?;
    let sf = sf_of(rd).map_err(|_| form(i, "an extend is 32 or 64 bits"))?;
    let (opc, imms) = match i.mnemonic {
        "sxtb" => (0b00u32, 7u32),
        "sxth" => (0b00, 15),
        "sxtw" => (0b00, 31),
        "uxtb" => (0b10, 7),
        _ => (0b10, 15),
    };
    if i.mnemonic == "sxtw" && sf == 0 {
        return Err(form(i, "sxtw writes a 64-bit register"));
    }
    if matches!(i.mnemonic, "uxtb" | "uxth") && sf == 1 {
        return Err(form(
            i,
            "there is no 64-bit uxtb or uxth: writing a w register already zero extends",
        ));
    }
    Ok(bfm(sf, opc, 0, imms, num(i, rn)?, num(i, rd)?))
}

fn multiply(i: &Insn) -> Result<u32, AsmError> {
    let rd = gpr_op(i, 0)?;
    let rn = gpr_op(i, 1)?;
    let rm = gpr_op(i, 2)?;
    let sf = sf_of(rd).map_err(|_| form(i, "a multiply is 32 or 64 bits"))?;
    let (op31, o0, long, needs_ra) = match i.mnemonic {
        "madd" => (0b000u32, 0u32, false, true),
        "msub" => (0b000, 1, false, true),
        "mul" => (0b000, 0, false, false),
        "mneg" => (0b000, 1, false, false),
        "smaddl" => (0b001, 0, true, true),
        "smsubl" => (0b001, 1, true, true),
        "smull" => (0b001, 0, true, false),
        "smnegl" => (0b001, 1, true, false),
        "umaddl" => (0b101, 0, true, true),
        "umsubl" => (0b101, 1, true, true),
        "umull" => (0b101, 0, true, false),
        "umnegl" => (0b101, 1, true, false),
        "smulh" => (0b010, 0, false, false),
        _ => (0b110, 0, false, false),
    };
    if long && sf == 0 {
        return Err(form(i, "a widening multiply writes a 64-bit register"));
    }
    let ra = if needs_ra {
        match i.operands().get(3) {
            Some(Operand::Reg(r)) => num(i, *r)?,
            _ => return Err(form(i, "needs an accumulator register")),
        }
    } else {
        31
    };
    Ok((sf << 31)
        | (0b11011 << 24)
        | (op31 << 21)
        | (num(i, rm)? << 16)
        | (o0 << 15)
        | (ra << 10)
        | (num(i, rn)? << 5)
        | num(i, rd)?)
}

fn cond_of(i: &Insn, n: usize) -> Result<u32, AsmError> {
    match i.operands().get(n) {
        Some(Operand::Cond(c)) => Ok(c.0 as u32 & 15),
        _ => Err(form(i, "expected a condition code")),
    }
}

fn csel_bits(m: &str) -> (u32, u32) {
    match m {
        "csel" => (0, 0),
        "csinc" | "cinc" | "cset" => (0, 1),
        "csinv" | "cinv" | "csetm" => (1, 0),
        _ => (1, 1),
    }
}

fn cond_select(sf: u32, op: u32, o2: u32, rm: u32, cond: u32, rn: u32, rd: u32) -> u32 {
    (sf << 31)
        | (op << 30)
        | (0b11010100 << 21)
        | (rm << 16)
        | (cond << 12)
        | (o2 << 10)
        | (rn << 5)
        | rd
}

fn csel(i: &Insn) -> Result<u32, AsmError> {
    let rd = gpr_op(i, 0)?;
    let rn = gpr_op(i, 1)?;
    let rm = gpr_op(i, 2)?;
    let sf = sf_of(rd).map_err(|_| form(i, "a conditional select is 32 or 64 bits"))?;
    let (op, o2) = csel_bits(i.mnemonic);
    Ok(cond_select(
        sf,
        op,
        o2,
        num(i, rm)?,
        cond_of(i, 3)?,
        num(i, rn)?,
        num(i, rd)?,
    ))
}

fn cset(i: &Insn) -> Result<u32, AsmError> {
    let rd = gpr_op(i, 0)?;
    let sf = sf_of(rd).map_err(|_| form(i, "a cset is 32 or 64 bits"))?;
    let cond = cond_of(i, 1)?;
    if cond >= 14 {
        return Err(form(i, "cset has no always or never condition"));
    }
    let (op, o2) = csel_bits(i.mnemonic);
    Ok(cond_select(sf, op, o2, 31, cond ^ 1, 31, num(i, rd)?))
}

fn cinc(i: &Insn) -> Result<u32, AsmError> {
    let rd = gpr_op(i, 0)?;
    let rn = gpr_op(i, 1)?;
    let sf = sf_of(rd).map_err(|_| form(i, "this operation is 32 or 64 bits"))?;
    let cond = cond_of(i, 2)?;
    if cond >= 14 {
        return Err(form(i, "this alias has no always or never condition"));
    }
    let (op, o2) = csel_bits(i.mnemonic);
    let rn = num(i, rn)?;
    Ok(cond_select(sf, op, o2, rn, cond ^ 1, rn, num(i, rd)?))
}

fn ccmp(i: &Insn) -> Result<u32, AsmError> {
    let rn = gpr_op(i, 0)?;
    let sf = sf_of(rn).map_err(|_| form(i, "a conditional compare is 32 or 64 bits"))?;
    let second = *i
        .operands()
        .get(1)
        .ok_or(form(i, "needs a second operand"))?;
    let (rm, imm_form) = match second {
        Operand::Reg(r) => (num(i, r)?, 0u32),
        other => {
            let v = imm_of(&other).ok_or(form(i, "expected a register or an immediate"))?;
            (unsigned_fits(v, 5, "conditional compare immediate")?, 1)
        }
    };
    let nzcv = imm_of(i.operands().get(2).ok_or(form(i, "needs flags"))?)
        .ok_or(form(i, "expected the flag value"))?;
    let nzcv = unsigned_fits(nzcv, 4, "nzcv")?;
    let cond = cond_of(i, 3)?;
    Ok((sf << 31)
        | (u32::from(i.mnemonic == "ccmp") << 30)
        | (1 << 29)
        | (0b11010010 << 21)
        | (rm << 16)
        | (cond << 12)
        | (imm_form << 11)
        | (num(i, rn)? << 5)
        | nzcv)
}

fn adc(i: &Insn) -> Result<u32, AsmError> {
    let rd = gpr_op(i, 0)?;
    let rn = gpr_op(i, 1)?;
    let rm = gpr_op(i, 2)?;
    let sf = sf_of(rd).map_err(|_| form(i, "a carry operation is 32 or 64 bits"))?;
    let sub = u32::from(i.mnemonic.starts_with("sbc"));
    let s = u32::from(i.mnemonic.ends_with('s'));
    Ok(carry(sf, sub, s, num(i, rm)?, num(i, rn)?, num(i, rd)?))
}

fn ngc(i: &Insn) -> Result<u32, AsmError> {
    let rd = gpr_op(i, 0)?;
    let rm = gpr_op(i, 1)?;
    let sf = sf_of(rd).map_err(|_| form(i, "a carry negate is 32 or 64 bits"))?;
    let s = u32::from(i.mnemonic.ends_with('s'));
    Ok(carry(sf, 1, s, num(i, rm)?, 31, num(i, rd)?))
}

fn carry(sf: u32, sub: u32, s: u32, rm: u32, rn: u32, rd: u32) -> u32 {
    (sf << 31) | (sub << 30) | (s << 29) | (0b11010000 << 21) | (rm << 16) | (rn << 5) | rd
}

fn extr(i: &Insn) -> Result<u32, AsmError> {
    let rd = gpr_op(i, 0)?;
    let rn = gpr_op(i, 1)?;
    let rm = gpr_op(i, 2)?;
    let sf = sf_of(rd).map_err(|_| form(i, "an extract is 32 or 64 bits"))?;
    let v = imm_of(i.operands().get(3).ok_or(form(i, "needs a bit position"))?)
        .ok_or(form(i, "expected a bit position"))?;
    let imms = unsigned_fits(v, 6, "extract position")?;
    if sf == 0 && imms >= 32 {
        return Err(AsmError::Range {
            what: "extract position",
            value: v,
            low: 0,
            high: 31,
        });
    }
    Ok((sf << 31)
        | (0b100111 << 23)
        | (sf << 22)
        | (num(i, rm)? << 16)
        | (imms << 10)
        | (num(i, rn)? << 5)
        | num(i, rd)?)
}

/// Four bytes of `nop`, the only padding A64 needs.
pub(crate) const NOP: u32 = 0xd503_201f;

#[cfg(test)]
mod tests {
    use super::*;

    /// Text in, one word out. Every expectation here was produced by
    /// `aarch64-linux-gnu-as` and read back with `objdump -d`, so the table is
    /// a record of what the toolchain says rather than of what this file does.
    const CASES: &[(&str, u32)] = &[
        // Data processing, register and immediate.
        ("add\tx0, x1, x2", 0x8b02_0020),
        ("add\tw0, w1, w2, lsl #3", 0x0b02_0c20),
        ("add\tx0, x1, #0x1, lsl #12", 0x9140_0420),
        ("sub\tsp, sp, #0x10", 0xd100_43ff),
        ("add\tx0, sp, w1, uxtw #2", 0x8b21_4be0),
        ("cmp\tw0, #0x1", 0x7100_041f),
        ("neg\tx0, x1", 0xcb01_03e0),
        ("mvn\tw0, w1", 0x2a21_03e0),
        ("tst\tx0, #0xff", 0xf240_1c1f),
        ("and\tx0, x1, #0xff", 0x9240_1c20),
        ("orr\tw0, w1, w2, ror #7", 0x2ac2_1c20),
        ("adc\tx0, x1, x2", 0x9a02_0020),
        ("extr\tx0, x1, x2, #5", 0x93c2_1420),
        // The moves, including the aliases and what they lower to.
        ("mov\tx0, x1", 0xaa01_03e0),
        ("mov\tsp, x0", 0x9100_001f),
        ("mov\tw0, #0x1234", 0x5282_4680),
        ("mov\tx0, #0xffffffffffffffff", 0x9280_0000),
        ("mov\tw0, #0xffff0000", 0x52bf_ffe0),
        ("movk\tw0, #0x5a5a, lsl #16", 0x72ab_4b40),
        // Loads and stores in each addressing mode the printer emits.
        ("ldr\tx0, [x1, #16]", 0xf940_0820),
        ("ldr\tw0, [x1, x2, lsl #2]", 0xb862_7820),
        ("ldrb\tw0, [x1, #1]", 0x3940_0420),
        ("ldrsw\tx0, [x1, #4]", 0xb980_0420),
        ("str\tx0, [x1], #16", 0xf801_0420),
        ("str\tx0, [x1, #-8]!", 0xf81f_8c20),
        ("ldur\tx0, [x1, #-1]", 0xf85f_f020),
        ("stp\tx29, x30, [sp, #-16]!", 0xa9bf_7bfd),
        ("ldp\tx29, x30, [sp], #16", 0xa8c1_7bfd),
        ("prfm\tpldl1keep, [x0, #8]", 0xf980_0400),
        // Branches and the system odds and ends.
        ("nop", 0xd503_201f),
        ("ret", 0xd65f_03c0),
        ("ret\tx1", 0xd65f_0020),
        ("blr\tx2", 0xd63f_0040),
        ("br\tx3", 0xd61f_0060),
        ("svc\t#0x0", 0xd400_0001),
        ("brk\t#0x1", 0xd420_0020),
        ("dmb\tish", 0xd503_3bbf),
        ("isb\tsy", 0xd503_3fdf),
        ("bti\tc", 0xd503_245f),
        ("paciasp", 0xd503_233f),
        ("autiasp", 0xd503_23bf),
        ("xpaclri", 0xd503_20ff),
        // Shifts, bitfields and extends.
        ("lsl\tw0, w1, #3", 0x531d_7020),
        ("lsr\tx0, x1, #5", 0xd345_fc20),
        ("asr\tw0, w1, w2", 0x1ac2_2820),
        ("ubfx\tx0, x1, #4, #8", 0xd344_2c20),
        ("sbfiz\tw0, w1, #2, #6", 0x131e_1420),
        ("sxtb\tx0, w1", 0x9340_1c20),
        ("uxth\tw0, w1", 0x5300_3c20),
        // Multiply, divide and the conditional selects.
        ("mul\tx0, x1, x2", 0x9b02_7c20),
        ("madd\tw0, w1, w2, w3", 0x1b02_0c20),
        ("smull\tx0, w1, w2", 0x9b22_7c20),
        ("udiv\tx0, x1, x2", 0x9ac2_0820),
        ("csel\tx0, x1, x2, eq", 0x9a82_0020),
        ("cset\tw0, ne", 0x1a9f_07e0),
        ("cinc\tx0, x1, lt", 0x9a81_a420),
        ("ccmp\tx0, #0x1, #0x2, eq", 0xfa41_0802),
        ("rbit\tx0, x1", 0xdac0_0020),
        ("clz\tw0, w1", 0x5ac0_1020),
        ("rev\tx0, x1", 0xdac0_0c20),
    ];

    fn asm(text: &str, at: u64) -> u32 {
        let e = crate::assemble(&r12e_core::Arch::AArch64, text, Addr(at))
            .unwrap_or_else(|e| panic!("{text}: {e}"));
        u32::from_le_bytes(e.bytes().try_into().expect("four bytes"))
    }

    #[test]
    fn the_mnemonic_table_is_sorted_and_unique() {
        for w in MNEMONICS.windows(2) {
            assert!(w[0] < w[1], "{} then {}", w[0], w[1]);
        }
        for w in NAMES.windows(2) {
            assert!(w[0] < w[1], "{} then {}", w[0], w[1]);
        }
    }

    #[test]
    fn the_encodings_are_the_toolchains() {
        for (text, want) in CASES {
            assert_eq!(asm(text, 0x1000), *want, "{text}");
        }
    }

    /// Everything above, back through the decoder: the encoder and the decoder
    /// have to be inverses, not merely both plausible.
    #[test]
    fn every_case_decodes_to_what_was_written() {
        for (text, _) in CASES {
            let bytes = asm(text, 0x1000).to_le_bytes();
            let back = r12e_arch::aarch64::decode(&bytes, Addr(0x1000))
                .unwrap_or_else(|| panic!("{text} does not decode"));
            let printed = r12e_arch::aarch64::format(
                &back,
                r12e_arch::aarch64::text::Style { objdump: false },
            );
            assert_eq!(&printed, text, "{text}");
        }
    }

    #[test]
    fn branches_are_relative_to_where_the_instruction_sits() {
        assert_eq!(asm("b\t0x1004", 0x1000), 0x1400_0001);
        assert_eq!(asm("bl\t0xffc", 0x1000), 0x97ff_ffff);
        assert_eq!(asm("b.eq\t0x1008", 0x1000), 0x5400_0040);
        assert_eq!(asm("cbz\tx0, 0x1008", 0x1000), 0xb400_0040);
        assert_eq!(asm("tbnz\tw0, #3, 0x1008", 0x1000), 0x3718_0040);
        // adr is byte relative and adrp is page relative, from the page the
        // instruction is on rather than from the instruction.
        assert_eq!(asm("adr\tx0, 0x1008", 0x1000), 0x1000_0040);
        // Two pages up: the low two bits of the page count live at the top
        // of the word, which is the field layout most likely to be got
        // backwards and the reason this case is written out.
        assert_eq!(asm("adrp\tx0, 0x3000", 0x1000), 0xd000_0000);
    }

    /// Spellings the printer never emits but a person writes, including the
    /// move-wide instructions the `mov` alias hides. These are checked for
    /// bytes only, since by construction they print back as the alias.
    #[test]
    fn the_spellings_a_person_writes_encode_the_same() {
        // The shifted add immediate: printed with the shift, written whole.
        assert_eq!(asm("add\tx0, x1, #0x1000", 0x1000), 0x9140_0420);
        assert_eq!(asm("add\tx0, x1, #0x1, lsl #12", 0x1000), 0x9140_0420);
        // The all-ones move: printed as the bit pattern, written as -1.
        assert_eq!(asm("mov\tx0, #-0x1", 0x1000), 0x9280_0000);
        assert_eq!(asm("mov\tx0, #0xffffffffffffffff", 0x1000), 0x9280_0000);
        // What `mov` lowers to, written out.
        assert_eq!(asm("movz\tx0, #0x1234, lsl #16", 0x1000), 0xd2a2_4680);
        assert_eq!(asm("mov\tx0, #0x12340000", 0x1000), 0xd2a2_4680);
        assert_eq!(asm("movn\tx0, #0x0", 0x1000), 0x9280_0000);
        assert_eq!(asm("movz\tw0, #0x1234", 0x1000), 0x5282_4680);
        // The barrier option is `sy` whether it is written or left out.
        assert_eq!(asm("isb", 0x1000), 0xd503_3fdf);
        // `sal` has no A64 spelling, but `lsl` by a register does, and the
        // alias and the raw instruction are the same bytes.
        assert_eq!(
            asm("lsl\tw0, w1, w2", 0x1000),
            asm("lslv\tw0, w1, w2", 0x1000)
        );
        assert_eq!(
            asm("asr\tx0, x1, #5", 0x1000),
            asm("sbfm\tx0, x1, #5, #63", 0x1000)
        );
    }

    #[test]
    fn a_target_the_encoding_cannot_reach_is_refused() {
        for text in [
            "b.eq\t0x200000",
            "cbz\tx0, 0x200000",
            "tbz\tx0, #1, 0x20000",
        ] {
            let e = crate::assemble(&r12e_core::Arch::AArch64, text, Addr(0)).expect_err(text);
            assert!(matches!(e, AsmError::BranchRange { .. }), "{text}: {e}");
        }
        // An unaligned target is its own error, not a rounded displacement.
        let e = crate::assemble(&r12e_core::Arch::AArch64, "b\t0x1002", Addr(0x1000))
            .expect_err("unaligned");
        assert!(matches!(e, AsmError::Unaligned { .. }), "{e}");
    }

    #[test]
    fn a_value_no_immediate_can_build_is_refused_rather_than_approximated() {
        let e = crate::assemble(&r12e_core::Arch::AArch64, "mov\tx0, #0x123456789", Addr(0))
            .expect_err("no single immediate builds this");
        assert!(matches!(e, AsmError::NoEncoding { .. }), "{e}");
        let e = crate::assemble(&r12e_core::Arch::AArch64, "and\tx0, x1, #0x3", Addr(0));
        assert!(e.is_ok(), "a rotated run of ones does encode");
        let e = crate::assemble(&r12e_core::Arch::AArch64, "and\tx0, x1, #0x5", Addr(0))
            .expect_err("0x5 is not a rotated run of ones");
        assert!(matches!(e, AsmError::NoEncoding { .. }), "{e}");
    }

    #[test]
    fn simd_is_declined_by_name_rather_than_called_a_typo() {
        let e = crate::assemble(
            &r12e_core::Arch::AArch64,
            "add\tv0.4s, v1.4s, v2.4s",
            Addr(0),
        )
        .expect_err("no SIMD encoder");
        assert!(
            e.to_string().contains("SIMD"),
            "the refusal should say what it is: {e}"
        );
    }
}
