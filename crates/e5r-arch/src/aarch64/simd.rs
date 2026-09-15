//! Advanced SIMD.
//!
//! The groups a compiler and a hand-written library actually emit: the
//! three-operand arithmetic, the immediate forms, the shifts, the lane moves,
//! the table lookups, the structure loads and stores, and the AES instructions.
//! Scalable Vector Extension encodings are not here; they decode as nothing,
//! which the coverage number records honestly.

use e5r_core::Addr;

use crate::insn::{AddrMode, Flow, Insn, Lanes, Mem, Operand, Reg, Width};

use super::{bit, bits};

/// The lane arrangement for a `size` field and a `Q` bit.
fn lanes(size: u32, q: u32) -> Option<Lanes> {
    Some(match (size, q) {
        (0b00, 0) => Lanes::B8,
        (0b00, 1) => Lanes::B16,
        (0b01, 0) => Lanes::H4,
        (0b01, 1) => Lanes::H8,
        (0b10, 0) => Lanes::S2,
        (0b10, 1) => Lanes::S4,
        (0b11, 0) => Lanes::D1,
        (0b11, 1) => Lanes::D2,
        _ => return None,
    })
}

/// The wider arrangement a lengthening instruction writes.
fn wide_lanes(size: u32) -> Option<Lanes> {
    Some(match size {
        0b00 => Lanes::H8,
        0b01 => Lanes::S4,
        0b10 => Lanes::D2,
        _ => return None,
    })
}

fn v(num: u32, l: Lanes) -> Operand {
    Operand::Vector(num as u8, l)
}

fn ins(addr: Addr, m: &'static str) -> Insn {
    Insn::new(addr, 4, m, Flow::Next)
}

/// Decode an Advanced SIMD instruction, or `None`.
pub fn decode(w: u32, addr: Addr) -> Option<Insn> {
    // Crypto AES: one source, one destination, byte lanes only.
    if w & 0xFF3E_0C00 == 0x4E28_0800 {
        let mnem = match bits(w, 16, 12) {
            0b00100 => "aese",
            0b00101 => "aesd",
            0b00110 => "aesmc",
            0b00111 => "aesimc",
            _ => return None,
        };
        let mut i = ins(addr, mnem);
        i.push(v(bits(w, 4, 0), Lanes::B16));
        i.push(v(bits(w, 9, 5), Lanes::B16));
        return Some(i);
    }

    // Table lookup, and the permutes that share its shape.
    if w & 0xBF20_8C00 == 0x0E00_0000 {
        return table_lookup(w, addr);
    }
    if w & 0xBF20_8C00 == 0x0E00_0800 {
        return permute(w, addr);
    }
    // Extract: a byte-granular concatenation of two registers.
    if w & 0xBF20_8400 == 0x2E00_0000 {
        let q = bit(w, 30);
        let l = if q == 1 { Lanes::B16 } else { Lanes::B8 };
        let mut i = ins(addr, "ext");
        i.push(v(bits(w, 4, 0), l));
        i.push(v(bits(w, 9, 5), l));
        i.push(v(bits(w, 20, 16), l));
        i.push(Operand::Count(bits(w, 14, 11) as i64));
        return Some(i);
    }
    // Copy: dup, ins, umov, smov.
    if w & 0x9FE0_8400 == 0x0E00_0400 {
        return copy(w, addr);
    }
    // Modified immediate, which is also where the vector fmov lives.
    if w & 0x9FF8_0400 == 0x0F00_0400 {
        return modified_immediate(w, addr);
    }
    // Shift by immediate, distinguished from the above by a non-zero immh.
    if w & 0x9F80_0400 == 0x0F00_0400 && bits(w, 22, 19) != 0 {
        return shift_immediate(w, addr);
    }
    // Two-register miscellaneous.
    if w & 0x9F3E_0C00 == 0x0E20_0800 {
        return two_reg_misc(w, addr);
    }
    // Scalar two-register miscellaneous: the conversions that read and write
    // a vector register rather than a general one.
    if w & 0xDF3E_0C00 == 0x5E20_0800 {
        let u = bit(w, 29);
        let opcode = bits(w, 16, 12);
        let mnem = match (opcode, u) {
            (0b11101, 0) => "scvtf",
            (0b11101, 1) => "ucvtf",
            (0b11011, 0) => "fcvtzs",
            (0b11011, 1) => "fcvtzu",
            (0b11010, 0) => "fcvtns",
            (0b11010, 1) => "fcvtnu",
            (0b11100, 0) => "fcvtas",
            (0b11100, 1) => "fcvtau",
            _ => return None,
        };
        let width = if bit(w, 22) == 1 {
            Width::W64
        } else {
            Width::W32
        };
        let mut i = ins(addr, mnem);
        i.push(Operand::Reg(Reg::vec(bits(w, 4, 0) as u8, width)));
        i.push(Operand::Reg(Reg::vec(bits(w, 9, 5) as u8, width)));
        return Some(i);
    }
    // Scalar pairwise: one register folded to a scalar.
    if w & 0xDF3E_0C00 == 0x5E30_0800 {
        return scalar_pairwise(w, addr);
    }
    // Across lanes.
    if w & 0x9F3E_0C00 == 0x0E30_0800 {
        return across_lanes(w, addr);
    }
    // Three different: the lengthening and widening forms.
    if w & 0x9F20_0C00 == 0x0E20_0000 {
        return three_different(w, addr);
    }
    // Three same.
    if w & 0x9F20_0400 == 0x0E20_0400 {
        return three_same(w, addr);
    }
    // Load and store of multiple structures.
    if w & 0xBFBF_0000 == 0x0C00_0000 || w & 0xBFA0_0000 == 0x0C80_0000 {
        return load_store_structures(w, addr);
    }
    None
}

fn table_lookup(w: u32, addr: Addr) -> Option<Insn> {
    if bits(w, 23, 22) != 0 {
        return None;
    }
    let q = bit(w, 30);
    let l = if q == 1 { Lanes::B16 } else { Lanes::B8 };
    let len = bits(w, 14, 13) + 1;
    let mut i = ins(addr, if bit(w, 12) == 1 { "tbx" } else { "tbl" });
    i.push(v(bits(w, 4, 0), l));
    i.push(Operand::VectorList(
        bits(w, 9, 5) as u8,
        len as u8,
        Lanes::B16,
    ));
    i.push(v(bits(w, 20, 16), l));
    Some(i)
}

fn permute(w: u32, addr: Addr) -> Option<Insn> {
    let l = lanes(bits(w, 23, 22), bit(w, 30))?;
    let mnem = match bits(w, 14, 12) {
        0b001 => "uzp1",
        0b010 => "trn1",
        0b011 => "zip1",
        0b101 => "uzp2",
        0b110 => "trn2",
        0b111 => "zip2",
        _ => return None,
    };
    let mut i = ins(addr, mnem);
    i.push(v(bits(w, 4, 0), l));
    i.push(v(bits(w, 9, 5), l));
    i.push(v(bits(w, 20, 16), l));
    Some(i)
}

/// The element width and index an `imm5` field selects.
fn elem(imm5: u32) -> Option<(Width, u8)> {
    if imm5 & 1 != 0 {
        Some((Width::W8, (imm5 >> 1) as u8))
    } else if imm5 & 2 != 0 {
        Some((Width::W16, (imm5 >> 2) as u8))
    } else if imm5 & 4 != 0 {
        Some((Width::W32, (imm5 >> 3) as u8))
    } else if imm5 & 8 != 0 {
        Some((Width::W64, (imm5 >> 4) as u8))
    } else {
        None
    }
}

fn copy(w: u32, addr: Addr) -> Option<Insn> {
    let q = bit(w, 30);
    let op = bit(w, 29);
    let imm5 = bits(w, 20, 16);
    let imm4 = bits(w, 14, 11);
    let rd = bits(w, 4, 0);
    let rn = bits(w, 9, 5);
    let (width, index) = elem(imm5)?;
    let size = match width {
        Width::W8 => 0,
        Width::W16 => 1,
        Width::W32 => 2,
        _ => 3,
    };

    // op set means an insert from one lane to another.
    if op == 1 {
        if q == 0 {
            return None;
        }
        let src = elem(imm5).map(|(wd, _)| wd)?;
        let shift = match src {
            Width::W8 => 0,
            Width::W16 => 1,
            Width::W32 => 2,
            _ => 3,
        };
        let mut i = ins(addr, "mov");
        i.push(Operand::VectorLane(rd as u8, width, index));
        i.push(Operand::VectorLane(rn as u8, width, (imm4 >> shift) as u8));
        return Some(i);
    }

    match imm4 {
        // dup from a vector element.
        0b0000 => {
            let l = lanes(size, q)?;
            let mut i = ins(addr, "dup");
            i.push(v(rd, l));
            i.push(Operand::VectorLane(rn as u8, width, index));
            Some(i)
        }
        // dup from a general register.
        0b0001 => {
            let l = lanes(size, q)?;
            let mut i = ins(addr, "dup");
            i.push(v(rd, l));
            i.push(Operand::Reg(super::gpr_for(rn, size == 3)));
            Some(i)
        }
        // smov and umov.
        0b0101 | 0b0111 => {
            let signed = imm4 == 0b0101;
            let wide = q == 1;
            // umov of a full lane is spelled mov.
            let mnem = if signed {
                "smov"
            } else if (wide && size == 3) || (!wide && size == 2) {
                "mov"
            } else {
                "umov"
            };
            let mut i = ins(addr, mnem);
            i.push(Operand::Reg(super::gpr_for(rd, wide)));
            i.push(Operand::VectorLane(rn as u8, width, index));
            Some(i)
        }
        // ins from a general register.
        0b0011 => {
            let mut i = ins(addr, "mov");
            i.push(Operand::VectorLane(rd as u8, width, index));
            i.push(Operand::Reg(super::gpr_for(rn, size == 3)));
            Some(i)
        }
        _ => None,
    }
}

/// Expand the `abcdefgh` immediate a `movi` carries, per `AdvSIMDExpandImm`.
fn advsimd_expand(cmode: u32, op: u32, imm8: u64) -> u64 {
    let replicate32 = |v: u64| v | (v << 32);
    match cmode >> 1 {
        0b000 => replicate32(imm8),
        0b001 => replicate32(imm8 << 8),
        0b010 => replicate32(imm8 << 16),
        0b011 => replicate32(imm8 << 24),
        0b100 => {
            let h = imm8 | (imm8 << 16);
            h | (h << 32)
        }
        0b101 => {
            let h = (imm8 << 8) | (imm8 << 24);
            h | (h << 32)
        }
        0b110 => {
            let v = if cmode & 1 == 0 {
                (imm8 << 8) | 0xff
            } else {
                (imm8 << 16) | 0xffff
            };
            replicate32(v)
        }
        // cmode 1110 with op set is the 64-bit form: each bit of the
        // immediate becomes a whole byte.
        _ if cmode & 1 == 0 && op == 1 => {
            let mut out = 0u64;
            for i in 0..8 {
                if imm8 >> i & 1 != 0 {
                    out |= 0xffu64 << (i * 8);
                }
            }
            out
        }
        _ => replicate32(imm8),
    }
}

fn modified_immediate(w: u32, addr: Addr) -> Option<Insn> {
    let q = bit(w, 30);
    let op = bit(w, 29);
    let cmode = bits(w, 15, 12);
    let o2 = bit(w, 11);
    let imm8 = ((bits(w, 18, 16) << 5) | bits(w, 9, 5)) as u64;
    let rd = bits(w, 4, 0);

    // The floating point forms.
    if o2 == 0 && cmode == 0b1111 {
        let l = if op == 1 {
            if q == 0 {
                return None;
            }
            Lanes::D2
        } else {
            lanes(0b10, q)?
        };
        let mut i = ins(addr, "fmov");
        i.push(v(rd, l));
        i.push(Operand::FpImm(super::vfp_expand_imm(imm8 as u8)));
        return Some(i);
    }
    if o2 != 0 {
        return None;
    }

    // cmode and op together name the instruction, the lane width, and the
    // shift kind. This is the manual's table rather than a pattern.
    let high = cmode >> 1;
    let odd = cmode & 1 == 1;
    let (mnem, size, shift, msl) = match (high, odd, op) {
        (0b000..=0b011, false, 0) => ("movi", 0b10, (high as u8) * 8, false),
        (0b000..=0b011, true, 0) => ("orr", 0b10, (high as u8) * 8, false),
        (0b000..=0b011, false, 1) => ("mvni", 0b10, (high as u8) * 8, false),
        (0b000..=0b011, true, 1) => ("bic", 0b10, (high as u8) * 8, false),
        (0b100 | 0b101, false, 0) => ("movi", 0b01, ((high as u8) - 4) * 8, false),
        (0b100 | 0b101, true, 0) => ("orr", 0b01, ((high as u8) - 4) * 8, false),
        (0b100 | 0b101, false, 1) => ("mvni", 0b01, ((high as u8) - 4) * 8, false),
        (0b100 | 0b101, true, 1) => ("bic", 0b01, ((high as u8) - 4) * 8, false),
        // Shifting ones: the shift is spelled `msl`.
        (0b110, _, 0) => ("movi", 0b10, if odd { 16 } else { 8 }, true),
        (0b110, _, 1) => ("mvni", 0b10, if odd { 16 } else { 8 }, true),
        // Byte lanes, and the 64-bit pattern form.
        (0b111, false, 0) => ("movi", 0b00, 0, false),
        (0b111, false, 1) => {
            // A 64-bit pattern per lane, printed on a scalar when Q is clear.
            let value = advsimd_expand(cmode, op, imm8);
            let mut i = ins(addr, "movi");
            if q == 1 {
                i.push(v(rd, Lanes::D2));
            } else {
                i.push(Operand::Reg(Reg::vec(rd as u8, Width::W64)));
            }
            i.push(Operand::UImm(value));
            return Some(i);
        }
        _ => return None,
    };

    let mut i = ins(addr, mnem);
    i.push(v(rd, lanes(size, q)?));
    i.push(Operand::UImm(imm8));
    if shift != 0 {
        i.push(Operand::ShiftOp(
            if msl {
                crate::insn::Shift::Msl
            } else {
                crate::insn::Shift::Lsl
            },
            shift,
        ));
    }
    Some(i)
}

fn shift_immediate(w: u32, addr: Addr) -> Option<Insn> {
    let q = bit(w, 30);
    let u = bit(w, 29);
    let immh = bits(w, 22, 19);
    let immb = bits(w, 18, 16);
    let opcode = bits(w, 15, 11);
    let rd = bits(w, 4, 0);
    let rn = bits(w, 9, 5);

    // The element size is the position of the highest set bit of immh.
    let size = match immh {
        0b0001 => 0,
        0b0010 | 0b0011 => 1,
        0b0100..=0b0111 => 2,
        0b1000..=0b1111 => 3,
        _ => return None,
    };
    if size == 3 && q == 0 {
        return None;
    }
    let l = lanes(size, q)?;
    let esize = 8u32 << size;
    let imm = (immh << 3) | immb;
    let right = esize * 2 - imm;
    let left = imm - esize;

    let (mnem, amount, narrow) = match (opcode, u) {
        (0b00000, 0) => ("sshr", right, false),
        (0b00000, 1) => ("ushr", right, false),
        (0b00010, 0) => ("ssra", right, false),
        (0b00010, 1) => ("usra", right, false),
        (0b00100, 0) => ("srshr", right, false),
        (0b00100, 1) => ("urshr", right, false),
        (0b00110, 0) => ("srsra", right, false),
        (0b00110, 1) => ("ursra", right, false),
        (0b01000, 1) => ("sri", right, false),
        (0b01010, 0) => ("shl", left, false),
        (0b01010, 1) => ("sli", left, false),
        (0b10000, 0) => ("shrn", right, true),
        (0b10000, 1) => ("sqshrun", right, true),
        (0b10001, 0) => ("rshrn", right, true),
        (0b10100, 0) => ("sshll", left, true),
        (0b10100, 1) => ("ushll", left, true),
        _ => return None,
    };

    // A lengthening shift of zero is spelled as an extend.
    let mnem: &'static str = match (mnem, amount, q) {
        ("sshll", 0, 0) => "sxtl",
        ("sshll", 0, 1) => "sxtl2",
        ("ushll", 0, 0) => "uxtl",
        ("ushll", 0, 1) => "uxtl2",
        (other, _, _) => other,
    };
    let extend = matches!(mnem, "sxtl" | "sxtl2" | "uxtl" | "uxtl2");

    let mut i = ins(addr, mnem);
    if narrow {
        // A narrowing shift writes half-width lanes and reads full ones; a
        // lengthening one does the reverse.
        let wide = wide_lanes(size)?;
        if mnem.ends_with("shll") || extend {
            i.push(v(rd, wide));
            i.push(v(rn, lanes(size, q)?));
        } else {
            i.push(v(rd, lanes(size, q)?));
            i.push(v(rn, wide));
        }
    } else {
        i.push(v(rd, l));
        i.push(v(rn, l));
    }
    if !extend {
        i.push(Operand::Count(amount as i64));
    }
    Some(i)
}

fn two_reg_misc(w: u32, addr: Addr) -> Option<Insn> {
    let q = bit(w, 30);
    let u = bit(w, 29);
    let size = bits(w, 23, 22);
    let opcode = bits(w, 16, 12);
    let l = lanes(size, q)?;
    let rd = bits(w, 4, 0);
    let rn = bits(w, 9, 5);

    let (mnem, zero) = match (opcode, u) {
        (0b00000, 0) => ("rev64", false),
        (0b00000, 1) => ("rev32", false),
        (0b00001, 0) => ("rev16", false),
        (0b00100, 0) => ("cls", false),
        (0b00100, 1) => ("clz", false),
        (0b00101, 0) => ("cnt", false),
        // objdump spells the bitwise NOT `mvn`, as the manual's alias does.
        (0b00101, 1) => ("mvn", false),
        (0b00111, 0) => ("sqabs", false),
        (0b00111, 1) => ("sqneg", false),
        (0b01000, 0) => ("cmgt", true),
        (0b01000, 1) => ("cmge", true),
        (0b01001, 0) => ("cmeq", true),
        (0b01001, 1) => ("cmle", true),
        (0b01010, 0) => ("cmlt", true),
        (0b01011, 0) => ("abs", false),
        (0b01011, 1) => ("neg", false),
        (0b10010, 0) => ("xtn", false),
        (0b10010, 1) => ("sqxtun", false),
        (0b10100, 0) => ("sqxtn", false),
        (0b10100, 1) => ("uqxtn", false),
        _ => return None,
    };

    // A narrowing move writing the upper half of its destination is spelled
    // with a trailing `2`.
    let narrowing = matches!(mnem, "xtn" | "sqxtn" | "uqxtn" | "sqxtun");
    let mnem = if narrowing && q == 1 {
        match mnem {
            "xtn" => "xtn2",
            "sqxtn" => "sqxtn2",
            "uqxtn" => "uqxtn2",
            _ => "sqxtun2",
        }
    } else {
        mnem
    };
    let mut i = ins(addr, mnem);
    i.push(v(rd, l));
    // The narrowing moves read the next arrangement up.
    if narrowing {
        i.push(v(rn, wide_lanes(size)?));
    } else {
        i.push(v(rn, l));
    }
    if zero {
        i.push(Operand::Count(0));
    }
    Some(i)
}

/// The scalar pairwise forms: two lanes of one register folded into a scalar.
fn scalar_pairwise(w: u32, addr: Addr) -> Option<Insn> {
    let u = bit(w, 29);
    let size = bits(w, 23, 22);
    let opcode = bits(w, 16, 12);
    let (mnem, width, lanes) = match (opcode, u) {
        (0b11011, 0) if size == 0b11 => ("addp", Width::W64, Lanes::D2),
        (0b01101, 1) => {
            let half = size & 1 == 0;
            (
                "faddp",
                if half { Width::W32 } else { Width::W64 },
                if half { Lanes::S2 } else { Lanes::D2 },
            )
        }
        (0b01100, 1) => {
            let half = size & 1 == 0;
            (
                "fmaxnmp",
                if half { Width::W32 } else { Width::W64 },
                if half { Lanes::S2 } else { Lanes::D2 },
            )
        }
        (0b01111, 1) => {
            let half = size & 1 == 0;
            (
                "fmaxp",
                if half { Width::W32 } else { Width::W64 },
                if half { Lanes::S2 } else { Lanes::D2 },
            )
        }
        _ => return None,
    };
    let mut i = ins(addr, mnem);
    i.push(Operand::Reg(Reg::vec(bits(w, 4, 0) as u8, width)));
    i.push(v(bits(w, 9, 5), lanes));
    Some(i)
}

fn across_lanes(w: u32, addr: Addr) -> Option<Insn> {
    let q = bit(w, 30);
    let u = bit(w, 29);
    let size = bits(w, 23, 22);
    let opcode = bits(w, 16, 12);
    let rd = bits(w, 4, 0);
    let rn = bits(w, 9, 5);
    let mnem = match (opcode, u) {
        (0b00011, 0) => "saddlv",
        (0b00011, 1) => "uaddlv",
        (0b01010, 0) => "smaxv",
        (0b01010, 1) => "umaxv",
        (0b11010, 0) => "sminv",
        (0b11010, 1) => "uminv",
        (0b11011, 0) => "addv",
        _ => return None,
    };
    // The destination is a scalar of the lane width, except for the long adds,
    // which accumulate into twice it.
    let long = opcode == 0b00011;
    let width = match (size, long) {
        (0b00, false) => Width::W8,
        (0b01, false) | (0b00, true) => Width::W16,
        (_, false) | (0b01, true) => Width::W32,
        _ => Width::W64,
    };
    let mut i = ins(addr, mnem);
    i.push(Operand::Reg(Reg::vec(rd as u8, width)));
    i.push(v(rn, lanes(size, q)?));
    Some(i)
}

fn three_different(w: u32, addr: Addr) -> Option<Insn> {
    let q = bit(w, 30);
    let u = bit(w, 29);
    let size = bits(w, 23, 22);
    let opcode = bits(w, 15, 12);
    let rd = bits(w, 4, 0);
    let rn = bits(w, 9, 5);
    let rm = bits(w, 20, 16);

    let mnem: &'static str = match (opcode, u, q) {
        (0b0000, 0, 0) => "saddl",
        (0b0000, 0, 1) => "saddl2",
        (0b0000, 1, 0) => "uaddl",
        (0b0000, 1, 1) => "uaddl2",
        (0b0010, 0, 0) => "ssubl",
        (0b0010, 0, 1) => "ssubl2",
        (0b0010, 1, 0) => "usubl",
        (0b0010, 1, 1) => "usubl2",
        (0b1000, 0, 0) => "smlal",
        (0b1000, 0, 1) => "smlal2",
        (0b1000, 1, 0) => "umlal",
        (0b1000, 1, 1) => "umlal2",
        (0b1010, 0, 0) => "smlsl",
        (0b1010, 0, 1) => "smlsl2",
        (0b1010, 1, 0) => "umlsl",
        (0b1010, 1, 1) => "umlsl2",
        (0b1100, 0, 0) => "smull",
        (0b1100, 0, 1) => "smull2",
        (0b1100, 1, 0) => "umull",
        (0b1100, 1, 1) => "umull2",
        (0b1110, 0, 0) => "pmull",
        (0b1110, 0, 1) => "pmull2",
        _ => return None,
    };
    let narrow = lanes(size, q)?;
    let wide = wide_lanes(size)?;
    let mut i = ins(addr, mnem);
    i.push(v(rd, wide));
    i.push(v(rn, narrow));
    i.push(v(rm, narrow));
    Some(i)
}

fn three_same(w: u32, addr: Addr) -> Option<Insn> {
    let q = bit(w, 30);
    let u = bit(w, 29);
    let size = bits(w, 23, 22);
    let opcode = bits(w, 15, 11);
    let rd = bits(w, 4, 0);
    let rn = bits(w, 9, 5);
    let rm = bits(w, 20, 16);

    // The logical group takes its arrangement from Q alone.
    if opcode == 0b00011 {
        let l = if q == 1 { Lanes::B16 } else { Lanes::B8 };
        let mnem = match (u, size) {
            (0, 0b00) => "and",
            (0, 0b01) => "bic",
            (0, 0b10) => "orr",
            (0, 0b11) => "orn",
            (1, 0b00) => "eor",
            (1, 0b01) => "bsl",
            (1, 0b10) => "bit",
            _ => "bif",
        };
        // `orr` with the same source twice is how a vector move is spelled.
        if mnem == "orr" && rn == rm {
            let mut i = ins(addr, "mov");
            i.push(v(rd, l));
            i.push(v(rn, l));
            return Some(i);
        }
        let mut i = ins(addr, mnem);
        i.push(v(rd, l));
        i.push(v(rn, l));
        i.push(v(rm, l));
        return Some(i);
    }

    let mnem: &'static str = match (opcode, u) {
        (0b00000, 0) => "shadd",
        (0b00000, 1) => "uhadd",
        (0b00001, 0) => "sqadd",
        (0b00001, 1) => "uqadd",
        (0b00010, 0) => "srhadd",
        (0b00010, 1) => "urhadd",
        (0b00100, 0) => "shsub",
        (0b00100, 1) => "uhsub",
        (0b00101, 0) => "sqsub",
        (0b00101, 1) => "uqsub",
        (0b00110, 0) => "cmgt",
        (0b00110, 1) => "cmhi",
        (0b00111, 0) => "cmge",
        (0b00111, 1) => "cmhs",
        (0b01000, 0) => "sshl",
        (0b01000, 1) => "ushl",
        (0b01001, 0) => "sqshl",
        (0b01001, 1) => "uqshl",
        (0b01010, 0) => "srshl",
        (0b01010, 1) => "urshl",
        (0b01011, 0) => "sqrshl",
        (0b01011, 1) => "uqrshl",
        (0b01100, 0) => "smax",
        (0b01100, 1) => "umax",
        (0b01101, 0) => "smin",
        (0b01101, 1) => "umin",
        (0b01110, 0) => "sabd",
        (0b01110, 1) => "uabd",
        (0b01111, 0) => "saba",
        (0b01111, 1) => "uaba",
        (0b10000, 0) => "add",
        (0b10000, 1) => "sub",
        (0b10001, 0) => "cmtst",
        (0b10001, 1) => "cmeq",
        (0b10010, 0) => "mla",
        (0b10010, 1) => "mls",
        (0b10011, 0) => "mul",
        (0b10011, 1) => "pmul",
        (0b10100, 0) => "smaxp",
        (0b10100, 1) => "umaxp",
        (0b10101, 0) => "sminp",
        (0b10101, 1) => "uminp",
        (0b10111, 0) => "addp",
        _ => return None,
    };
    let l = lanes(size, q)?;
    let mut i = ins(addr, mnem);
    i.push(v(rd, l));
    i.push(v(rn, l));
    i.push(v(rm, l));
    Some(i)
}

/// LD1 through LD4 and ST1 through ST4, in their multiple-structure forms.
fn load_store_structures(w: u32, addr: Addr) -> Option<Insn> {
    let q = bit(w, 30);
    let load = bit(w, 22) == 1;
    let post = bit(w, 23) == 1;
    let opcode = bits(w, 15, 12);
    let size = bits(w, 11, 10);
    let rn = bits(w, 9, 5);
    let rt = bits(w, 4, 0);
    let rm = bits(w, 20, 16);

    let (base, count) = match opcode {
        0b0000 => ("4", 4u32),
        0b0010 => ("1", 4),
        0b0100 => ("3", 3),
        0b0110 => ("1", 3),
        0b0111 => ("1", 1),
        0b1000 => ("2", 2),
        0b1010 => ("1", 2),
        _ => return None,
    };
    let mnem: &'static str = match (load, base) {
        (true, "1") => "ld1",
        (true, "2") => "ld2",
        (true, "3") => "ld3",
        (true, "4") => "ld4",
        (false, "1") => "st1",
        (false, "2") => "st2",
        (false, "3") => "st3",
        _ => "st4",
    };
    let l = lanes(size, q)?;
    let bytes = if q == 1 { 16 } else { 8 } * count as u64;

    let mut i = ins(addr, mnem);
    i.push(Operand::VectorList(rt as u8, count as u8, l));
    i.push(Operand::Mem(Mem {
        seg: None,
        base: Some(super::rsp_for(rn)),
        index: (post && rm != 31).then(|| (super::gpr_for(rm, true), crate::insn::Extend::Lsl, 0)),
        disp: if post && rm == 31 { bytes as i64 } else { 0 },
        mode: if post {
            AddrMode::PostIndex
        } else {
            AddrMode::Offset
        },
        size: bytes,
    }));
    Some(i)
}
