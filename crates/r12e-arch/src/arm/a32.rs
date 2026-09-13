//! A32 decode.
//!
//! The top-level split follows the architecture reference manual's A5 decode
//! tree on bits 27:25, and each group below is one of its tables. Condition
//! 15 is not a condition at all but a second instruction space, so it leaves
//! first.

use r12e_core::Addr;

use crate::insn::{AddrMode, Flow, Insn, Mem, Operand};

use super::text::{decimal, index, minus_zero};
use super::{
    AL, BARRIERS, MSR_MASKS, bit, bits, cm, core_list, reg, sext, shift_by_reg, shifted,
    so_imm_ops, vfp, wb_reg,
};

const DP: [&[&str; 16]; 16] = [
    conds!("and"),
    conds!("eor"),
    conds!("sub"),
    conds!("rsb"),
    conds!("add"),
    conds!("adc"),
    conds!("sbc"),
    conds!("rsc"),
    conds!("tst"),
    conds!("teq"),
    conds!("cmp"),
    conds!("cmn"),
    conds!("orr"),
    conds!("mov"),
    conds!("bic"),
    conds!("mvn"),
];

const DP_S: [&[&str; 16]; 16] = [
    conds!("ands"),
    conds!("eors"),
    conds!("subs"),
    conds!("rsbs"),
    conds!("adds"),
    conds!("adcs"),
    conds!("sbcs"),
    conds!("rscs"),
    conds!("tst"),
    conds!("teq"),
    conds!("cmp"),
    conds!("cmn"),
    conds!("orrs"),
    conds!("movs"),
    conds!("bics"),
    conds!("mvns"),
];

const SHIFTS: [&[&str; 16]; 4] = [conds!("lsl"), conds!("lsr"), conds!("asr"), conds!("ror")];
const SHIFTS_S: [&[&str; 16]; 4] = [
    conds!("lsls"),
    conds!("lsrs"),
    conds!("asrs"),
    conds!("rors"),
];

/// Decode one A32 word.
pub fn decode(w: u32, addr: Addr) -> Option<Insn> {
    let cond = bits(w, 31, 28);
    if cond == 15 {
        return unconditional(w, addr);
    }
    match bits(w, 27, 25) {
        0b000 => dp_misc(w, cond, addr),
        0b001 => dp_imm(w, cond, addr),
        0b010 => ldst(w, cond, addr, false),
        0b011 if bit(w, 4) == 0 => ldst(w, cond, addr, true),
        0b011 => media(w, cond, addr),
        0b100 => block(w, cond, addr),
        0b101 => branch(w, cond, addr),
        0b110 => vfp::ldst(w, cond, addr, 4),
        _ => vfp::dp(w, cond, addr, 4),
    }
}

fn at(addr: Addr, mn: &'static str, flow: Flow) -> Insn {
    Insn::new(addr, 4, mn, flow)
}

/// Table A5-2: the register data-processing space shares bits 27:25 with the
/// multiplies, the halfword loads and stores, and the branch-and-exchange
/// corner, and only bits 7:4 tell them apart.
fn dp_misc(w: u32, cond: u32, addr: Addr) -> Option<Insn> {
    let control = bits(w, 24, 20) & 0b11001 == 0b10000;
    if bit(w, 4) == 0 {
        return if control {
            if bit(w, 7) == 0 {
                misc(w, cond, addr)
            } else {
                None // halfword multiply and accumulate
            }
        } else {
            dp_reg(w, cond, addr, None)
        };
    }
    if bit(w, 7) == 0 {
        return if control {
            misc(w, cond, addr)
        } else {
            dp_reg(w, cond, addr, Some(bits(w, 11, 8)))
        };
    }
    match bits(w, 7, 4) {
        0b1001 if bit(w, 24) == 0 => multiply(w, cond, addr),
        0b1001 => sync(w, cond, addr),
        _ => extra_ldst(w, cond, addr),
    }
}

/// Data processing with a register source, optionally shifted by `by`.
fn dp_reg(w: u32, cond: u32, addr: Addr, by: Option<u32>) -> Option<Insn> {
    let op = bits(w, 24, 21) as usize;
    let s = bit(w, 20) == 1;
    let (rd, rn, rm) = (bits(w, 15, 12), bits(w, 19, 16), bits(w, 3, 0));
    let (ty, imm5) = (bits(w, 6, 5), bits(w, 11, 7));
    let table = if s { &DP_S } else { &DP };

    // A `mov` whose source is shifted is spelled as the shift.
    if op == 0b1101 {
        let flow = pc_write(rd, rm, by.is_none() && ty == 0 && imm5 == 0);
        let shift_mn = cm(
            if s {
                SHIFTS_S[ty as usize]
            } else {
                SHIFTS[ty as usize]
            },
            cond,
        );
        let mut i = match by {
            Some(_) => at(addr, shift_mn, flow),
            None if ty == 0 && imm5 == 0 => at(addr, cm(table[op], cond), flow),
            None if ty == 3 && imm5 == 0 => at(
                addr,
                cm(if s { conds!("rrxs") } else { conds!("rrx") }, cond),
                flow,
            ),
            None => at(addr, shift_mn, flow),
        };
        i.push(Operand::Reg(reg(rd))).push(Operand::Reg(reg(rm)));
        match by {
            Some(rs) => {
                i.push(Operand::Reg(reg(rs)));
            }
            None if ty == 0 && imm5 == 0 => {}
            None if ty == 3 && imm5 == 0 => {}
            None => {
                let (_, n) = super::decode_shift(ty, imm5);
                i.push(Operand::Count(n as i64));
            }
        }
        return Some(i);
    }

    let src = match by {
        Some(_) => Operand::Reg(reg(rm)),
        None => shifted(rm, ty, imm5),
    };
    let mut i = at(addr, cm(table[op], cond), pc_write(rd, rm, false));
    if (0b1000..=0b1011).contains(&op) {
        if !s {
            return None;
        }
        i.push(Operand::Reg(reg(rn)));
    } else if op == 0b1111 {
        i.push(Operand::Reg(reg(rd)));
    } else {
        i.push(Operand::Reg(reg(rd))).push(Operand::Reg(reg(rn)));
    }
    i.push(src);
    if let Some(rs) = by {
        i.push(Operand::Name(shift_by_reg(ty, rs)));
    }
    Some(i)
}

/// Writing the pc is a branch, and moving the link register back into it is a
/// return. A predicated one keeps the branch and loses the fall-through, which
/// is the closest [`Flow`] can come to a conditional indirect transfer.
fn pc_write(rd: u32, rm: u32, plain_mov: bool) -> Flow {
    match (rd, rm, plain_mov) {
        (15, 14, true) => Flow::Return,
        (15, _, _) => Flow::IndirectBranch,
        _ => Flow::Next,
    }
}

/// Table A5-3: `bx`, `clz`, `mrs`, `msr` and the saturating adds.
fn misc(w: u32, cond: u32, addr: Addr) -> Option<Insn> {
    let op = bits(w, 22, 21);
    let (rd, rm) = (bits(w, 15, 12), bits(w, 3, 0));
    match bits(w, 6, 4) {
        0b000 if bit(w, 9) == 0 && op & 1 == 0 => {
            let mut i = at(addr, cm(conds!("mrs"), cond), Flow::Next);
            i.push(Operand::Reg(reg(rd)))
                .push(Operand::Name(if bit(w, 22) == 1 { "spsr" } else { "apsr" }));
            Some(i)
        }
        0b000 if bit(w, 9) == 0 => {
            let mask = bit(w, 22) << 4 | bits(w, 19, 16);
            let mut i = at(addr, cm(conds!("msr"), cond), Flow::Next);
            i.push(Operand::Name(MSR_MASKS[mask as usize]))
                .push(Operand::Reg(reg(rm)));
            Some(i)
        }
        0b001 if op == 0b01 => {
            let flow = if rm == 14 {
                Flow::Return
            } else {
                Flow::IndirectBranch
            };
            let mut i = at(addr, cm(conds!("bx"), cond), flow);
            i.push(Operand::Reg(reg(rm)));
            Some(i)
        }
        0b001 if op == 0b11 => {
            let mut i = at(addr, cm(conds!("clz"), cond), Flow::Next);
            i.push(Operand::Reg(reg(rd))).push(Operand::Reg(reg(rm)));
            Some(i)
        }
        0b010 if op == 0b01 => {
            let mut i = at(addr, cm(conds!("bxj"), cond), Flow::IndirectBranch);
            i.push(Operand::Reg(reg(rm)));
            Some(i)
        }
        0b011 if op == 0b01 => {
            let mut i = at(addr, cm(conds!("blx"), cond), Flow::IndirectCall);
            i.push(Operand::Reg(reg(rm)));
            Some(i)
        }
        0b101 => {
            const SAT: [&[&str; 16]; 4] = [
                conds!("qadd"),
                conds!("qsub"),
                conds!("qdadd"),
                conds!("qdsub"),
            ];
            let mut i = at(addr, cm(SAT[op as usize], cond), Flow::Next);
            i.push(Operand::Reg(reg(rd)))
                .push(Operand::Reg(reg(rm)))
                .push(Operand::Reg(reg(bits(w, 19, 16))));
            Some(i)
        }
        0b111 if op == 0b01 => {
            let imm = bits(w, 19, 8) << 4 | bits(w, 3, 0);
            let mut i = at(addr, cm(conds!("bkpt"), cond), Flow::Trap);
            i.push(Operand::UImm(imm as u64));
            Some(i)
        }
        _ => None,
    }
}

/// Table A5-4, minus the halfword multiplies: `mul` through `smlal`.
fn multiply(w: u32, cond: u32, addr: Addr) -> Option<Insn> {
    let s = bit(w, 20) == 1;
    let (rd, ra, rm, rn) = (
        bits(w, 19, 16),
        bits(w, 15, 12),
        bits(w, 11, 8),
        bits(w, 3, 0),
    );
    let long = |t: &'static [&str; 16], ts: &'static [&str; 16]| {
        let mut i = at(addr, cm(if s { ts } else { t }, cond), Flow::Next);
        i.push(Operand::Reg(reg(ra)))
            .push(Operand::Reg(reg(rd)))
            .push(Operand::Reg(reg(rn)))
            .push(Operand::Reg(reg(rm)));
        i
    };
    Some(match bits(w, 23, 21) {
        0b000 => {
            let mut i = at(
                addr,
                cm(if s { conds!("muls") } else { conds!("mul") }, cond),
                Flow::Next,
            );
            i.push(Operand::Reg(reg(rd)))
                .push(Operand::Reg(reg(rn)))
                .push(Operand::Reg(reg(rm)));
            i
        }
        0b001 => {
            let mut i = at(
                addr,
                cm(if s { conds!("mlas") } else { conds!("mla") }, cond),
                Flow::Next,
            );
            i.push(Operand::Reg(reg(rd)))
                .push(Operand::Reg(reg(rn)))
                .push(Operand::Reg(reg(rm)))
                .push(Operand::Reg(reg(ra)));
            i
        }
        0b010 if !s => long(conds!("umaal"), conds!("umaal")),
        0b011 if !s => {
            let mut i = at(addr, cm(conds!("mls"), cond), Flow::Next);
            i.push(Operand::Reg(reg(rd)))
                .push(Operand::Reg(reg(rn)))
                .push(Operand::Reg(reg(rm)))
                .push(Operand::Reg(reg(ra)));
            i
        }
        0b100 => long(conds!("umull"), conds!("umulls")),
        0b101 => long(conds!("umlal"), conds!("umlals")),
        0b110 => long(conds!("smull"), conds!("smulls")),
        0b111 => long(conds!("smlal"), conds!("smlals")),
        _ => return None,
    })
}

/// The load-exclusive family; the rest of table A5-5 is left alone.
fn sync(w: u32, cond: u32, addr: Addr) -> Option<Insn> {
    let (rn, rd, rt) = (bits(w, 19, 16), bits(w, 15, 12), bits(w, 3, 0));
    let (mn, load, size) = match bits(w, 23, 20) {
        0b1000 => (cm(conds!("strex"), cond), false, 4),
        0b1001 => (cm(conds!("ldrex"), cond), true, 4),
        0b1100 => (cm(conds!("strexb"), cond), false, 1),
        0b1101 => (cm(conds!("ldrexb"), cond), true, 1),
        0b1110 => (cm(conds!("strexh"), cond), false, 2),
        0b1111 => (cm(conds!("ldrexh"), cond), true, 2),
        _ => return None,
    };
    let mem = Operand::Mem(Mem::base_disp(reg(rn), 0, size));
    let mut i = at(addr, mn, Flow::Next);
    if load {
        i.push(Operand::Reg(reg(rd))).push(mem);
    } else {
        i.push(Operand::Reg(reg(rd)))
            .push(Operand::Reg(reg(rt)))
            .push(mem);
    }
    Some(i)
}

/// Table A5-10: the halfword, signed-byte and doubleword accesses, whose
/// displacements are eight bits and print in decimal.
fn extra_ldst(w: u32, cond: u32, addr: Addr) -> Option<Insn> {
    let (p, u, imm, wb, l) = (
        bit(w, 24) == 1,
        bit(w, 23) == 1,
        bit(w, 22) == 1,
        bit(w, 21) == 1,
        bit(w, 20) == 1,
    );
    if !p && wb {
        return None; // the unprivileged forms
    }
    let (rn, rt) = (bits(w, 19, 16), bits(w, 15, 12));
    let (mn, size, pair) = match (bits(w, 6, 5), l) {
        (0b01, false) => (cm(conds!("strh"), cond), 2, false),
        (0b01, true) => (cm(conds!("ldrh"), cond), 2, false),
        (0b10, false) => (cm(conds!("ldrd"), cond), 8, true),
        (0b10, true) => (cm(conds!("ldrsb"), cond), 1, false),
        (0b11, false) => (cm(conds!("strd"), cond), 8, true),
        _ => (cm(conds!("ldrsh"), cond), 2, false),
    };
    if pair && rt & 1 == 1 {
        return None;
    }
    let mode = match (p, wb) {
        (false, _) => AddrMode::PostIndex,
        (true, true) => AddrMode::PreIndex,
        (true, false) => AddrMode::Offset,
    };
    let mut m = Mem {
        seg: None,
        base: Some(reg(rn)),
        index: None,
        disp: 0,
        mode,
        size,
    };
    if imm {
        let off = (bits(w, 11, 8) << 4 | bits(w, 3, 0)) as i64;
        m.disp = if u { off } else { -off };
        if !u && off == 0 {
            m = minus_zero(m);
        }
    } else {
        if !u {
            return None; // a subtracted index has nowhere to live in `Mem`
        }
        m.index = index(reg(bits(w, 3, 0)), 0);
    }
    let mut i = at(addr, mn, Flow::Next);
    i.push(Operand::Reg(reg(rt)));
    if pair {
        i.push(Operand::Reg(reg(rt + 1)));
    }
    i.push(Operand::Mem(decimal(m)));
    Some(i)
}

/// Table A5-6, plus `movw`, `movt` and the hints that share its slots.
fn dp_imm(w: u32, cond: u32, addr: Addr) -> Option<Insn> {
    let (rd, rn) = (bits(w, 15, 12), bits(w, 19, 16));
    match bits(w, 24, 20) {
        0b10000 | 0b10100 => {
            let imm = bits(w, 19, 16) << 12 | bits(w, 11, 0);
            let wide = bit(w, 22) == 1;
            let mut i = at(
                addr,
                cm(if wide { conds!("movt") } else { conds!("movw") }, cond),
                Flow::Next,
            );
            i.push(Operand::Reg(reg(rd)))
                .push(Operand::UImm(imm as u64));
            Some(i)
        }
        0b10010 if rn == 0 && rd == 0b1111 => {
            const HINTS: [&[&str; 16]; 5] = [
                conds!("nop"),
                conds!("yield"),
                conds!("wfe"),
                conds!("wfi"),
                conds!("sev"),
            ];
            let n = bits(w, 7, 0) as usize;
            (n < HINTS.len()).then(|| at(addr, cm(HINTS[n], cond), Flow::Next))
        }
        0b10010 | 0b10110 => {
            let mask = bit(w, 22) << 4 | rn;
            let mut i = at(addr, cm(conds!("msr"), cond), Flow::Next);
            let (v, rot) = so_imm_ops(bits(w, 11, 0), true);
            i.push(Operand::Name(MSR_MASKS[mask as usize])).push(v);
            if let Some(rot) = rot {
                i.push(rot);
            }
            Some(i)
        }
        _ => {
            let op = bits(w, 24, 21) as usize;
            let s = bit(w, 20) == 1;
            let table = if s { &DP_S } else { &DP };
            // A `mov` to the pc reads better as a bit pattern than as a
            // negative number, which is the one place LLVM prints it unsigned.
            let (value, rot) = so_imm_ops(bits(w, 11, 0), op == 0b1101 && rd == 15);
            let flow = if rd == 15 && !(0b1000..=0b1011).contains(&op) {
                Flow::IndirectBranch
            } else {
                Flow::Next
            };
            let mut i = at(addr, cm(table[op], cond), flow);
            match op {
                0b1000..=0b1011 => {
                    i.push(Operand::Reg(reg(rn)));
                }
                0b1101 | 0b1111 => {
                    i.push(Operand::Reg(reg(rd)));
                }
                _ => {
                    i.push(Operand::Reg(reg(rd))).push(Operand::Reg(reg(rn)));
                }
            }
            i.push(value);
            if let Some(rot) = rot {
                i.push(rot);
            }
            Some(i)
        }
    }
}

/// Tables A5-15 and A5-16: the word and byte accesses.
fn ldst(w: u32, cond: u32, addr: Addr, reg_form: bool) -> Option<Insn> {
    let (p, u, b, wb, l) = (
        bit(w, 24) == 1,
        bit(w, 23) == 1,
        bit(w, 22) == 1,
        bit(w, 21) == 1,
        bit(w, 20) == 1,
    );
    if !p && wb {
        return None; // ldrt and its relatives
    }
    let (rn, rt) = (bits(w, 19, 16), bits(w, 15, 12));
    let mode = match (p, wb) {
        (false, _) => AddrMode::PostIndex,
        (true, true) => AddrMode::PreIndex,
        (true, false) => AddrMode::Offset,
    };
    let mut m = Mem {
        seg: None,
        base: Some(reg(rn)),
        index: None,
        disp: 0,
        mode,
        size: if b { 1 } else { 4 },
    };
    if reg_form {
        if !u || bits(w, 6, 5) != 0 {
            return None; // a subtracted or non-`lsl` index has nowhere to live
        }
        m.index = index(reg(bits(w, 3, 0)), bits(w, 11, 7) as u8);
    } else {
        let off = bits(w, 11, 0) as i64;
        m.disp = if u { off } else { -off };
        if !u && off == 0 && mode != AddrMode::Offset {
            m = minus_zero(m);
        }
    }
    if mode == AddrMode::PostIndex {
        m = decimal(m);
    }
    let mn = match (l, b) {
        (true, false) => cm(conds!("ldr"), cond),
        (true, true) => cm(conds!("ldrb"), cond),
        (false, false) => cm(conds!("str"), cond),
        (false, true) => cm(conds!("strb"), cond),
    };
    let flow = if l && rt == 15 {
        Flow::IndirectBranch
    } else {
        Flow::Next
    };
    let mut i = at(addr, mn, flow);
    i.push(Operand::Reg(reg(rt))).push(Operand::Mem(m));
    Some(i)
}

/// Table A5-13: the extends, the bitfields, `rev`, the divides and `udf`.
fn media(w: u32, cond: u32, addr: Addr) -> Option<Insn> {
    let (op1, op2) = (bits(w, 24, 20), bits(w, 7, 5));
    let (rd, rn, rm) = (bits(w, 15, 12), bits(w, 19, 16), bits(w, 3, 0));
    match (op1, op2) {
        (0b11111, 0b111) => {
            let imm = bits(w, 19, 8) << 4 | rm;
            let mut i = at(addr, cm(conds!("udf"), cond), Flow::Trap);
            i.push(Operand::UImm(imm as u64));
            Some(i)
        }
        (0b11010 | 0b11011 | 0b11110 | 0b11111, 0b010 | 0b110) => {
            let signed = op1 < 0b11110;
            let mut i = at(
                addr,
                cm(
                    if signed {
                        conds!("sbfx")
                    } else {
                        conds!("ubfx")
                    },
                    cond,
                ),
                Flow::Next,
            );
            i.push(Operand::Reg(reg(rd)))
                .push(Operand::Reg(reg(rm)))
                .push(Operand::UImm(bits(w, 11, 7) as u64))
                .push(Operand::UImm(bits(w, 20, 16) as u64 + 1));
            Some(i)
        }
        (0b11100 | 0b11101, 0b000 | 0b100) => {
            let lsb = bits(w, 11, 7);
            let width = bits(w, 20, 16) as i64 - lsb as i64 + 1;
            if width < 1 {
                return None;
            }
            let mut i = at(
                addr,
                cm(
                    if rm == 15 {
                        conds!("bfc")
                    } else {
                        conds!("bfi")
                    },
                    cond,
                ),
                Flow::Next,
            );
            i.push(Operand::Reg(reg(rd)));
            if rm != 15 {
                i.push(Operand::Reg(reg(rm)));
            }
            i.push(Operand::Count(lsb as i64))
                .push(Operand::Count(width));
            Some(i)
        }
        (0b10001 | 0b10011, 0b000) => {
            let mut i = at(
                addr,
                cm(
                    if op1 == 0b10001 {
                        conds!("sdiv")
                    } else {
                        conds!("udiv")
                    },
                    cond,
                ),
                Flow::Next,
            );
            i.push(Operand::Reg(reg(rn)))
                .push(Operand::Reg(reg(rm)))
                .push(Operand::Reg(reg(bits(w, 11, 8))));
            Some(i)
        }
        (0b01011, 0b001) | (0b01011, 0b101) | (0b01111, 0b001) | (0b01111, 0b101)
            if rn == 15 && bits(w, 11, 8) == 15 =>
        {
            let mn = match (op1, op2) {
                (0b01011, 0b001) => conds!("rev"),
                (0b01011, 0b101) => conds!("rev16"),
                (0b01111, 0b001) => conds!("rbit"),
                _ => conds!("revsh"),
            };
            let mut i = at(addr, cm(mn, cond), Flow::Next);
            i.push(Operand::Reg(reg(rd))).push(Operand::Reg(reg(rm)));
            Some(i)
        }
        (0b01000 | 0b01010 | 0b01011 | 0b01100 | 0b01110 | 0b01111, 0b011)
            if bits(w, 9, 8) == 0 =>
        {
            let plain = rn == 15;
            let mn = match (op1, plain) {
                (0b01000, true) => conds!("sxtb16"),
                (0b01000, false) => conds!("sxtab16"),
                (0b01010, true) => conds!("sxtb"),
                (0b01010, false) => conds!("sxtab"),
                (0b01011, true) => conds!("sxth"),
                (0b01011, false) => conds!("sxtah"),
                (0b01100, true) => conds!("uxtb16"),
                (0b01100, false) => conds!("uxtab16"),
                (0b01110, true) => conds!("uxtb"),
                (0b01110, false) => conds!("uxtab"),
                (0b01111, true) => conds!("uxth"),
                _ => conds!("uxtah"),
            };
            let mut i = at(addr, cm(mn, cond), Flow::Next);
            i.push(Operand::Reg(reg(rd)));
            if !plain {
                i.push(Operand::Reg(reg(rn)));
            }
            i.push(Operand::Reg(reg(rm)));
            let rotate = bits(w, 11, 10);
            if rotate != 0 {
                i.push(Operand::Name(ROTATES[rotate as usize]));
            }
            Some(i)
        }
        _ => None,
    }
}

/// The four rotate amounts an extend can apply, which print after its source.
const ROTATES: [&str; 4] = ["ror #0", "ror #8", "ror #16", "ror #24"];

/// Table A5-21: load and store multiple, and the `push` and `pop` spellings
/// LLVM prefers for the two that use the stack pointer.
fn block(w: u32, cond: u32, addr: Addr) -> Option<Insn> {
    if bit(w, 22) == 1 {
        return None; // the exception-return forms
    }
    let (p, u, wb, l) = (bit(w, 24), bit(w, 23), bit(w, 21) == 1, bit(w, 20) == 1);
    let rn = bits(w, 19, 16);
    let list = bits(w, 15, 0);
    if list == 0 {
        return None;
    }
    let stack = rn == 13 && wb && list.count_ones() >= 2;
    let flow = if l && list >> 15 == 1 {
        if rn == 13 {
            Flow::Return
        } else {
            Flow::IndirectBranch
        }
    } else {
        Flow::Next
    };
    const LDM: [&[&str; 16]; 4] = [
        conds!("ldmda"),
        conds!("ldm"),
        conds!("ldmdb"),
        conds!("ldmib"),
    ];
    const STM: [&[&str; 16]; 4] = [
        conds!("stmda"),
        conds!("stm"),
        conds!("stmdb"),
        conds!("stmib"),
    ];
    let kind = (p << 1 | u) as usize;
    let mut i = match (l, kind, stack) {
        (true, 0b01, true) => at(addr, cm(conds!("pop"), cond), flow),
        (false, 0b10, true) => at(addr, cm(conds!("push"), cond), flow),
        (true, _, _) => at(addr, cm(LDM[kind], cond), flow),
        (false, _, _) => at(addr, cm(STM[kind], cond), flow),
    };
    if !stack || !matches!((l, kind), (true, 0b01) | (false, 0b10)) {
        if wb {
            i.push(Operand::Name(wb_reg(rn)));
        } else {
            i.push(Operand::Reg(reg(rn)));
        }
    }
    i.push(core_list(list));
    Some(i)
}

fn branch(w: u32, cond: u32, addr: Addr) -> Option<Insn> {
    let target = super::target(addr, 8 + sext(bits(w, 23, 0), 24) * 4);
    let (mn, flow) = if bit(w, 24) == 1 {
        (cm(conds!("bl"), cond), Flow::Call(target))
    } else if cond == AL {
        (cm(conds!("b"), cond), Flow::Branch(target))
    } else {
        (cm(conds!("b"), cond), Flow::CondBranch(target))
    };
    let mut i = at(addr, mn, flow);
    i.push(Operand::Addr(target));
    Some(i)
}

/// Condition 15 is a second instruction space: the barriers, `pld`, and the
/// `blx` that changes instruction set.
fn unconditional(w: u32, addr: Addr) -> Option<Insn> {
    if bits(w, 27, 25) == 0b101 {
        let off = sext(bits(w, 23, 0), 24) * 4 + (bit(w, 24) as i64) * 2;
        let target = super::target(addr, 8 + off);
        let mut i = at(addr, "blx", Flow::Call(target));
        i.push(Operand::Addr(target));
        return Some(i);
    }
    if bits(w, 27, 4) == 0x57ff0 {
        let option = Operand::Name(BARRIERS[bits(w, 3, 0) as usize]);
        let mn = match bits(w, 7, 4) {
            0b0100 => "dsb",
            0b0101 => "dmb",
            0b0110 => "isb",
            0b0001 => return Some(at(addr, "clrex", Flow::Next)),
            _ => return None,
        };
        let mut i = at(addr, mn, Flow::Next);
        i.push(option);
        return Some(i);
    }
    if bits(w, 27, 26) == 0b01 && bit(w, 24) == 1 && bits(w, 15, 12) == 0b1111 && bit(w, 4) == 0 {
        // pld and pli, whose only operand is the address they touch.
        let mn = match (bit(w, 22), bit(w, 25)) {
            (0, 0) => "pld",
            (1, 0) => "pldw",
            _ => return None,
        };
        let off = bits(w, 11, 0) as i64;
        let m = Mem::base_disp(
            reg(bits(w, 19, 16)),
            if bit(w, 23) == 1 { off } else { -off },
            1,
        );
        let mut i = at(addr, mn, Flow::Next);
        i.push(Operand::Mem(m));
        return Some(i);
    }
    None
}
