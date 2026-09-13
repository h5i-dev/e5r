//! T32 decode, and the IT state it cannot be done without.
//!
//! Sixteen-bit encodings come first; a halfword whose top five bits are
//! `11101`, `11110` or `11111` starts a thirty-two-bit one instead. The `.w`
//! suffix on the wide spellings is not decoration: LLVM prints it exactly
//! where a narrow encoding of the same operation exists, so it is part of the
//! mnemonic table and not something the formatter can add.

use r12e_core::Addr;

use crate::insn::{AddrMode, Cond, Flow, Insn, Mem, Operand};

use super::text::{always, decimal, index, minus_zero};
use super::{AL, bit, bits, cm, core_list, reg, sext, shifted, t2_imm, vfp, wb_reg};

/// The eight ITSTATE bits: the block's condition in 7:4, what remains of its
/// mask in 3:0. All-zero low bits mean no block is in progress.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct ItState(pub u8);

impl ItState {
    /// True while instructions are still being predicated by a block.
    pub fn in_block(self) -> bool {
        self.0 & 0xf != 0
    }

    /// The condition the next instruction runs under, if any.
    pub fn cond(self) -> Option<Cond> {
        self.in_block().then_some(Cond(self.0 >> 4))
    }

    /// The state one instruction later.
    pub fn advance(self) -> ItState {
        if !self.in_block() || self.0 & 7 == 0 {
            return ItState(0);
        }
        ItState((self.0 & 0xe0) | ((self.0 << 1) & 0x1f))
    }

    fn start(firstcond: u32, mask: u32) -> ItState {
        ItState((firstcond << 4 | mask) as u8)
    }

    fn value(self) -> u32 {
        self.cond().map_or(AL, |c| c.0 as u32)
    }
}

/// Decode one T32 instruction, and report the state the next one runs under.
pub fn decode(bytes: &[u8], addr: Addr, it: ItState) -> Option<(Insn, ItState)> {
    let hw1 = u16::from_le_bytes(bytes.get(..2)?.try_into().ok()?) as u32;
    let cond = it.value();
    if hw1 >> 11 >= 0b11101 {
        let hw2 = u16::from_le_bytes(bytes.get(2..4)?.try_into().ok()?) as u32;
        let i = wide(hw1 << 16 | hw2, cond, it.in_block(), addr)?;
        return Some((i, it.advance()));
    }
    let i = narrow(hw1, cond, it.in_block(), addr)?;
    // An `it` replaces the state rather than advancing it.
    let next = if hw1 & 0xff00 == 0xbf00 && hw1 & 0xf != 0 {
        ItState::start(it_cond(bits(hw1, 7, 4)), bits(hw1, 3, 0))
    } else {
        it.advance()
    };
    Some((i, next))
}

fn at(addr: Addr, len: u8, mn: &'static str, flow: Flow) -> Insn {
    Insn::new(addr, len, mn, flow)
}

fn branch_flow(cond: u32, target: Addr) -> Flow {
    if cond == AL {
        Flow::Branch(target)
    } else {
        Flow::CondBranch(target)
    }
}

/// A sixteen-bit encoding that sets the flags outside an IT block and does not
/// set them inside one, which is the whole difference between `adds` and
/// `addlo` in a listing.
fn flagged(
    in_it: bool,
    cond: u32,
    plain: &'static [&str; 16],
    setting: &'static str,
) -> &'static str {
    if in_it { cm(plain, cond) } else { setting }
}

const NARROW_DP: [&[&str; 16]; 16] = [
    conds!("and"),
    conds!("eor"),
    conds!("lsl"),
    conds!("lsr"),
    conds!("asr"),
    conds!("adc"),
    conds!("sbc"),
    conds!("ror"),
    conds!("tst"),
    conds!("rsb"),
    conds!("cmp"),
    conds!("cmn"),
    conds!("orr"),
    conds!("mul"),
    conds!("bic"),
    conds!("mvn"),
];

const NARROW_DP_S: [&str; 16] = [
    "ands", "eors", "lsls", "lsrs", "asrs", "adcs", "sbcs", "rors", "tst", "rsbs", "cmp", "cmn",
    "orrs", "muls", "bics", "mvns",
];

const NARROW_SHIFT: [&[&str; 16]; 3] = [conds!("lsl"), conds!("lsr"), conds!("asr")];
const NARROW_SHIFT_S: [&str; 3] = ["lsls", "lsrs", "asrs"];

/// The sixteen-bit encodings, table A6-1.
fn narrow(hw: u32, cond: u32, in_it: bool, addr: Addr) -> Option<Insn> {
    let rd = bits(hw, 2, 0);
    let rn = bits(hw, 5, 3);
    match bits(hw, 15, 10) {
        0b000000..=0b001111 => shift_add_sub(hw, cond, in_it, addr),
        0b010000 => {
            let op = bits(hw, 9, 6) as usize;
            let mn = flagged(in_it, cond, NARROW_DP[op], NARROW_DP_S[op]);
            let mut i = at(addr, 2, mn, Flow::Next);
            match op {
                0b1001 => {
                    i.push(Operand::Reg(reg(rd)))
                        .push(Operand::Reg(reg(rn)))
                        .push(Operand::Count(0));
                }
                0b1101 => {
                    i.push(Operand::Reg(reg(rd)))
                        .push(Operand::Reg(reg(rn)))
                        .push(Operand::Reg(reg(rd)));
                }
                _ => {
                    i.push(Operand::Reg(reg(rd))).push(Operand::Reg(reg(rn)));
                }
            }
            Some(i)
        }
        0b010001 => special(hw, cond, addr),
        0b010010 | 0b010011 => {
            let m = always(Mem::base_disp(reg(15), bits(hw, 7, 0) as i64 * 4, 4));
            let mut i = at(addr, 2, cm(conds!("ldr"), cond), Flow::Next);
            i.push(Operand::Reg(reg(bits(hw, 10, 8))))
                .push(Operand::Mem(m));
            Some(i)
        }
        0b010100..=0b010111 => {
            const OPS: [(&[&str; 16], u64); 8] = [
                (conds!("str"), 4),
                (conds!("strh"), 2),
                (conds!("strb"), 1),
                (conds!("ldrsb"), 1),
                (conds!("ldr"), 4),
                (conds!("ldrh"), 2),
                (conds!("ldrb"), 1),
                (conds!("ldrsh"), 2),
            ];
            let (mn, size) = OPS[bits(hw, 11, 9) as usize];
            let mut m = Mem::base_disp(reg(rn), 0, size);
            m.index = index(reg(bits(hw, 8, 6)), 0);
            let mut i = at(addr, 2, cm(mn, cond), Flow::Next);
            i.push(Operand::Reg(reg(rd))).push(Operand::Mem(m));
            Some(i)
        }
        0b011000..=0b100111 => ldst_imm5(hw, cond, addr),
        0b101000 | 0b101001 => {
            let mut i = at(addr, 2, cm(conds!("adr"), cond), Flow::Next);
            i.push(Operand::Reg(reg(bits(hw, 10, 8))))
                .push(Operand::Count(bits(hw, 7, 0) as i64 * 4));
            Some(i)
        }
        0b101010 | 0b101011 => {
            let mut i = at(addr, 2, cm(conds!("add"), cond), Flow::Next);
            i.push(Operand::Reg(reg(bits(hw, 10, 8))))
                .push(Operand::Reg(reg(13)))
                .push(Operand::UImm(bits(hw, 7, 0) as u64 * 4));
            Some(i)
        }
        0b101100..=0b101111 => misc(hw, cond, addr),
        0b110000..=0b110011 => {
            let rn = bits(hw, 10, 8);
            let list = bits(hw, 7, 0);
            if list == 0 {
                return None;
            }
            let load = bit(hw, 11) == 1;
            let wb = !load || list >> rn & 1 == 0;
            let mut i = at(
                addr,
                2,
                cm(if load { conds!("ldm") } else { conds!("stm") }, cond),
                Flow::Next,
            );
            if wb {
                i.push(Operand::Name(wb_reg(rn)));
            } else {
                i.push(Operand::Reg(reg(rn)));
            }
            i.push(core_list(list));
            Some(i)
        }
        0b110100..=0b110111 => {
            let c = bits(hw, 11, 8);
            let imm = bits(hw, 7, 0);
            match c {
                0b1110 => Some(match imm {
                    // Two of the two hundred and fifty six are the EABI's.
                    0xfe => at(addr, 2, "trap", Flow::Trap),
                    0xf9 => at(addr, 2, "__brkdiv0", Flow::Trap),
                    _ => {
                        let mut i = at(addr, 2, "udf", Flow::Trap);
                        i.push(Operand::UImm(imm as u64));
                        i
                    }
                }),
                0b1111 => {
                    let mut i = at(addr, 2, cm(conds!("svc"), cond), Flow::Syscall);
                    i.push(Operand::UImm(imm as u64));
                    Some(i)
                }
                _ => {
                    let target = super::target(addr, 4 + sext(imm, 8) * 2);
                    let c = if in_it { cond } else { c };
                    let mut i = at(addr, 2, cm(conds!("b"), c), Flow::CondBranch(target));
                    i.push(Operand::Addr(target));
                    Some(i)
                }
            }
        }
        0b111000 | 0b111001 => {
            let target = super::target(addr, 4 + sext(bits(hw, 10, 0), 11) * 2);
            let mut i = at(addr, 2, cm(conds!("b"), cond), branch_flow(cond, target));
            i.push(Operand::Addr(target));
            Some(i)
        }
        _ => None,
    }
}

/// Table A6-2: the shifts, adds, subtracts, moves and compares that make up a
/// quarter of the sixteen-bit space.
fn shift_add_sub(hw: u32, cond: u32, in_it: bool, addr: Addr) -> Option<Insn> {
    let (rd, rn) = (bits(hw, 2, 0), bits(hw, 5, 3));
    match bits(hw, 13, 11) {
        0b011 => {
            let sub = bit(hw, 9) == 1;
            let imm = bit(hw, 10) == 1;
            let mn = if sub {
                flagged(in_it, cond, conds!("sub"), "subs")
            } else {
                flagged(in_it, cond, conds!("add"), "adds")
            };
            let mut i = at(addr, 2, mn, Flow::Next);
            i.push(Operand::Reg(reg(rd))).push(Operand::Reg(reg(rn)));
            if imm {
                i.push(Operand::UImm(bits(hw, 8, 6) as u64));
            } else {
                i.push(Operand::Reg(reg(bits(hw, 8, 6))));
            }
            Some(i)
        }
        op @ 0b000..=0b010 => {
            let imm5 = bits(hw, 10, 6);
            // `lsl` by nothing is how a register move is encoded, and it is
            // the one sixteen-bit form that keeps setting the flags inside an
            // IT block rather than taking the block's condition.
            if op == 0 && imm5 == 0 {
                let mut i = at(addr, 2, "movs", Flow::Next);
                i.push(Operand::Reg(reg(rd))).push(Operand::Reg(reg(rn)));
                return Some(i);
            }
            let mn = flagged(
                in_it,
                cond,
                NARROW_SHIFT[op as usize],
                NARROW_SHIFT_S[op as usize],
            );
            let amount = if op != 0 && imm5 == 0 { 32 } else { imm5 };
            let mut i = at(addr, 2, mn, Flow::Next);
            i.push(Operand::Reg(reg(rd)))
                .push(Operand::Reg(reg(rn)))
                .push(Operand::UImm(amount as u64));
            Some(i)
        }
        op => {
            let rdn = bits(hw, 10, 8);
            let imm = Operand::UImm(bits(hw, 7, 0) as u64);
            let mn = match op {
                0b100 => flagged(in_it, cond, conds!("mov"), "movs"),
                0b101 => cm(conds!("cmp"), cond),
                0b110 => flagged(in_it, cond, conds!("add"), "adds"),
                _ => flagged(in_it, cond, conds!("sub"), "subs"),
            };
            let mut i = at(addr, 2, mn, Flow::Next);
            i.push(Operand::Reg(reg(rdn))).push(imm);
            Some(i)
        }
    }
}

/// Table A6-3: the forms that reach the high registers, and `bx`.
fn special(hw: u32, cond: u32, addr: Addr) -> Option<Insn> {
    let rm = bits(hw, 6, 3);
    let rdn = bit(hw, 7) << 3 | bits(hw, 2, 0);
    match bits(hw, 9, 8) {
        0b11 => {
            let call = bit(hw, 7) == 1;
            let flow = match (call, rm) {
                (true, _) => Flow::IndirectCall,
                (false, 14) => Flow::Return,
                (false, _) => Flow::IndirectBranch,
            };
            let mut i = at(
                addr,
                2,
                cm(if call { conds!("blx") } else { conds!("bx") }, cond),
                flow,
            );
            i.push(Operand::Reg(reg(rm)));
            Some(i)
        }
        op => {
            if op == 0b00 && (rm == 13 || rdn == 13) {
                let mut i = at(addr, 2, cm(conds!("add"), cond), Flow::Next);
                // The stack pointer always prints as the second operand, so
                // adding to it and adding it read differently.
                if rm == 13 {
                    i.push(Operand::Reg(reg(rdn)))
                        .push(Operand::Reg(reg(13)))
                        .push(Operand::Reg(reg(rdn)));
                } else {
                    i.push(Operand::Reg(reg(13))).push(Operand::Reg(reg(rm)));
                }
                return Some(i);
            }
            let (mn, flow) = match op {
                0b00 => (
                    cm(conds!("add"), cond),
                    if rdn == 15 {
                        Flow::IndirectBranch
                    } else {
                        Flow::Next
                    },
                ),
                0b01 => (cm(conds!("cmp"), cond), Flow::Next),
                _ => (
                    cm(conds!("mov"), cond),
                    match (rdn, rm) {
                        (15, 14) => Flow::Return,
                        (15, _) => Flow::IndirectBranch,
                        _ => Flow::Next,
                    },
                ),
            };
            let mut i = at(addr, 2, mn, flow);
            i.push(Operand::Reg(reg(rdn))).push(Operand::Reg(reg(rm)));
            Some(i)
        }
    }
}

/// The immediate-offset loads and stores, whose scale follows their width.
fn ldst_imm5(hw: u32, cond: u32, addr: Addr) -> Option<Insn> {
    let load = bit(hw, 11) == 1;
    let (rt, rn, imm5) = (bits(hw, 2, 0), bits(hw, 5, 3), bits(hw, 10, 6));
    let (mn, size, base, off) = match bits(hw, 15, 12) {
        0b0110 => (
            if load { conds!("ldr") } else { conds!("str") },
            4,
            rn,
            imm5 * 4,
        ),
        0b0111 => (
            if load { conds!("ldrb") } else { conds!("strb") },
            1,
            rn,
            imm5,
        ),
        0b1000 => (
            if load { conds!("ldrh") } else { conds!("strh") },
            2,
            rn,
            imm5 * 2,
        ),
        _ => (
            if load { conds!("ldr") } else { conds!("str") },
            4,
            13,
            bits(hw, 7, 0) * 4,
        ),
    };
    let rt = if bits(hw, 15, 12) == 0b1001 {
        bits(hw, 10, 8)
    } else {
        rt
    };
    let mut i = at(addr, 2, cm(mn, cond), Flow::Next);
    i.push(Operand::Reg(reg(rt)))
        .push(Operand::Mem(Mem::base_disp(reg(base), off as i64, size)));
    Some(i)
}

/// Table A6-4: the sixteen-bit odds and ends, `push` and `pop` among them.
fn misc(hw: u32, cond: u32, addr: Addr) -> Option<Insn> {
    let (rd, rm) = (bits(hw, 2, 0), bits(hw, 5, 3));
    match bits(hw, 11, 8) {
        0b0000 => {
            let sub = bit(hw, 7) == 1;
            let mut i = at(
                addr,
                2,
                cm(if sub { conds!("sub") } else { conds!("add") }, cond),
                Flow::Next,
            );
            i.push(Operand::Reg(reg(13)))
                .push(Operand::UImm(bits(hw, 6, 0) as u64 * 4));
            Some(i)
        }
        0b0001 | 0b0011 | 0b1001 | 0b1011 => {
            let off = bit(hw, 9) << 6 | bits(hw, 7, 3) << 1;
            let target = super::target(addr, 4 + off as i64);
            let mut i = at(
                addr,
                2,
                if bit(hw, 11) == 1 { "cbnz" } else { "cbz" },
                Flow::CondBranch(target),
            );
            i.push(Operand::Reg(reg(rd))).push(Operand::Addr(target));
            Some(i)
        }
        0b0010 => {
            const OPS: [&[&str; 16]; 4] = [
                conds!("sxth"),
                conds!("sxtb"),
                conds!("uxth"),
                conds!("uxtb"),
            ];
            let mut i = at(addr, 2, cm(OPS[bits(hw, 7, 6) as usize], cond), Flow::Next);
            i.push(Operand::Reg(reg(rd))).push(Operand::Reg(reg(rm)));
            Some(i)
        }
        0b0100 | 0b0101 | 0b1100 | 0b1101 => {
            let pop = bit(hw, 11) == 1;
            let extra = bit(hw, 8) << if pop { 15 } else { 14 };
            let list = bits(hw, 7, 0) | extra;
            if list == 0 {
                return None;
            }
            let flow = if pop && list >> 15 == 1 {
                Flow::Return
            } else {
                Flow::Next
            };
            let mut i = at(
                addr,
                2,
                cm(if pop { conds!("pop") } else { conds!("push") }, cond),
                flow,
            );
            i.push(core_list(list));
            Some(i)
        }
        0b1010 => {
            let mn = match bits(hw, 7, 6) {
                0b00 => conds!("rev"),
                0b01 => conds!("rev16"),
                0b11 => conds!("revsh"),
                _ => return None,
            };
            let mut i = at(addr, 2, cm(mn, cond), Flow::Next);
            i.push(Operand::Reg(reg(rd))).push(Operand::Reg(reg(rm)));
            Some(i)
        }
        0b1110 => {
            let mut i = at(addr, 2, "bkpt", Flow::Trap);
            i.push(Operand::UImm(bits(hw, 7, 0) as u64));
            Some(i)
        }
        0b1111 => {
            let mask = bits(hw, 3, 0);
            let first = bits(hw, 7, 4);
            if mask != 0 {
                // An unpredictable first condition is read as `al`, but the
                // block still predicates with the encoded value.
                let named = it_cond(first);
                let mut i = at(addr, 2, it_name(named, mask), Flow::Next);
                i.push(Operand::Cond(Cond(named as u8)));
                return Some(i);
            }
            const HINTS: [&[&str; 16]; 5] = [
                conds!("nop"),
                conds!("yield"),
                conds!("wfe"),
                conds!("wfi"),
                conds!("sev"),
            ];
            (first < 5).then(|| at(addr, 2, cm(HINTS[first as usize], cond), Flow::Next))
        }
        _ => None,
    }
}

/// An unpredictable first condition is read as `al`, which then makes every
/// `e` instruction in the block carry the condition that has no name.
fn it_cond(first: u32) -> u32 {
    if first == 15 { AL } else { first }
}

/// The spelling of an `it`: one letter per instruction after the first, `t`
/// where it takes the block condition and `e` where it takes the inverse.
fn it_name(first: u32, mask: u32) -> &'static str {
    const NAMES: [&str; 15] = [
        "it", "ite", "itt", "itee", "itet", "itte", "ittt", "iteee", "iteet", "itete", "itett",
        "ittee", "ittet", "ittte", "itttt",
    ];
    // The lowest set bit terminates the mask; everything above it is one
    // instruction, and each such bit is `t` when it matches the condition's
    // low bit.
    let len = 4 - mask.trailing_zeros();
    let mut key = 0usize;
    for n in 0..len.saturating_sub(1) {
        let b = mask >> (3 - n) & 1;
        key = key << 1 | ((b == first & 1) as usize);
    }
    NAMES[(1 << (len - 1)) - 1 + key]
}

/// The thirty-two-bit encodings, table A6-9.
fn wide(w: u32, cond: u32, in_it: bool, addr: Addr) -> Option<Insn> {
    let op2 = bits(w, 26, 20);
    match bits(w, 28, 27) {
        // The coprocessor space, which for VFP is the A32 word unchanged.
        0b01 if op2 & 0b1000000 != 0 => match bits(w, 27, 24) {
            0b1100 | 0b1101 => vfp::ldst(w, cond, addr, 4),
            0b1110 => vfp::dp(w, cond, addr, 4),
            _ => None,
        },
        0b01 if op2 & 0b1100100 == 0b0000000 => block(w, cond, addr),
        0b01 if op2 & 0b1100100 == 0b0000100 => dual(w, cond, addr),
        0b01 => dp_shifted(w, cond, addr),
        0b10 if bit(w, 15) == 1 => control(w, cond, in_it, addr),
        0b10 if op2 & 0b0100000 == 0 => dp_imm(w, cond, addr),
        0b10 => dp_plain_imm(w, cond, addr),
        _ => group11(w, cond, addr),
    }
}

const WIDE_DP: [&[&str; 16]; 16] = [
    conds!("and", ".w"),
    conds!("bic", ".w"),
    conds!("orr", ".w"),
    conds!("orn"),
    conds!("eor", ".w"),
    conds!("and", ".w"),
    conds!("and", ".w"),
    conds!("and", ".w"),
    conds!("add", ".w"),
    conds!("and", ".w"),
    conds!("adc", ".w"),
    conds!("sbc", ".w"),
    conds!("and", ".w"),
    conds!("sub", ".w"),
    // `rsb` is the one shifted-register form LLVM spells without `.w`.
    conds!("rsb"),
    conds!("and", ".w"),
];

/// Data processing with a shifted register, which always takes `.w` except for
/// `rsb` and `rrx`, matching LLVM's tables rather than any rule.
fn dp_shifted(w: u32, cond: u32, addr: Addr) -> Option<Insn> {
    let op = bits(w, 24, 21) as usize;
    let s = bit(w, 20) == 1;
    let (rn, rd, rm) = (bits(w, 19, 16), bits(w, 11, 8), bits(w, 3, 0));
    let imm5 = bits(w, 14, 12) << 2 | bits(w, 7, 6);
    let ty = bits(w, 5, 4);
    let test = matches!(op, 0b0000 | 0b0100 | 0b1000 | 0b1101) && s && rd == 15;

    if op == 0b0010 && rn == 15 {
        return move_shifted(cond, addr, s, rd, rm, ty, imm5);
    }
    if op == 0b0011 && rn == 15 {
        let mut i = at(
            addr,
            4,
            cm(
                if s {
                    conds!("mvns", ".w")
                } else {
                    conds!("mvn", ".w")
                },
                cond,
            ),
            Flow::Next,
        );
        i.push(Operand::Reg(reg(rd))).push(shifted(rm, ty, imm5));
        return Some(i);
    }
    let mn = if test {
        match op {
            0b0000 => cm(conds!("tst", ".w"), cond),
            0b0100 => cm(conds!("teq", ".w"), cond),
            0b1000 => cm(conds!("cmn", ".w"), cond),
            _ => cm(conds!("cmp", ".w"), cond),
        }
    } else {
        wide_dp_name(op, s, cond)?
    };
    let mut i = at(addr, 4, mn, Flow::Next);
    if test {
        i.push(Operand::Reg(reg(rn)));
    } else {
        i.push(Operand::Reg(reg(rd))).push(Operand::Reg(reg(rn)));
    }
    i.push(shifted(rm, ty, imm5));
    Some(i)
}

/// The shifted-register and modified-immediate groups share an opcode field,
/// and the `s` forms need their own spellings.
fn wide_dp_name(op: usize, s: bool, cond: u32) -> Option<&'static str> {
    const S_FORMS: [&[&str; 16]; 16] = [
        conds!("ands", ".w"),
        conds!("bics", ".w"),
        conds!("orrs", ".w"),
        conds!("orns"),
        conds!("eors", ".w"),
        conds!("ands", ".w"),
        conds!("ands", ".w"),
        conds!("ands", ".w"),
        conds!("adds", ".w"),
        conds!("ands", ".w"),
        conds!("adcs", ".w"),
        conds!("sbcs", ".w"),
        conds!("ands", ".w"),
        conds!("subs", ".w"),
        conds!("rsbs"),
        conds!("ands", ".w"),
    ];
    // `pkh` shares the opcode field but not the operand shape.
    if matches!(op, 0b0101 | 0b0110 | 0b0111 | 0b1001 | 0b1100 | 0b1111) {
        return None;
    }
    Some(cm(if s { S_FORMS[op] } else { WIDE_DP[op] }, cond))
}

/// `mov` with a shift is spelled as the shift, and its amount prints in hex
/// where the same amount inside a shifted operand prints in decimal.
fn move_shifted(
    cond: u32,
    addr: Addr,
    s: bool,
    rd: u32,
    rm: u32,
    ty: u32,
    imm5: u32,
) -> Option<Insn> {
    let plain: [&[&str; 16]; 4] = [
        conds!("lsl", ".w"),
        conds!("lsr", ".w"),
        conds!("asr", ".w"),
        conds!("ror", ".w"),
    ];
    let setting: [&[&str; 16]; 4] = [
        conds!("lsls", ".w"),
        conds!("lsrs", ".w"),
        conds!("asrs", ".w"),
        conds!("rors", ".w"),
    ];
    let mut i = if ty == 0 && imm5 == 0 {
        at(
            addr,
            4,
            cm(
                if s {
                    conds!("movs", ".w")
                } else {
                    conds!("mov", ".w")
                },
                cond,
            ),
            Flow::Next,
        )
    } else if ty == 3 && imm5 == 0 {
        at(
            addr,
            4,
            cm(if s { conds!("rrxs") } else { conds!("rrx") }, cond),
            Flow::Next,
        )
    } else {
        at(
            addr,
            4,
            cm(
                if s {
                    setting[ty as usize]
                } else {
                    plain[ty as usize]
                },
                cond,
            ),
            Flow::Next,
        )
    };
    i.push(Operand::Reg(reg(rd))).push(Operand::Reg(reg(rm)));
    if !(imm5 == 0 && (ty == 0 || ty == 3)) {
        let (_, n) = super::decode_shift(ty, imm5);
        i.push(Operand::UImm(n as u64));
    }
    Some(i)
}

/// Data processing with a modified immediate. Only the arithmetic and the
/// moves take `.w` here; the logical forms do not.
fn dp_imm(w: u32, cond: u32, addr: Addr) -> Option<Insn> {
    const PLAIN: [&[&str; 16]; 16] = [
        conds!("and"),
        conds!("bic"),
        conds!("orr"),
        conds!("orn"),
        conds!("eor"),
        conds!("and"),
        conds!("and"),
        conds!("and"),
        conds!("add", ".w"),
        conds!("and"),
        conds!("adc"),
        conds!("sbc"),
        conds!("and"),
        conds!("sub", ".w"),
        conds!("rsb", ".w"),
        conds!("and"),
    ];
    const S_FORMS: [&[&str; 16]; 16] = [
        conds!("ands"),
        conds!("bics"),
        conds!("orrs"),
        conds!("orns"),
        conds!("eors"),
        conds!("ands"),
        conds!("ands"),
        conds!("ands"),
        conds!("adds", ".w"),
        conds!("ands"),
        conds!("adcs"),
        conds!("sbcs"),
        conds!("ands"),
        conds!("subs", ".w"),
        conds!("rsbs", ".w"),
        conds!("ands"),
    ];
    let op = bits(w, 24, 21) as usize;
    if matches!(op, 0b0101 | 0b0110 | 0b0111 | 0b1001 | 0b1100 | 0b1111) {
        return None;
    }
    let s = bit(w, 20) == 1;
    let (rn, rd) = (bits(w, 19, 16), bits(w, 11, 8));
    let value = t2_imm(bit(w, 26) << 11 | bits(w, 14, 12) << 8 | bits(w, 7, 0));
    let imm = Operand::UImm(value as u64);
    let test = matches!(op, 0b0000 | 0b0100 | 0b1000 | 0b1101) && s && rd == 15;
    if test {
        let mn = match op {
            0b0000 => conds!("tst", ".w"),
            0b0100 => conds!("teq", ".w"),
            0b1000 => conds!("cmn", ".w"),
            _ => conds!("cmp", ".w"),
        };
        let mut i = at(addr, 4, cm(mn, cond), Flow::Next);
        i.push(Operand::Reg(reg(rn))).push(imm);
        return Some(i);
    }
    let mut i = if op == 0b0010 && rn == 15 {
        let mut i = at(
            addr,
            4,
            cm(
                if s {
                    conds!("movs", ".w")
                } else {
                    conds!("mov", ".w")
                },
                cond,
            ),
            Flow::Next,
        );
        i.push(Operand::Reg(reg(rd)));
        i
    } else if op == 0b0011 && rn == 15 {
        let mut i = at(
            addr,
            4,
            cm(if s { conds!("mvns") } else { conds!("mvn") }, cond),
            Flow::Next,
        );
        i.push(Operand::Reg(reg(rd)));
        i
    } else {
        let mut i = at(
            addr,
            4,
            cm(if s { S_FORMS[op] } else { PLAIN[op] }, cond),
            Flow::Next,
        );
        i.push(Operand::Reg(reg(rd))).push(Operand::Reg(reg(rn)));
        i
    };
    i.push(imm);
    Some(i)
}

/// The plain binary immediates: `movw`, `movt`, `addw`, the bitfields.
fn dp_plain_imm(w: u32, cond: u32, addr: Addr) -> Option<Insn> {
    let (rn, rd) = (bits(w, 19, 16), bits(w, 11, 8));
    let imm12 = bit(w, 26) << 11 | bits(w, 14, 12) << 8 | bits(w, 7, 0);
    let lsb = bits(w, 14, 12) << 2 | bits(w, 7, 6);
    match bits(w, 24, 20) {
        0b00000 | 0b01010 if rn == 15 => {
            let sub = bit(w, 23) == 1;
            let mut i = at(addr, 4, cm(conds!("adr", ".w"), cond), Flow::Next);
            let off = imm12 as i64;
            i.push(Operand::Reg(reg(rd)))
                .push(Operand::Count(if sub { -off } else { off }));
            Some(i)
        }
        op @ (0b00000 | 0b01010) => {
            let mut i = at(
                addr,
                4,
                cm(
                    if op == 0 {
                        conds!("addw")
                    } else {
                        conds!("subw")
                    },
                    cond,
                ),
                Flow::Next,
            );
            i.push(Operand::Reg(reg(rd)))
                .push(Operand::Reg(reg(rn)))
                .push(Operand::UImm(imm12 as u64));
            Some(i)
        }
        0b00100 | 0b01100 => {
            let imm16 = rn << 12 | imm12;
            let mut i = at(
                addr,
                4,
                cm(
                    if bit(w, 23) == 1 {
                        conds!("movt")
                    } else {
                        conds!("movw")
                    },
                    cond,
                ),
                Flow::Next,
            );
            i.push(Operand::Reg(reg(rd)))
                .push(Operand::UImm(imm16 as u64));
            Some(i)
        }
        0b10100 | 0b11100 => {
            let signed = bit(w, 23) == 0;
            let mut i = at(
                addr,
                4,
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
                .push(Operand::Reg(reg(rn)))
                .push(Operand::UImm(lsb as u64))
                .push(Operand::UImm(bits(w, 4, 0) as u64 + 1));
            Some(i)
        }
        0b10110 => {
            let width = bits(w, 4, 0) as i64 - lsb as i64 + 1;
            if width < 1 {
                return None;
            }
            let mut i = at(
                addr,
                4,
                cm(
                    if rn == 15 {
                        conds!("bfc")
                    } else {
                        conds!("bfi")
                    },
                    cond,
                ),
                Flow::Next,
            );
            i.push(Operand::Reg(reg(rd)));
            if rn != 15 {
                i.push(Operand::Reg(reg(rn)));
            }
            i.push(Operand::Count(lsb as i64))
                .push(Operand::Count(width));
            Some(i)
        }
        _ => None,
    }
}

/// Branches, and the control instructions that share their slot.
fn control(w: u32, cond: u32, in_it: bool, addr: Addr) -> Option<Insn> {
    let s = bit(w, 26);
    let (j1, j2) = (bit(w, 13), bit(w, 11));
    match (bit(w, 14), bit(w, 12)) {
        (0, 0) if bits(w, 26, 23) == 0b1111 => misc_control(w, cond, addr),
        (0, 0) => {
            let c = bits(w, 25, 22);
            if c >= 0b1110 {
                return None;
            }
            let off = sext(
                s << 20 | j2 << 19 | j1 << 18 | bits(w, 21, 16) << 12 | bits(w, 10, 0) << 1,
                21,
            );
            let target = super::target(addr, 4 + off);
            // Inside an IT block a conditional branch is unpredictable, and
            // the block's condition is the one that prints.
            let c = if in_it { cond } else { c };
            let mut i = at(addr, 4, cm(conds!("b", ".w"), c), Flow::CondBranch(target));
            i.push(Operand::Addr(target));
            Some(i)
        }
        (hi, lo) => {
            let i1 = 1 - (j1 ^ s);
            let i2 = 1 - (j2 ^ s);
            let off = sext(
                s << 24 | i1 << 23 | i2 << 22 | bits(w, 25, 16) << 12 | bits(w, 10, 0) << 1,
                25,
            );
            // `blx` changes instruction set, so its target is A32-aligned and
            // measured from a pc rounded down to a word.
            let exchange = hi == 1 && lo == 0;
            if exchange && bit(w, 0) == 1 {
                return None;
            }
            let base = if exchange {
                Addr(addr.get() & !3)
            } else {
                addr
            };
            let target = super::target(base, 4 + off);
            let (mn, flow) = match (hi, lo) {
                (0, _) => (cm(conds!("b", ".w"), cond), branch_flow(cond, target)),
                (_, 1) => (cm(conds!("bl"), cond), Flow::Call(target)),
                _ => (cm(conds!("blx"), cond), Flow::Call(target)),
            };
            let mut i = at(addr, 4, mn, flow);
            i.push(Operand::Addr(target));
            Some(i)
        }
    }
}

/// The barriers and hints that live among the branches.
fn misc_control(w: u32, cond: u32, addr: Addr) -> Option<Insn> {
    if bits(w, 25, 20) == 0b111011 {
        let option = Operand::Name(super::BARRIERS[bits(w, 3, 0) as usize]);
        let mn = match bits(w, 7, 4) {
            0b0100 => "dsb",
            0b0101 => "dmb",
            0b0110 => "isb",
            0b0010 => return Some(at(addr, 4, "clrex", Flow::Next)),
            _ => return None,
        };
        let mut i = at(addr, 4, mn, Flow::Next);
        i.push(option);
        return Some(i);
    }
    if bits(w, 25, 20) == 0b111010 && bits(w, 10, 8) == 0 {
        const HINTS: [&[&str; 16]; 5] = [
            conds!("nop", ".w"),
            conds!("yield", ".w"),
            conds!("wfe", ".w"),
            conds!("wfi", ".w"),
            conds!("sev", ".w"),
        ];
        let n = bits(w, 7, 0) as usize;
        return (n < HINTS.len()).then(|| at(addr, 4, cm(HINTS[n], cond), Flow::Next));
    }
    None
}

/// Load and store multiple, whose `push` and `pop` spellings take `.w`.
fn block(w: u32, cond: u32, addr: Addr) -> Option<Insn> {
    let (wb, l) = (bit(w, 21) == 1, bit(w, 20) == 1);
    let rn = bits(w, 19, 16);
    let list = bits(w, 15, 0);
    if list.count_ones() < 2 {
        return None;
    }
    let db = match bits(w, 24, 23) {
        0b01 => false,
        0b10 => true,
        _ => return None,
    };
    let stack = rn == 13 && wb;
    let flow = if l && list >> 15 == 1 {
        if rn == 13 {
            Flow::Return
        } else {
            Flow::IndirectBranch
        }
    } else {
        Flow::Next
    };
    let (mn, implicit) = match (l, db, stack) {
        (true, false, true) => (cm(conds!("pop", ".w"), cond), true),
        (false, true, true) => (cm(conds!("push", ".w"), cond), true),
        (true, false, _) => (cm(conds!("ldm", ".w"), cond), false),
        (true, true, _) => (cm(conds!("ldmdb"), cond), false),
        (false, false, _) => (cm(conds!("stm", ".w"), cond), false),
        (false, true, _) => (cm(conds!("stmdb"), cond), false),
    };
    let mut i = at(addr, 4, mn, flow);
    if !implicit {
        if wb {
            i.push(Operand::Name(wb_reg(rn)));
        } else {
            i.push(Operand::Reg(reg(rn)));
        }
    }
    i.push(core_list(list));
    Some(i)
}

/// Load and store dual, the exclusives, and the table branches.
fn dual(w: u32, cond: u32, addr: Addr) -> Option<Insn> {
    let (rn, rt, rt2) = (bits(w, 19, 16), bits(w, 15, 12), bits(w, 11, 8));
    match (bits(w, 24, 23), bits(w, 21, 20)) {
        (0b00, 0b00) => {
            let m = Mem::base_disp(reg(rn), bits(w, 7, 0) as i64 * 4, 4);
            let mut i = at(addr, 4, cm(conds!("strex"), cond), Flow::Next);
            i.push(Operand::Reg(reg(rt2)))
                .push(Operand::Reg(reg(rt)))
                .push(Operand::Mem(m));
            Some(i)
        }
        (0b00, 0b01) => {
            let m = Mem::base_disp(reg(rn), bits(w, 7, 0) as i64 * 4, 4);
            let mut i = at(addr, 4, cm(conds!("ldrex"), cond), Flow::Next);
            i.push(Operand::Reg(reg(rt))).push(Operand::Mem(m));
            Some(i)
        }
        (0b01, 0b01) if bits(w, 7, 4) <= 1 => {
            let half = bit(w, 4) == 1;
            let mut m = Mem::base_disp(reg(rn), 0, if half { 2 } else { 1 });
            m.index = index(reg(bits(w, 3, 0)), half as u8);
            let mut i = at(
                addr,
                4,
                cm(if half { conds!("tbh") } else { conds!("tbb") }, cond),
                Flow::IndirectBranch,
            );
            i.push(Operand::Mem(m));
            Some(i)
        }
        _ => {
            let (p, u, wb, l) = (
                bit(w, 24) == 1,
                bit(w, 23) == 1,
                bit(w, 21) == 1,
                bit(w, 20) == 1,
            );
            if !p && !wb {
                return None;
            }
            let mode = match (p, wb) {
                (false, _) => AddrMode::PostIndex,
                (true, true) => AddrMode::PreIndex,
                (true, false) => AddrMode::Offset,
            };
            let off = bits(w, 7, 0) as i64 * 4;
            let mut m = decimal(Mem {
                seg: None,
                base: Some(reg(rn)),
                index: None,
                disp: if u { off } else { -off },
                mode,
                size: 8,
            });
            if !u && off == 0 {
                m = minus_zero(m);
            }
            let mut i = at(
                addr,
                4,
                cm(if l { conds!("ldrd") } else { conds!("strd") }, cond),
                Flow::Next,
            );
            i.push(Operand::Reg(reg(rt)))
                .push(Operand::Reg(reg(rt2)))
                .push(Operand::Mem(m));
            Some(i)
        }
    }
}

/// The `op1 == 11` half: the single loads and stores, the register
/// data-processing forms, and the multiplies.
fn group11(w: u32, cond: u32, addr: Addr) -> Option<Insn> {
    let op2 = bits(w, 26, 20);
    if op2 & 0b1110000 == 0b0100000 {
        return dp_reg(w, cond, addr);
    }
    if op2 & 0b1111000 == 0b0110000 {
        return multiply(w, cond, addr);
    }
    if op2 & 0b1111000 == 0b0111000 {
        return multiply_long(w, cond, addr);
    }
    if op2 & 0b1000000 == 0 {
        return ldst(w, cond, addr);
    }
    None
}

/// The single-item loads and stores, whose `.w` marks the twelve-bit and
/// register forms and whose absence marks the eight-bit ones.
fn ldst(w: u32, cond: u32, addr: Addr) -> Option<Insn> {
    let signed = bit(w, 24) == 1;
    let wide_imm = bit(w, 23) == 1;
    let size = bits(w, 22, 21);
    let load = bit(w, 20) == 1;
    let (rn, rt) = (bits(w, 19, 16), bits(w, 15, 12));
    if size == 3 || (signed && (!load || size == 2)) || rt == 15 {
        return None;
    }
    let bytes = 1u64 << size;
    let names: [&[&str; 16]; 6] = [
        conds!("strb", ".w"),
        conds!("ldrb", ".w"),
        conds!("strh", ".w"),
        conds!("ldrh", ".w"),
        conds!("str", ".w"),
        conds!("ldr", ".w"),
    ];
    let narrow_names: [&[&str; 16]; 6] = [
        conds!("strb"),
        conds!("ldrb"),
        conds!("strh"),
        conds!("ldrh"),
        conds!("str"),
        conds!("ldr"),
    ];
    let signed_names: [&[&str; 16]; 2] = [conds!("ldrsb", ".w"), conds!("ldrsh", ".w")];
    let signed_narrow: [&[&str; 16]; 2] = [conds!("ldrsb"), conds!("ldrsh")];
    let pick = |wide: bool| -> &'static [&'static str; 16] {
        if signed {
            if wide {
                signed_names[size as usize]
            } else {
                signed_narrow[size as usize]
            }
        } else if wide {
            names[(size * 2 + load as u32) as usize]
        } else {
            narrow_names[(size * 2 + load as u32) as usize]
        }
    };

    if rn == 15 {
        if !load {
            return None;
        }
        let off = bits(w, 11, 0) as i64;
        let mut m = always(Mem::base_disp(
            reg(15),
            if wide_imm { off } else { -off },
            bytes,
        ));
        if !wide_imm && off == 0 {
            m = minus_zero(m);
        }
        let mut i = at(addr, 4, cm(pick(true), cond), Flow::Next);
        i.push(Operand::Reg(reg(rt))).push(Operand::Mem(m));
        return Some(i);
    }
    if wide_imm {
        let m = Mem::base_disp(reg(rn), bits(w, 11, 0) as i64, bytes);
        let mut i = at(addr, 4, cm(pick(true), cond), Flow::Next);
        i.push(Operand::Reg(reg(rt))).push(Operand::Mem(m));
        return Some(i);
    }
    if bits(w, 11, 6) == 0 {
        let mut m = Mem::base_disp(reg(rn), 0, bytes);
        m.index = index(reg(bits(w, 3, 0)), bits(w, 5, 4) as u8);
        let mut i = at(addr, 4, cm(pick(true), cond), Flow::Next);
        i.push(Operand::Reg(reg(rt))).push(Operand::Mem(m));
        return Some(i);
    }
    if bit(w, 11) == 0 {
        return None;
    }
    let (p, u, wb) = (bit(w, 10) == 1, bit(w, 9) == 1, bit(w, 8) == 1);
    if p && u && !wb {
        const T_FORMS: [&[&str; 16]; 6] = [
            conds!("strbt"),
            conds!("ldrbt"),
            conds!("strht"),
            conds!("ldrht"),
            conds!("strt"),
            conds!("ldrt"),
        ];
        const T_SIGNED: [&[&str; 16]; 2] = [conds!("ldrsbt"), conds!("ldrsht")];
        let mn = if signed {
            T_SIGNED[size as usize]
        } else {
            T_FORMS[(size * 2 + load as u32) as usize]
        };
        let m = Mem::base_disp(reg(rn), bits(w, 7, 0) as i64, bytes);
        let mut i = at(addr, 4, cm(mn, cond), Flow::Next);
        i.push(Operand::Reg(reg(rt))).push(Operand::Mem(decimal(m)));
        return Some(i);
    }
    if !p && !wb {
        return None;
    }
    let mode = match (p, wb) {
        (false, _) => AddrMode::PostIndex,
        (true, true) => AddrMode::PreIndex,
        (true, false) => AddrMode::Offset,
    };
    let off = bits(w, 7, 0) as i64;
    let mut m = decimal(Mem {
        seg: None,
        base: Some(reg(rn)),
        index: None,
        disp: if u { off } else { -off },
        mode,
        size: bytes,
    });
    if !u && off == 0 {
        m = minus_zero(m);
    }
    let mut i = at(addr, 4, cm(pick(false), cond), Flow::Next);
    i.push(Operand::Reg(reg(rt))).push(Operand::Mem(m));
    Some(i)
}

/// Shifts by a register, the extends, and the `clz` corner.
fn dp_reg(w: u32, cond: u32, addr: Addr) -> Option<Insn> {
    let (rn, rd, rm) = (bits(w, 19, 16), bits(w, 11, 8), bits(w, 3, 0));
    if bits(w, 15, 12) != 0b1111 {
        return None;
    }
    if bit(w, 23) == 0 && bits(w, 7, 4) == 0 {
        const PLAIN: [&[&str; 16]; 4] = [
            conds!("lsl", ".w"),
            conds!("lsr", ".w"),
            conds!("asr", ".w"),
            conds!("ror", ".w"),
        ];
        const SETS: [&[&str; 16]; 4] = [
            conds!("lsls", ".w"),
            conds!("lsrs", ".w"),
            conds!("asrs", ".w"),
            conds!("rors", ".w"),
        ];
        let op = bits(w, 22, 21) as usize;
        let s = bit(w, 20) == 1;
        let mut i = at(
            addr,
            4,
            cm(if s { SETS[op] } else { PLAIN[op] }, cond),
            Flow::Next,
        );
        i.push(Operand::Reg(reg(rd)))
            .push(Operand::Reg(reg(rn)))
            .push(Operand::Reg(reg(rm)));
        return Some(i);
    }
    if bit(w, 23) == 0 && bits(w, 7, 6) == 0b10 {
        // The four with a sixteen-bit counterpart take `.w`; the two that
        // pack halfwords do not, and neither do the accumulating forms.
        const PLAIN: [&[&str; 16]; 6] = [
            conds!("sxth", ".w"),
            conds!("uxth", ".w"),
            conds!("sxtb16"),
            conds!("uxtb16"),
            conds!("sxtb", ".w"),
            conds!("uxtb", ".w"),
        ];
        const WITH: [&[&str; 16]; 6] = [
            conds!("sxtah"),
            conds!("uxtah"),
            conds!("sxtab16"),
            conds!("uxtab16"),
            conds!("sxtab"),
            conds!("uxtab"),
        ];
        let op = bits(w, 22, 20) as usize;
        if op >= PLAIN.len() {
            return None;
        }
        let plain = rn == 15;
        let mut i = at(
            addr,
            4,
            cm(if plain { PLAIN[op] } else { WITH[op] }, cond),
            Flow::Next,
        );
        i.push(Operand::Reg(reg(rd)));
        if !plain {
            i.push(Operand::Reg(reg(rn)));
        }
        i.push(Operand::Reg(reg(rm)));
        let rotate = bits(w, 5, 4);
        if rotate != 0 {
            const ROTATES: [&str; 4] = ["ror #0", "ror #8", "ror #16", "ror #24"];
            i.push(Operand::Name(ROTATES[rotate as usize]));
        }
        return Some(i);
    }
    if bits(w, 23, 22) == 0b10 && bits(w, 7, 6) == 0b10 {
        if rn != rm {
            return None; // the source is encoded twice and must agree
        }
        let mn = match (bits(w, 21, 20), bits(w, 5, 4)) {
            (0b01, 0b00) => conds!("rev", ".w"),
            (0b01, 0b01) => conds!("rev16", ".w"),
            (0b01, 0b10) => conds!("rbit"),
            (0b01, 0b11) => conds!("revsh", ".w"),
            (0b11, 0b00) => conds!("clz"),
            _ => return None,
        };
        let mut i = at(addr, 4, cm(mn, cond), Flow::Next);
        i.push(Operand::Reg(reg(rd))).push(Operand::Reg(reg(rm)));
        return Some(i);
    }
    None
}

/// `mul`, `mla` and `mls`; the signed multiply corner is left alone.
fn multiply(w: u32, cond: u32, addr: Addr) -> Option<Insn> {
    if bits(w, 22, 20) != 0 || bits(w, 7, 5) != 0 {
        return None;
    }
    let (rn, ra, rd, rm) = (
        bits(w, 19, 16),
        bits(w, 15, 12),
        bits(w, 11, 8),
        bits(w, 3, 0),
    );
    let mls = bit(w, 4) == 1;
    if ra == 15 && mls {
        return None;
    }
    let mut i = at(
        addr,
        4,
        cm(
            if mls {
                conds!("mls")
            } else if ra == 15 {
                conds!("mul")
            } else {
                conds!("mla")
            },
            cond,
        ),
        Flow::Next,
    );
    i.push(Operand::Reg(reg(rd)))
        .push(Operand::Reg(reg(rn)))
        .push(Operand::Reg(reg(rm)));
    if ra != 15 {
        i.push(Operand::Reg(reg(ra)));
    }
    Some(i)
}

/// The long multiplies and the divides, which share a table.
fn multiply_long(w: u32, cond: u32, addr: Addr) -> Option<Insn> {
    let (rn, lo, hi, rm) = (
        bits(w, 19, 16),
        bits(w, 15, 12),
        bits(w, 11, 8),
        bits(w, 3, 0),
    );
    let op2 = bits(w, 7, 4);
    let mn = match (bits(w, 22, 20), op2) {
        (0b000, 0b0000) => conds!("smull"),
        (0b010, 0b0000) => conds!("umull"),
        (0b100, 0b0000) => conds!("smlal"),
        (0b110, 0b0000) => conds!("umlal"),
        (0b110, 0b0110) => conds!("umaal"),
        (0b001, 0b1111) => conds!("sdiv"),
        (0b011, 0b1111) => conds!("udiv"),
        _ => return None,
    };
    let divide = op2 == 0b1111;
    let mut i = at(addr, 4, cm(mn, cond), Flow::Next);
    if divide {
        i.push(Operand::Reg(reg(hi)))
            .push(Operand::Reg(reg(rn)))
            .push(Operand::Reg(reg(rm)));
    } else {
        i.push(Operand::Reg(reg(lo)))
            .push(Operand::Reg(reg(hi)))
            .push(Operand::Reg(reg(rn)))
            .push(Operand::Reg(reg(rm)));
    }
    Some(i)
}
