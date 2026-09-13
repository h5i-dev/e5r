//! VFP, shared by both instruction sets.
//!
//! A T32 coprocessor instruction is bit for bit the A32 one, so both decoders
//! hand the same word here and only the condition differs: A32 reads it from
//! bits 31:28, T32 from the IT state.

use r12e_core::Addr;

use crate::insn::{AddrMode, Flow, Insn, Mem, Operand};

use super::text::{decimal, minus_zero};
use super::{bit, bits, cm, reg, vfp_list, vreg, wb_reg};

/// One mnemonic in both precisions, single first.
macro_rules! fp {
    ($b:literal) => {
        [conds!($b, ".f32"), conds!($b, ".f64")]
    };
}

/// The VFP system registers by their four-bit field.
const VFP_SYSREGS: [&str; 16] = [
    "fpsid", "fpscr", "s2", "s3", "s4", "mvfr2", "mvfr1", "mvfr0", "fpexc", "fpinst", "fpinst2",
    "s11", "s12", "s13", "s14", "s15",
];

/// Bits 27:25 == 110: the coprocessor loads and stores, which for VFP are
/// `vldr`, `vstr`, the multiple forms, and the 64-bit core transfers.
pub fn ldst(w: u32, cond: u32, addr: Addr, len: u8) -> Option<Insn> {
    let double = match bits(w, 11, 8) {
        0b1010 => false,
        0b1011 => true,
        _ => return None,
    };
    if bits(w, 24, 21) == 0b0010 {
        return core_pair(w, cond, addr, len, double);
    }
    let (p, u, wb, l) = (bit(w, 24), bit(w, 23), bit(w, 21) == 1, bit(w, 20) == 1);
    let rn = bits(w, 19, 16);
    let vd = bits(w, 15, 12);
    let d = bit(w, 22);
    let first = if double { d << 4 | vd } else { vd << 1 | d };

    if p == 1 && !wb {
        let off = bits(w, 7, 0) as i64 * 4;
        let mut m = decimal(Mem {
            seg: None,
            base: Some(reg(rn)),
            index: None,
            disp: if u == 1 { off } else { -off },
            mode: AddrMode::Offset,
            size: if double { 8 } else { 4 },
        });
        if u == 0 && off == 0 {
            m = minus_zero(m);
        }
        let mut i = Insn::new(
            addr,
            len,
            cm(if l { conds!("vldr") } else { conds!("vstr") }, cond),
            Flow::Next,
        );
        i.push(Operand::Reg(vreg(first, double)))
            .push(Operand::Mem(m));
        return Some(i);
    }
    if p == u {
        return None;
    }
    let imm8 = bits(w, 7, 0);
    if double && imm8 & 1 == 1 {
        return None; // the deprecated `fldmx` and `fstmx` forms
    }
    // A run that would leave the register file is truncated rather than
    // rejected, which is what LLVM's decoder does with it.
    let mut count = if double { imm8 / 2 } else { imm8 };
    if count == 0 {
        return None;
    }
    if double && (count > 16 || first + count > 32) {
        count = 16.min(32 - first);
    } else if !double && first + count > 32 {
        count = 32 - first;
    }
    let stack = rn == 13 && wb;
    // `vpush` is the decrement-before store and `vpop` the increment-after
    // load, the two directions a stack needs.
    let (mn, implicit) = match (l, p == 1, stack) {
        (true, false, true) => (cm(conds!("vpop"), cond), true),
        (false, true, true) => (cm(conds!("vpush"), cond), true),
        (true, false, _) => (cm(conds!("vldmia"), cond), false),
        (true, true, _) => (cm(conds!("vldmdb"), cond), false),
        (false, false, _) => (cm(conds!("vstmia"), cond), false),
        (false, true, _) => (cm(conds!("vstmdb"), cond), false),
    };
    let mut i = Insn::new(addr, len, mn, Flow::Next);
    if !implicit {
        if wb {
            i.push(Operand::Name(wb_reg(rn)));
        } else {
            i.push(Operand::Reg(reg(rn)));
        }
    }
    i.push(vfp_list(double, first, count));
    Some(i)
}

/// `vmov` between a pair of core registers and one double or two singles.
fn core_pair(w: u32, cond: u32, addr: Addr, len: u8, double: bool) -> Option<Insn> {
    let (rt, rt2) = (bits(w, 15, 12), bits(w, 19, 16));
    let vm = bits(w, 3, 0);
    let m = bit(w, 5);
    let first = if double { m << 4 | vm } else { vm << 1 | m };
    let mut i = Insn::new(addr, len, cm(conds!("vmov"), cond), Flow::Next);
    let core = [Operand::Reg(reg(rt)), Operand::Reg(reg(rt2))];
    let vec: Vec<Operand> = if double {
        vec![Operand::Reg(vreg(first, true))]
    } else {
        vec![
            Operand::Reg(vreg(first, false)),
            Operand::Reg(vreg(first + 1, false)),
        ]
    };
    let (a, b) = if bit(w, 20) == 1 {
        (&core[..], &vec[..])
    } else {
        (&vec[..], &core[..])
    };
    for op in a.iter().chain(b) {
        i.push(*op);
    }
    Some(i)
}

/// Bits 27:25 == 111: VFP arithmetic, the core transfers, and `svc`.
pub fn dp(w: u32, cond: u32, addr: Addr, len: u8) -> Option<Insn> {
    if bit(w, 24) == 1 {
        let mut i = Insn::new(addr, len, cm(conds!("svc"), cond), Flow::Syscall);
        i.push(Operand::UImm(bits(w, 23, 0) as u64));
        return Some(i);
    }
    let double = match bits(w, 11, 8) {
        0b1010 => false,
        0b1011 => true,
        _ => return None,
    };
    if bit(w, 4) == 1 {
        return transfer(w, cond, addr, len, double);
    }
    arith(w, cond, addr, len, double)
}

/// Between a core register and a single-precision one, or the status register.
fn transfer(w: u32, cond: u32, addr: Addr, len: u8, double: bool) -> Option<Insn> {
    if double {
        return None; // the lane transfers, which are Advanced SIMD
    }
    let (rt, vn, n) = (bits(w, 15, 12), bits(w, 19, 16), bit(w, 7));
    let load = bit(w, 20) == 1;
    match bits(w, 23, 21) {
        0b000 => {
            let mut i = Insn::new(addr, len, cm(conds!("vmov"), cond), Flow::Next);
            let (core, vec) = (
                Operand::Reg(reg(rt)),
                Operand::Reg(vreg(vn << 1 | n, false)),
            );
            if load {
                i.push(core).push(vec);
            } else {
                i.push(vec).push(core);
            }
            Some(i)
        }
        0b111 => {
            let sys = Operand::Name(VFP_SYSREGS[vn as usize]);
            // Only the status register has the flags spelling.
            let flags = vn == 1;
            let mut i = Insn::new(
                addr,
                len,
                cm(if load { conds!("vmrs") } else { conds!("vmsr") }, cond),
                Flow::Next,
            );
            if load {
                let dst = if rt == 15 && flags {
                    Operand::Name("APSR_nzcv")
                } else {
                    Operand::Reg(reg(rt))
                };
                i.push(dst).push(sys);
            } else {
                i.push(sys).push(Operand::Reg(reg(rt)));
            }
            Some(i)
        }
        _ => None,
    }
}

/// The three-register arithmetic and the `1x11` corner that holds everything
/// else: the immediate move, the unary operations, the compares and `vcvt`.
fn arith(w: u32, cond: u32, addr: Addr, len: u8, double: bool) -> Option<Insn> {
    let sz = double as usize;
    let num = |v: u32, hi: u32| if double { hi << 4 | v } else { v << 1 | hi };
    let d = num(bits(w, 15, 12), bit(w, 22));
    let n = num(bits(w, 19, 16), bit(w, 7));
    let m = num(bits(w, 3, 0), bit(w, 5));
    let opc3 = bit(w, 6);
    let three = |mn: &'static str| {
        let mut i = Insn::new(addr, len, mn, Flow::Next);
        i.push(Operand::Reg(vreg(d, double)))
            .push(Operand::Reg(vreg(n, double)))
            .push(Operand::Reg(vreg(m, double)));
        i
    };
    let table = match bit(w, 23) << 2 | bits(w, 21, 20) {
        0b000 => [fp!("vmla"), fp!("vmls")],
        0b001 => [fp!("vnmls"), fp!("vnmla")],
        0b010 => [fp!("vmul"), fp!("vnmul")],
        0b011 => [fp!("vadd"), fp!("vsub")],
        0b100 if opc3 == 0 => [fp!("vdiv"), fp!("vdiv")],
        0b101 => [fp!("vfnms"), fp!("vfnma")],
        0b110 => [fp!("vfma"), fp!("vfms")],
        0b111 => return other(w, cond, addr, len, double),
        _ => return None,
    };
    Some(three(cm(table[opc3 as usize][sz], cond)))
}

/// The `opc1 == 1x11` group, where four more bits pick the operation.
fn other(w: u32, cond: u32, addr: Addr, len: u8, double: bool) -> Option<Insn> {
    let sz = double as usize;
    let num = |v: u32, hi: u32, dbl: bool| if dbl { hi << 4 | v } else { v << 1 | hi };
    let d = num(bits(w, 15, 12), bit(w, 22), double);
    let m = num(bits(w, 3, 0), bit(w, 5), double);
    let opc2 = bits(w, 19, 16);
    let opc3 = bits(w, 7, 6);

    if opc3 & 1 == 0 {
        // The immediate, whose eight bits expand the same way at both widths.
        let imm8 = bits(w, 19, 16) << 4 | bits(w, 3, 0);
        let mut i = Insn::new(addr, len, cm(fp!("vmov")[sz], cond), Flow::Next);
        i.push(Operand::Reg(vreg(d, double)))
            .push(Operand::FpImm(expand_imm(imm8)));
        return Some(i);
    }
    let unary = |mn: &'static str| {
        let mut i = Insn::new(addr, len, mn, Flow::Next);
        i.push(Operand::Reg(vreg(d, double)))
            .push(Operand::Reg(vreg(m, double)));
        i
    };
    match (opc2, opc3) {
        (0b0000, 0b01) => Some(unary(cm(fp!("vmov")[sz], cond))),
        (0b0000, 0b11) => Some(unary(cm(fp!("vabs")[sz], cond))),
        (0b0001, 0b01) => Some(unary(cm(fp!("vneg")[sz], cond))),
        (0b0001, 0b11) => Some(unary(cm(fp!("vsqrt")[sz], cond))),
        (0b0100, 0b01) => Some(unary(cm(fp!("vcmp")[sz], cond))),
        (0b0100, 0b11) => Some(unary(cm(fp!("vcmpe")[sz], cond))),
        (0b0101, 0b01) | (0b0101, 0b11) => {
            let mn = if opc3 == 0b01 {
                fp!("vcmp")[sz]
            } else {
                fp!("vcmpe")[sz]
            };
            let mut i = Insn::new(addr, len, cm(mn, cond), Flow::Next);
            i.push(Operand::Reg(vreg(d, double)))
                .push(Operand::Count(0));
            Some(i)
        }
        (0b0111, 0b11) => {
            // Between the two precisions: the destination is the other one.
            const CVT: [&[&str; 16]; 2] = [conds!("vcvt", ".f64.f32"), conds!("vcvt", ".f32.f64")];
            let dst = num(bits(w, 15, 12), bit(w, 22), !double);
            let mut i = Insn::new(addr, len, cm(CVT[sz], cond), Flow::Next);
            i.push(Operand::Reg(vreg(dst, !double)))
                .push(Operand::Reg(vreg(m, double)));
            Some(i)
        }
        (0b1000, 0b01) | (0b1000, 0b11) => {
            const CVT: [[&[&str; 16]; 2]; 2] = [
                [conds!("vcvt", ".f32.u32"), conds!("vcvt", ".f64.u32")],
                [conds!("vcvt", ".f32.s32"), conds!("vcvt", ".f64.s32")],
            ];
            let src = num(bits(w, 3, 0), bit(w, 5), false);
            let mut i = Insn::new(
                addr,
                len,
                cm(CVT[(opc3 >> 1) as usize][sz], cond),
                Flow::Next,
            );
            i.push(Operand::Reg(vreg(d, double)))
                .push(Operand::Reg(vreg(src, false)));
            Some(i)
        }
        (0b1100, _) | (0b1101, _) => {
            const CVT: [[&[&str; 16]; 2]; 2] = [
                [conds!("vcvtr", ".u32.f32"), conds!("vcvtr", ".u32.f64")],
                [conds!("vcvtr", ".s32.f32"), conds!("vcvtr", ".s32.f64")],
            ];
            const CVTZ: [[&[&str; 16]; 2]; 2] = [
                [conds!("vcvt", ".u32.f32"), conds!("vcvt", ".u32.f64")],
                [conds!("vcvt", ".s32.f32"), conds!("vcvt", ".s32.f64")],
            ];
            let signed = (opc2 & 1) as usize;
            let table = if opc3 >> 1 == 1 { &CVTZ } else { &CVT };
            let dst = num(bits(w, 15, 12), bit(w, 22), false);
            let mut i = Insn::new(addr, len, cm(table[signed][sz], cond), Flow::Next);
            i.push(Operand::Reg(vreg(dst, false)))
                .push(Operand::Reg(vreg(m, double)));
            Some(i)
        }
        _ => None,
    }
}

/// `VFPExpandImm`, as the double it names; the single-precision encoding names
/// the same value with fewer bits behind it.
fn expand_imm(imm8: u32) -> u64 {
    let sign = (imm8 >> 7) as u64 & 1;
    let b6 = (imm8 >> 6) & 1;
    let exp = ((1 - b6) << 10 | if b6 == 1 { 0xff << 2 } else { 0 } | (imm8 >> 4) & 3) as u64;
    sign << 63 | exp << 52 | ((imm8 & 0xf) as u64) << 48
}
