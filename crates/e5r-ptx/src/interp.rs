//! A concrete interpreter of the subset, written to mirror
//! `verification/ptx/Ptx/Semantics/Instruction.lean` line for line.
//!
//! It is not trusted. It is used to search for counterexamples, and every
//! counterexample it finds is replayed by the Lean kernel against the Lean
//! definitions before anything is reported (`e5r-verify ptx check`). It is
//! also cross-checked against the Lean model and the GPU on the differential
//! test cases (`tests/interp_vs_model.rs`, `scripts/check-ptx-difftest.sh`).

use crate::ast::*;
use std::collections::HashMap;

/// `%tid` etc. of one thread, and the launch shape.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Dim3 {
    /// `.x`
    pub x: u32,
    /// `.y`
    pub y: u32,
    /// `.z`
    pub z: u32,
}

impl Dim3 {
    fn get(self, d: Dim) -> u32 {
        match d {
            Dim::X => self.x,
            Dim::Y => self.y,
            Dim::Z => self.z,
        }
    }
}

/// One allocation, as `Ptx.Region`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Region {
    /// First byte.
    pub base: u64,
    /// Size in bytes.
    pub size: u128,
}

/// What a thread observes of its launch (`Ptx.Ctx`).
#[derive(Clone, Debug)]
pub struct Ctx {
    /// `%tid`
    pub tid: Dim3,
    /// `%ntid`
    pub ntid: Dim3,
    /// `%ctaid`
    pub ctaid: Dim3,
    /// `%nctaid`
    pub nctaid: Dim3,
    /// Raw parameter bits, `.u32` zero-extended; missing names read 0.
    pub params: HashMap<String, u64>,
}

/// Byte-addressed memory with a default of zero.
#[derive(Clone, Debug, Default)]
pub struct Mem {
    /// Bytes that are not zero (or were written).
    pub bytes: HashMap<u64, u8>,
}

impl Mem {
    /// The byte at `a`.
    pub fn get(&self, a: u64) -> u8 {
        self.bytes.get(&a).copied().unwrap_or(0)
    }
    /// Little-endian read of `n` bytes, zero-extended.
    pub fn rd(&self, a: u64, n: u32) -> u64 {
        (0..n).rev().fold(0u64, |v, i| {
            v << 8 | self.get(a.wrapping_add(i as u64)) as u64
        })
    }
    /// Little-endian write of the low `n` bytes of `v`.
    pub fn wr(&mut self, a: u64, n: u32, v: u64) {
        for i in 0..n {
            self.bytes
                .insert(a.wrapping_add(i as u64), (v >> (8 * i)) as u8);
        }
    }
}

/// `Ptx.TState`.
#[derive(Clone, Debug, Default)]
pub struct TState {
    /// Index of the next statement.
    pub pc: usize,
    /// Data registers; missing ones read `init`.
    pub r: HashMap<String, u64>,
    /// Predicate registers; missing ones read false.
    pub p: HashMap<String, bool>,
}

/// One memory access: address, size in bytes, is-store.
pub type Access = (u64, u32, bool);

/// The result of one step (`Ptx.Res`), with the access it made.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Res {
    /// The thread moved; the access it made, if any.
    Ok(Option<Access>),
    /// `ret`/`exit`.
    Halted,
    /// A fault, with the reason.
    Fault(String),
}

fn width(t: Ty) -> u32 {
    t.width().unwrap_or(32)
}

fn lo32(v: u64) -> u64 {
    v & 0xffff_ffff
}

fn sext32(v: u64) -> u64 {
    v as u32 as i32 as i64 as u64
}

fn imm(v: i128) -> u64 {
    v as u64 // BitVec.ofInt 64: two's complement modulo 2^64
}

/// `Region.holds` and `accessOk`, as natural numbers.
pub fn access_ok(al: &[Region], a: u64, n: u32) -> bool {
    a % n as u64 == 0
        && al.iter().any(|r| {
            r.base as u128 <= a as u128 && a as u128 + n as u128 <= r.base as u128 + r.size
        })
}

impl TState {
    fn reg(&self, r: &str) -> u64 {
        self.r.get(r).copied().unwrap_or(0)
    }
    fn pred(&self, r: &str) -> bool {
        self.p.get(r).copied().unwrap_or(false)
    }
    fn op(&self, c: &Ctx, o: &Operand) -> u64 {
        match o {
            Operand::Reg(r) => self.reg(r),
            Operand::Imm(v) => imm(*v),
            Operand::Sreg(s) => {
                (match s {
                    Sreg::Tid(d) => c.tid.get(*d),
                    Sreg::Ntid(d) => c.ntid.get(*d),
                    Sreg::Ctaid(d) => c.ctaid.get(*d),
                    Sreg::Nctaid(d) => c.nctaid.get(*d),
                }) as u64
            }
        }
    }
    fn set(&mut self, d: &str, v: u64) {
        self.r.insert(d.to_string(), v);
        self.pc += 1;
    }
}

fn at_width(w: u32, f: impl Fn(u64, u64) -> u64, a: u64, b: u64) -> u64 {
    if w == 32 {
        lo32(f(lo32(a), lo32(b)))
    } else {
        f(a, b)
    }
}

fn fit(t: Ty, v: u64) -> u64 {
    if width(t) == 32 { lo32(v) } else { v }
}

fn cmp(c: CmpOp, t: Ty, a: u64, b: u64) -> Option<bool> {
    let (x, y, w) = if width(t) == 32 {
        (lo32(a), lo32(b), 32)
    } else {
        (a, b, 64)
    };
    let s = |v: u64| {
        if w == 32 {
            v as u32 as i32 as i64
        } else {
            v as i64
        }
    };
    let signed = matches!(t, Ty::S32 | Ty::S64);
    Some(match c {
        CmpOp::Eq => x == y,
        CmpOp::Ne => x != y,
        _ if t.is_bits() || t == Ty::Pred => return None,
        CmpOp::Lt if signed => s(x) < s(y),
        CmpOp::Le if signed => s(x) <= s(y),
        CmpOp::Gt if signed => s(x) > s(y),
        CmpOp::Ge if signed => s(x) >= s(y),
        CmpOp::Lt | CmpOp::Lo => x < y,
        CmpOp::Le | CmpOp::Ls => x <= y,
        CmpOp::Gt | CmpOp::Hi => x > y,
        CmpOp::Ge | CmpOp::Hs => x >= y,
    })
}

fn convert(dt: Ty, st: Ty, a: u64) -> u64 {
    match (width(st), width(dt)) {
        (32, 32) | (64, 32) => lo32(a),
        (64, 64) => a,
        _ => {
            if matches!(st, Ty::S32 | Ty::S64) {
                sext32(a)
            } else {
                lo32(a)
            }
        }
    }
}

fn shift(w: u32, a: u64, b: u64, kind: u8) -> u64 {
    let n = lo32(b).min(w as u64) as u32;
    if w == 32 {
        let x = lo32(a) as u32;
        lo32(match kind {
            0 => {
                if n >= 32 {
                    0
                } else {
                    (x << n) as u64
                }
            }
            1 => {
                if n >= 32 {
                    0
                } else {
                    (x >> n) as u64
                }
            }
            _ => ((x as i32) >> n.min(31)) as u32 as u64,
        })
    } else {
        match kind {
            0 => {
                if n >= 64 {
                    0
                } else {
                    a << n
                }
            }
            1 => {
                if n >= 64 {
                    0
                } else {
                    a >> n
                }
            }
            _ => ((a as i64) >> n.min(63)) as u64,
        }
    }
}

/// One step of thread `s` (`Ptx.stepMem`).
pub fn step(k: &Kernel, al: &[Region], c: &Ctx, s: &mut TState, m: &mut Mem) -> Res {
    let Some(st) = k.body.get(s.pc) else {
        return Res::Fault(format!("pc {} past the end of the body", s.pc));
    };
    if let Some(g) = &st.guard {
        if s.pred(&g.pred) == g.neg {
            s.pc += 1;
            return Res::Ok(None);
        }
    }
    use Instr::*;
    match &st.instr {
        Bin(b, t, d, x, y) => {
            let (a, bb) = (s.op(c, x), s.op(c, y));
            let w = width(*t);
            let v = match b {
                BinOp::Add => at_width(w, u64::wrapping_add, a, bb),
                BinOp::Sub => at_width(w, u64::wrapping_sub, a, bb),
                BinOp::MulLo => at_width(w, u64::wrapping_mul, a, bb),
                BinOp::And => at_width(w, |x, y| x & y, a, bb),
                BinOp::Or => at_width(w, |x, y| x | y, a, bb),
                BinOp::Xor => at_width(w, |x, y| x ^ y, a, bb),
                BinOp::Shl => shift(w, a, bb, 0),
                BinOp::Shr if matches!(t, Ty::S32 | Ty::S64) => shift(w, a, bb, 2),
                BinOp::Shr => shift(w, a, bb, 1),
                BinOp::MulWide => match t {
                    Ty::U32 => lo32(a).wrapping_mul(lo32(bb)),
                    Ty::S32 => sext32(a).wrapping_mul(sext32(bb)),
                    _ => return Res::Fault("mul.wide type".into()),
                },
            };
            s.set(d, v);
        }
        MadLo(t, d, x, y, z) => {
            let w = width(*t);
            let p = at_width(w, u64::wrapping_mul, s.op(c, x), s.op(c, y));
            let v = at_width(w, u64::wrapping_add, p, s.op(c, z));
            s.set(d, v);
        }
        Not(t, d, a) => {
            let v = fit(*t, !s.op(c, a));
            s.set(d, v);
        }
        Mov(t, d, a) => {
            let v = fit(*t, s.op(c, a));
            s.set(d, v);
        }
        Setp(op, t, p, a, b) => match cmp(*op, *t, s.op(c, a), s.op(c, b)) {
            Some(v) => {
                s.p.insert(p.clone(), v);
                s.pc += 1;
            }
            None => return Res::Fault("ordered comparison on a .b type".into()),
        },
        Selp(t, d, a, b, p) => {
            let v = fit(*t, if s.pred(p) { s.op(c, a) } else { s.op(c, b) });
            s.set(d, v);
        }
        Cvt(dt, st, d, a) => {
            let v = convert(*dt, *st, s.op(c, a));
            s.set(d, v);
        }
        CvtaGlobal(d, a) => {
            let v = s.op(c, a);
            s.set(d, v);
        }
        Ld(Space::Param, t, d, Address::Param(n, off)) if off.unwrap_or(0) == 0 => {
            let v = fit(*t, c.params.get(n).copied().unwrap_or(0));
            s.set(d, v);
        }
        Ld(Space::Global, t, d, Address::Reg(r, off)) => {
            let a = s.reg(r).wrapping_add(imm(off.unwrap_or(0)));
            let n = width(*t) / 8;
            if !access_ok(al, a, n) {
                return Res::Fault(format!("load of {n} bytes at {a:#x}"));
            }
            let v = m.rd(a, n);
            s.set(d, v);
            return Res::Ok(Some((a, n, false)));
        }
        St(Space::Global, t, Address::Reg(r, off), v) => {
            let a = s.reg(r).wrapping_add(imm(off.unwrap_or(0)));
            let n = width(*t) / 8;
            if !access_ok(al, a, n) {
                return Res::Fault(format!("store of {n} bytes at {a:#x}"));
            }
            let x = s.op(c, v);
            m.wr(a, n, x);
            s.pc += 1;
            return Res::Ok(Some((a, n, true)));
        }
        Ld(..) | St(..) => return Res::Fault("unsupported memory form".into()),
        Bra(_, l) => match k.labels.iter().find(|(m, _)| m == l) {
            Some((_, pc)) => s.pc = *pc,
            None => return Res::Fault(format!("missing label {l}")),
        },
        Ret | Exit => return Res::Halted,
    }
    Res::Ok(None)
}

/// How a solo run of one thread ended.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum End {
    /// `ret`/`exit` after this many steps.
    Halted(usize),
    /// A fault at this step.
    Fault(usize, String),
    /// Still running after the fuel.
    OutOfFuel,
}

/// Run one thread alone from `m` for at most `fuel` steps. Returns how it
/// ended and every access it made, in order.
pub fn run_solo(
    k: &Kernel,
    al: &[Region],
    c: &Ctx,
    m: &mut Mem,
    fuel: usize,
) -> (End, Vec<Access>) {
    let mut s = TState::default();
    let mut acc = Vec::new();
    for i in 0..fuel {
        match step(k, al, c, &mut s, m) {
            Res::Ok(a) => acc.extend(a),
            Res::Halted => return (End::Halted(i), acc),
            Res::Fault(why) => return (End::Fault(i, why), acc),
        }
    }
    (End::OutOfFuel, acc)
}
