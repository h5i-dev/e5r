//! A concrete interpreter of the subset, written to mirror
//! `verification/ptx/Ptx/Semantics/Instruction.lean` and `SIMT.lean` line
//! for line.
//!
//! It is not trusted. It is used to search for counterexamples, and every
//! counterexample it finds is replayed by the Lean kernel against the Lean
//! definitions before anything is reported (`e5r ptx check`). It is
//! also cross-checked against the Lean model and the GPU on the differential
//! test cases (`scripts/check-ptx-difftest.sh`).

use crate::ast::*;
use crate::fp;
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
    /// Aggregate argument bytes; absent bytes read zero, independently of scalars.
    pub byte_params: HashMap<String, Vec<u8>>,
    /// Where each `.shared` variable is placed (`Launch.shared`); missing
    /// names read 0.
    pub sym: HashMap<String, u64>,
}

/// Parameter loads preserve scalar semantics and bound aggregate byte accesses
/// by the declaration, rather than by a possibly incomplete supplied vector.
pub fn param_value(k: &Kernel, c: &Ctx, t: Ty, name: &str, off: i128) -> Option<u64> {
    if let Some(p) = k.aggregate_params.iter().find(|p| p.name == name) {
        let bytes = t.width()? / 8;
        let off = u32::try_from(off).ok()?;
        if p.align < bytes
            || p.align % bytes != 0
            || off % bytes != 0
            || off.checked_add(bytes)? > p.size
        {
            return None;
        }
        let data = c.byte_params.get(name);
        Some((0..bytes).rev().fold(0, |v, i| {
            (v << 8)
                | data
                    .and_then(|b| b.get((off + i) as usize))
                    .copied()
                    .unwrap_or(0) as u64
        }))
    } else if off == 0 {
        Some(fit(t, c.params.get(name).copied().unwrap_or(0)))
    } else {
        None
    }
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

/// The data spaces (`Ptx.Sp`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Sp {
    /// Global memory.
    Global,
    /// The CTA's shared memory.
    Shared,
}

/// `Ptx.AccKind`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    /// A load.
    Read,
    /// A store.
    Write,
    /// An atomic read-modify-write.
    Atomic,
}

/// One memory access (`Ptx.Acc`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Access {
    /// Space.
    pub sp: Sp,
    /// First byte.
    pub addr: u64,
    /// Bytes.
    pub size: u32,
    /// Load, store or atomic.
    pub kind: Kind,
}

/// The result of one step (`Ptx.TRes`), with the access it made.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Res {
    /// The thread moved; the access it made, if any.
    Ok(Option<Access>),
    /// The thread waits at `bar.sync` (its pc is unchanged).
    Wait,
    /// `ret`/`exit`.
    Halted,
    /// A fault, with the reason.
    Fault(String),
}

/// The allocations of each space (`Launch.allocs`).
#[derive(Clone, Debug, Default)]
pub struct Allocs {
    /// Global allocations.
    pub global: Vec<Region>,
    /// The `.shared` variables, as placed.
    pub shared: Vec<Region>,
}

impl Allocs {
    fn of(&self, sp: Sp) -> &[Region] {
        match sp {
            Sp::Global => &self.global,
            Sp::Shared => &self.shared,
        }
    }
}

/// The shared regions of `k` under a placement (`Launch.sregions`).
pub fn shared_regions(k: &Kernel, sym: &HashMap<String, u64>) -> Vec<Region> {
    k.shared
        .iter()
        .map(|d| Region {
            base: sym.get(&d.name).copied().unwrap_or(0),
            size: d.size() as u128,
        })
        .collect()
}

/// A placement ptxas could choose (`LayoutOk`): in declaration order, each
/// variable at the next multiple of its alignment, starting at `start`.
pub fn layout(k: &Kernel, start: u64) -> HashMap<String, u64> {
    let mut at = start;
    let mut out = HashMap::new();
    for d in &k.shared {
        let a = d.alignment() as u64;
        at = at.div_ceil(a) * a;
        out.insert(d.name.clone(), at);
        at += d.size();
    }
    out
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
            Operand::Sym(n) => c.sym.get(n).copied().unwrap_or(0),
            Operand::FImm(v, _) => *v,
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

/// `Ptx.atomVal`: the value an `atom`/`red` stores.
fn atom_val(op: AtomOp, t: Ty, old: u64, b: u64) -> u64 {
    let w = width(t);
    let signed = matches!(t, Ty::S32 | Ty::S64);
    let le = |x: u64, y: u64| {
        if signed {
            if w == 32 {
                (x as u32 as i32) <= (y as u32 as i32)
            } else {
                (x as i64) <= (y as i64)
            }
        } else {
            x <= y
        }
    };
    match op {
        AtomOp::Add => at_width(w, u64::wrapping_add, old, b),
        AtomOp::And => at_width(w, |x, y| x & y, old, b),
        AtomOp::Or => at_width(w, |x, y| x | y, old, b),
        AtomOp::Xor => at_width(w, |x, y| x ^ y, old, b),
        AtomOp::Exch => fit(t, b),
        AtomOp::Min => at_width(w, |x, y| if le(x, y) { x } else { y }, old, b),
        AtomOp::Max => at_width(w, |x, y| if le(y, x) { x } else { y }, old, b),
    }
}

/// `Ptx.dataAddr`.
fn data_addr(c: &Ctx, s: &TState, sp: Space, a: &Address) -> Option<(Sp, u64)> {
    match (sp, a) {
        (Space::Global, Address::Reg(r, off)) => {
            Some((Sp::Global, s.reg(r).wrapping_add(imm(off.unwrap_or(0)))))
        }
        (Space::Shared, Address::Reg(r, off)) => {
            Some((Sp::Shared, s.reg(r).wrapping_add(imm(off.unwrap_or(0)))))
        }
        (Space::Shared, Address::Param(n, off)) => Some((
            Sp::Shared,
            c.sym
                .get(n)
                .copied()
                .unwrap_or(0)
                .wrapping_add(imm(off.unwrap_or(0))),
        )),
        _ => None,
    }
}

/// One step of thread `s` (`Ptx.tstep`) against global memory `g` and its
/// CTA's shared memory `sh`.
pub fn step(k: &Kernel, al: &Allocs, c: &Ctx, s: &mut TState, g: &mut Mem, sh: &mut Mem) -> Res {
    let Some(st) = k.body.get(s.pc) else {
        return Res::Fault(format!("pc {} past the end of the body", s.pc));
    };
    if let Some(gd) = &st.guard {
        if s.pred(&gd.pred) == gd.neg {
            s.pc += 1;
            return Res::Ok(None);
        }
    }
    use Instr::*;
    match &st.instr {
        Por(d, a, b) => {
            let v = s.pred(a) || s.pred(b);
            s.p.insert(d.clone(), v);
            s.pc += 1;
        }
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
        Bfi32(d, a, b, pos, len) => {
            let (pos, len) = (*pos as u32, *len as u32);
            let mask = if pos >= 32 || len == 0 {
                0
            } else {
                (u32::MAX >> (32 - len.min(32)))
                    .checked_shl(pos)
                    .unwrap_or(0)
            };
            let v = ((s.op(c, a) as u32).checked_shl(pos).unwrap_or(0) & mask)
                | ((s.op(c, b) as u32) & !mask);
            s.set(d, v as u64);
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
        Ld(Space::Param, t, d, Address::Param(n, off)) => {
            let Some(v) = param_value(k, c, *t, n, off.unwrap_or(0)) else {
                return Res::Fault("out-of-bounds or unaligned parameter load".into());
            };
            s.set(d, v);
        }
        Ld(Space::Param, ..) | St(Space::Param, ..) => {
            return Res::Fault("unsupported memory form".into());
        }
        Ld(sp, t, d, a) => {
            let Some((sp, a)) = data_addr(c, s, *sp, a) else {
                return Res::Fault("unsupported memory form".into());
            };
            let n = width(*t) / 8;
            if !access_ok(al.of(sp), a, n) {
                return Res::Fault(format!("load of {n} bytes at {sp:?} {a:#x}"));
            }
            let m = if sp == Sp::Global { &*g } else { &*sh };
            let v = m.rd(a, n);
            s.set(d, v);
            return Res::Ok(Some(Access {
                sp,
                addr: a,
                size: n,
                kind: Kind::Read,
            }));
        }
        St(sp, t, a, v) => {
            let Some((sp, a)) = data_addr(c, s, *sp, a) else {
                return Res::Fault("unsupported memory form".into());
            };
            let n = width(*t) / 8;
            if !access_ok(al.of(sp), a, n) {
                return Res::Fault(format!("store of {n} bytes at {sp:?} {a:#x}"));
            }
            let x = s.op(c, v);
            let m = if sp == Sp::Global { g } else { sh };
            m.wr(a, n, x);
            s.pc += 1;
            return Res::Ok(Some(Access {
                sp,
                addr: a,
                size: n,
                kind: Kind::Write,
            }));
        }
        Atom(sp, _, t, _, a, _) | Cas(sp, t, _, a, _, _) | Red(sp, _, t, a, _) => {
            let Some((sp, a)) = data_addr(c, s, *sp, a) else {
                return Res::Fault("unsupported memory form".into());
            };
            let n = width(*t) / 8;
            if !access_ok(al.of(sp), a, n) {
                return Res::Fault(format!("atomic of {n} bytes at {sp:?} {a:#x}"));
            }
            let m = if sp == Sp::Global { g } else { sh };
            let old = m.rd(a, n);
            let new = match &st.instr {
                Atom(_, op, _, _, _, b) | Red(_, op, _, _, b) => atom_val(*op, *t, old, s.op(c, b)),
                Cas(_, _, _, _, b, e) => {
                    if fit(*t, old) == fit(*t, s.op(c, b)) {
                        s.op(c, e)
                    } else {
                        old
                    }
                }
                _ => unreachable!(),
            };
            m.wr(a, n, new);
            match &st.instr {
                Atom(_, _, _, d, _, _) | Cas(_, _, d, _, _, _) => s.set(d, fit(*t, old)),
                _ => s.pc += 1,
            }
            return Res::Ok(Some(Access {
                sp,
                addr: a,
                size: n,
                kind: Kind::Atomic,
            }));
        }
        Bar => return Res::Wait,
        Bra(_, l) => match k.labels.iter().find(|(m, _)| m == l) {
            Some((_, pc)) => s.pc = *pc,
            None => return Res::Fault(format!("missing label {l}")),
        },
        Ret | Exit => return Res::Halted,
        FBin(op, m, ftz, sat, t, d, a, b) => {
            let f = t.fmt();
            let (x, y) = (fbits(*t, s.op(c, a)), fbits(*t, s.op(c, b)));
            let r = match op {
                crate::ast::FBin::Add => fp::fadd(f, *m, *ftz, *sat, x, y),
                crate::ast::FBin::Sub => fp::fsub(f, *m, *ftz, *sat, x, y),
                crate::ast::FBin::Mul => fp::fmul(f, *m, *ftz, *sat, x, y),
                crate::ast::FBin::Div => fp::fdiv(f, *m, *ftz, x, y),
            };
            s.set(d, fres(*t, r));
        }
        Ffma(m, ftz, sat, t, d, a, b, e) => {
            let (x, y, z) = (
                fbits(*t, s.op(c, a)),
                fbits(*t, s.op(c, b)),
                fbits(*t, s.op(c, e)),
            );
            let r = fp::ffma(t.fmt(), *m, *ftz, *sat, x, y, z);
            s.set(d, fres(*t, r));
        }
        Fsqrt(m, ftz, t, d, a) => {
            let r = fp::fsqrt(t.fmt(), *m, *ftz, fbits(*t, s.op(c, a)));
            s.set(d, fres(*t, r));
        }
        Frcp(m, ftz, t, d, a) => {
            let r = fp::frcp(t.fmt(), *m, *ftz, fbits(*t, s.op(c, a)));
            s.set(d, fres(*t, r));
        }
        Fneg(ftz, t, d, a) => {
            let r = fp::fneg(t.fmt(), *ftz, fbits(*t, s.op(c, a)));
            s.set(d, fres(*t, r));
        }
        Fabs(ftz, t, d, a) => {
            let r = fp::fabs(t.fmt(), *ftz, fbits(*t, s.op(c, a)));
            s.set(d, fres(*t, r));
        }
        Fminmax(mx, ftz, nan, t, d, a, b) => {
            let r = fp::fminmax(
                t.fmt(),
                *mx,
                *ftz,
                *nan,
                fbits(*t, s.op(c, a)),
                fbits(*t, s.op(c, b)),
            );
            s.set(d, fres(*t, r));
        }
        Fsetp(op, ftz, t, p, a, b) => {
            let v = fp::fsetp(
                t.fmt(),
                *op,
                *ftz,
                fbits(*t, s.op(c, a)),
                fbits(*t, s.op(c, b)),
            );
            s.p.insert(p.clone(), v);
            s.pc += 1;
        }
        CvtF(dt, st, r, ftz, sat, d, a) => match cvt_float(*dt, *st, *r, *ftz, *sat, s.op(c, a)) {
            Some(v) => s.set(d, v),
            None => return Res::Fault("cvt form outside the subset".into()),
        },
    }
    Res::Ok(None)
}

/// `Ptx.fbits`.
fn fbits(t: Ty, v: u64) -> u64 {
    fit(t, v)
}

/// `Ptx.fres` with the default NaN oracle (`Launch.nan` is `fun _ _ => 0`,
/// which is not a NaN, so every NaN result is `Fmt.qnan`).
fn fres(t: Ty, r: Option<u64>) -> u64 {
    r.unwrap_or_else(|| t.fmt().qnan())
}

/// `Ptx.intOf`.
fn int_of(t: Ty, v: u64) -> i128 {
    match (width(t), matches!(t, Ty::S32 | Ty::S64)) {
        (32, true) => v as u32 as i32 as i128,
        (32, false) => v as u32 as i128,
        (_, true) => v as i64 as i128,
        _ => v as i128,
    }
}

/// `Ptx.cvtFloat`.
fn cvt_float(dt: Ty, st: Ty, r: CvtRnd, ftz: bool, sat: bool, a: u64) -> Option<u64> {
    let (df, sf) = (dt.fmt(), st.fmt());
    match (dt.is_float(), st.is_float(), r) {
        (false, true, CvtRnd::I(m)) => {
            let w = width(dt);
            let signed = matches!(dt, Ty::S32 | Ty::S64);
            Some(fit(
                dt,
                fp::to_int(sf, m, ftz && st == Ty::F32, signed, w, fbits(st, a)),
            ))
        }
        (true, false, CvtRnd::F(m)) => {
            let v = fp::of_int(df, m, false, int_of(st, a));
            Some(fres(dt, fp::sat_bits(df, sat, Some(v))))
        }
        (true, true, CvtRnd::I(m)) if dt == st => Some(fres(
            dt,
            fp::sat_bits(
                df,
                sat,
                fp::round_integral(df, m, ftz && dt == Ty::F32, fbits(st, a)),
            ),
        )),
        (true, true, CvtRnd::F(m)) if dt == Ty::F32 && st == Ty::F64 => {
            Some(fres(dt, fp::convert_f(df, sf, m, ftz, sat, fbits(st, a))))
        }
        (true, true, CvtRnd::None) if dt == Ty::F64 && st == Ty::F32 => Some(fres(
            dt,
            fp::convert_f(df, sf, fp::RMode::Rn, ftz, sat, fbits(st, a)),
        )),
        _ => None,
    }
}

/// How a solo run of one thread ended.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum End {
    /// `ret`/`exit` after this many steps.
    Halted(usize),
    /// At a barrier after this many steps.
    Wait(usize),
    /// A fault at this step.
    Fault(usize, String),
    /// Still running after the fuel.
    OutOfFuel,
}

/// Run one thread alone from its state, for at most `fuel` steps, until it
/// halts, faults or reaches a barrier. Returns how it ended and every access
/// it made, with the step it made it at, in order.
pub fn run_until_wait(
    k: &Kernel,
    al: &Allocs,
    c: &Ctx,
    s: &mut TState,
    g: &mut Mem,
    sh: &mut Mem,
    fuel: usize,
) -> (End, Vec<(usize, Access)>) {
    let mut acc = Vec::new();
    for i in 0..fuel {
        match step(k, al, c, s, g, sh) {
            Res::Ok(a) => acc.extend(a.map(|a| (i, a))),
            Res::Wait => return (End::Wait(i), acc),
            Res::Halted => return (End::Halted(i), acc),
            Res::Fault(why) => return (End::Fault(i, why), acc),
        }
    }
    (End::OutOfFuel, acc)
}

/// Run one thread alone from the start for at most `fuel` steps.
pub fn run_solo(
    k: &Kernel,
    al: &Allocs,
    c: &Ctx,
    g: &mut Mem,
    sh: &mut Mem,
    fuel: usize,
) -> (End, Vec<Access>) {
    let mut s = TState::default();
    let (e, acc) = run_until_wait(k, al, c, &mut s, g, sh, fuel);
    (e, acc.into_iter().map(|(_, a)| a).collect())
}

/// One access in a whole-launch run: who made it, in which phase of its
/// CTA (barriers passed), at which of its own steps, and what it was.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Event {
    /// The thread's index in [`Launch::threads`].
    pub thread: usize,
    /// Barriers its CTA had passed.
    pub phase: usize,
    /// The thread's step count before this access.
    pub step: usize,
    /// The access.
    pub access: Access,
}

/// A concrete launch for [`run_grid`].
#[derive(Clone, Debug)]
pub struct Launch {
    /// `%nctaid`.
    pub grid: Dim3,
    /// `%ntid`.
    pub block: Dim3,
    /// Parameter bits.
    pub params: HashMap<String, u64>,
    /// Aggregate argument bytes, copied unchanged into every thread context.
    pub byte_params: HashMap<String, Vec<u8>>,
    /// Shared variable placement.
    pub sym: HashMap<String, u64>,
    /// Global allocations.
    pub alloc: Vec<Region>,
}

impl Launch {
    /// Every thread, in the order of `Launch.threads`: CTAs z, y, x, then
    /// threads z, y, x.
    pub fn threads(&self) -> Vec<(Dim3, Dim3)> {
        let mut v = Vec::new();
        for cz in 0..self.grid.z {
            for cy in 0..self.grid.y {
                for cx in 0..self.grid.x {
                    for tz in 0..self.block.z {
                        for ty in 0..self.block.y {
                            for tx in 0..self.block.x {
                                v.push((
                                    Dim3 {
                                        x: cx,
                                        y: cy,
                                        z: cz,
                                    },
                                    Dim3 {
                                        x: tx,
                                        y: ty,
                                        z: tz,
                                    },
                                ));
                            }
                        }
                    }
                }
            }
        }
        v
    }

    /// The context of one thread.
    pub fn ctx(&self, cta: Dim3, tid: Dim3) -> Ctx {
        Ctx {
            tid,
            ntid: self.block,
            ctaid: cta,
            nctaid: self.grid,
            params: self.params.clone(),
            byte_params: self.byte_params.clone(),
            sym: self.sym.clone(),
        }
    }

    /// The allocations, for kernel `k`.
    pub fn allocs(&self, k: &Kernel) -> Allocs {
        Allocs {
            global: self.alloc.clone(),
            shared: shared_regions(k, &self.sym),
        }
    }
}

/// How a whole-launch run ended.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GridEnd {
    /// Every thread halted.
    Done,
    /// Thread (index) faulted.
    Fault(usize, String),
    /// A barrier diverged in the CTA of this thread (`Ptx.Diverged`).
    Diverged(usize),
    /// Fuel ran out.
    OutOfFuel,
}

/// Run the whole launch on one schedule: CTA after CTA in `threads` order;
/// inside a CTA, each thread in order runs until it waits, halts or faults,
/// then the barrier is released when all wait at the same `bar.sync`.
/// Every step is a `Ptx.Step`, so this is one of the model's executions.
/// `sh0` is the initial content of every CTA's shared memory.
pub fn run_grid(
    k: &Kernel,
    l: &Launch,
    g: &mut Mem,
    sh0: &Mem,
    fuel: usize,
) -> (GridEnd, Vec<Event>) {
    let al = l.allocs(k);
    let all = l.threads();
    let per = (l.block.x as usize) * (l.block.y as usize) * (l.block.z as usize);
    let mut events = Vec::new();
    let mut left = fuel;
    for (ci, chunk) in all.chunks(per.max(1)).enumerate() {
        if per == 0 {
            break;
        }
        let mut sh = sh0.clone();
        let ctxs: Vec<Ctx> = chunk.iter().map(|(c, t)| l.ctx(*c, *t)).collect();
        let mut ts: Vec<TState> = vec![TState::default(); chunk.len()];
        let mut steps = vec![0usize; chunk.len()];
        let mut phase = 0;
        loop {
            let mut ends = Vec::new();
            for (i, s) in ts.iter_mut().enumerate() {
                let (e, acc) = run_until_wait(k, &al, &ctxs[i], s, g, &mut sh, left);
                let idx = ci * per + i;
                for (st, a) in acc {
                    events.push(Event {
                        thread: idx,
                        phase,
                        step: steps[i] + st,
                        access: a,
                    });
                }
                let used = match &e {
                    End::Halted(n) | End::Wait(n) => *n,
                    End::Fault(_, why) => return (GridEnd::Fault(idx, why.clone()), events),
                    End::OutOfFuel => return (GridEnd::OutOfFuel, events),
                };
                steps[i] += used;
                left -= used;
                ends.push(e);
            }
            let waiting: Vec<usize> = (0..ts.len())
                .filter(|i| matches!(ends[*i], End::Wait(_)))
                .collect();
            if waiting.is_empty() {
                break; // every thread halted
            }
            let pc = ts[waiting[0]].pc;
            if waiting.len() != ts.len() || waiting.iter().any(|i| ts[*i].pc != pc) {
                return (GridEnd::Diverged(ci * per + waiting[0]), events);
            }
            for s in ts.iter_mut() {
                s.pc += 1;
            }
            phase += 1;
            if left == 0 {
                return (GridEnd::OutOfFuel, events);
            }
            left -= 1;
        }
    }
    (GridEnd::Done, events)
}
