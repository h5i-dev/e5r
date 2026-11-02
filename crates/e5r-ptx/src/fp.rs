//! `.f32`/`.f64` operations on bit patterns, mirroring
//! `verification/ptx/Ptx/Semantics/Float.lean` and `FloatCore.lean`.
//!
//! Untrusted like the rest of the interpreter: the Lean definitions are the
//! semantics, and the differential test compares this file, the Lean model
//! and the GPU on the same inputs. The Lean side rounds a `Rat`; this side
//! rounds an exact value `N / D · 2^e` with a small unsigned big integer, and
//! the two are written to compute the same function (`round` below follows
//! `Fmt.round`, `roundQ`, `precRoundQ`, `overflows`, `tiny`).
//!
//! `None` is a NaN result; the caller takes its bits from the NaN oracle.

use std::cmp::Ordering;

/// A small unsigned big integer, little-endian 64-bit limbs, no trailing
/// zero limbs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Big(Vec<u64>);

impl Big {
    fn norm(mut v: Vec<u64>) -> Big {
        while v.last() == Some(&0) {
            v.pop();
        }
        Big(v)
    }
    /// From a `u128`.
    pub fn from(x: u128) -> Big {
        Big::norm(vec![x as u64, (x >> 64) as u64])
    }
    fn is_zero(&self) -> bool {
        self.0.is_empty()
    }
    /// Number of significant bits (0 for zero).
    pub fn bits(&self) -> u64 {
        match self.0.last() {
            None => 0,
            Some(h) => 64 * (self.0.len() as u64 - 1) + (64 - h.leading_zeros() as u64),
        }
    }
    fn shl(&self, n: u64) -> Big {
        if self.is_zero() {
            return self.clone();
        }
        let (w, b) = ((n / 64) as usize, (n % 64) as u32);
        let mut v = vec![0u64; w];
        let mut carry = 0u64;
        for &x in &self.0 {
            if b == 0 {
                v.push(x);
            } else {
                v.push((x << b) | carry);
                carry = x >> (64 - b);
            }
        }
        if carry != 0 {
            v.push(carry);
        }
        Big::norm(v)
    }
    fn cmp(&self, o: &Big) -> Ordering {
        if self.0.len() != o.0.len() {
            return self.0.len().cmp(&o.0.len());
        }
        for i in (0..self.0.len()).rev() {
            match self.0[i].cmp(&o.0[i]) {
                Ordering::Equal => {}
                c => return c,
            }
        }
        Ordering::Equal
    }
    fn add(&self, o: &Big) -> Big {
        let n = self.0.len().max(o.0.len());
        let mut v = Vec::with_capacity(n + 1);
        let mut c = 0u128;
        for i in 0..n {
            let s = *self.0.get(i).unwrap_or(&0) as u128 + *o.0.get(i).unwrap_or(&0) as u128 + c;
            v.push(s as u64);
            c = s >> 64;
        }
        if c != 0 {
            v.push(c as u64);
        }
        Big::norm(v)
    }
    /// `self − o`, requires `self ≥ o`.
    fn sub(&self, o: &Big) -> Big {
        let mut v = Vec::with_capacity(self.0.len());
        let mut borrow = 0i128;
        for i in 0..self.0.len() {
            let d = self.0[i] as i128 - *o.0.get(i).unwrap_or(&0) as i128 - borrow;
            if d < 0 {
                v.push((d + (1i128 << 64)) as u64);
                borrow = 1;
            } else {
                v.push(d as u64);
                borrow = 0;
            }
        }
        Big::norm(v)
    }
    fn mul(&self, o: &Big) -> Big {
        let mut v = vec![0u64; self.0.len() + o.0.len()];
        for (i, &a) in self.0.iter().enumerate() {
            let mut c = 0u128;
            for (j, &b) in o.0.iter().enumerate() {
                let t = v[i + j] as u128 + a as u128 * b as u128 + c;
                v[i + j] = t as u64;
                c = t >> 64;
            }
            let mut k = i + o.0.len();
            while c != 0 {
                let t = v[k] as u128 + c;
                v[k] = t as u64;
                c = t >> 64;
                k += 1;
            }
        }
        Big::norm(v)
    }
    /// `(self / d, self % d)` when the quotient is below `2^128`.
    fn divrem_small(&self, d: &Big) -> (u128, Big) {
        let mut r = self.clone();
        let mut q = 0u128;
        if r.cmp(d) == Ordering::Less {
            return (0, r);
        }
        let top = r.bits() - d.bits();
        assert!(top < 128, "quotient too large");
        for i in (0..=top).rev() {
            let t = d.shl(i);
            if r.cmp(&t) != Ordering::Less {
                r = r.sub(&t);
                q |= 1u128 << i;
            }
        }
        (q, r)
    }
}

/// `Fp.RMode`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RMode {
    /// to nearest, ties to even
    Rn,
    /// toward zero
    Rz,
    /// toward −∞
    Rm,
    /// toward +∞
    Rp,
}

/// `Fp.Fmt`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fmt {
    /// Fraction bits.
    pub fb: u32,
    /// Exponent bits.
    pub eb: u32,
}

/// binary32
pub const F32: Fmt = Fmt { fb: 23, eb: 8 };
/// binary64
pub const F64: Fmt = Fmt { fb: 52, eb: 11 };

/// An exact nonzero-or-zero value `±N / D · 2^e`, `D > 0`.
#[derive(Clone, Debug)]
struct Q {
    neg: bool,
    n: Big,
    d: Big,
    e: i64,
}

impl Q {
    fn is_zero(&self) -> bool {
        self.n.is_zero()
    }
    /// `⌊log₂ |q|⌋`, `q ≠ 0` (`Fp.ilog2`).
    fn ilog2(&self) -> i64 {
        let k = self.n.bits() as i64 - self.d.bits() as i64;
        // |q| < 2^k ⇔ N·2^e < D·2^k  (exponent e moved to the shifts)
        if self.lt_pow2(k + self.e) { k + self.e - 1 } else { k + self.e }
    }
    /// `|q| < 2^k`.
    fn lt_pow2(&self, k: i64) -> bool {
        let (a, b) = self.scaled(k);
        a.cmp(&b) == Ordering::Less
    }
    /// `(A, B)` with `|q| / 2^k = A / B`.
    fn scaled(&self, k: i64) -> (Big, Big) {
        let s = self.e - k;
        if s >= 0 {
            (self.n.shl(s as u64), self.d.clone())
        } else {
            (self.n.clone(), self.d.shl((-s) as u64))
        }
    }
}

impl Fmt {
    fn bias(self) -> i64 {
        (1i64 << (self.eb - 1)) - 1
    }
    fn emin(self) -> i64 {
        1 - self.bias()
    }
    fn emax(self) -> i64 {
        self.bias()
    }
    fn sign_bit(self) -> u64 {
        1u64 << (self.eb + self.fb)
    }
    fn exp_max(self) -> u64 {
        (1u64 << self.eb) - 1
    }
    /// The sign bit is set.
    pub fn sgn(self, x: u64) -> bool {
        x & self.sign_bit() != 0
    }
    fn bexp(self, x: u64) -> u64 {
        (x >> self.fb) & self.exp_max()
    }
    fn frac(self, x: u64) -> u64 {
        x & ((1u64 << self.fb) - 1)
    }
    /// NaN pattern.
    pub fn is_nan(self, x: u64) -> bool {
        self.bexp(x) == self.exp_max() && self.frac(x) != 0
    }
    fn is_inf(self, x: u64) -> bool {
        self.bexp(x) == self.exp_max() && self.frac(x) == 0
    }
    fn is_zero(self, x: u64) -> bool {
        self.bexp(x) == 0 && self.frac(x) == 0
    }
    fn is_sub(self, x: u64) -> bool {
        self.bexp(x) == 0 && self.frac(x) != 0
    }
    fn zero(self, neg: bool) -> u64 {
        if neg { self.sign_bit() } else { 0 }
    }
    fn inf(self, neg: bool) -> u64 {
        self.zero(neg) + (self.exp_max() << self.fb)
    }
    fn max_fin(self, neg: bool) -> u64 {
        self.zero(neg) + ((self.exp_max() - 1) << self.fb) + ((1u64 << self.fb) - 1)
    }
    /// `1.0`.
    pub fn one(self) -> u64 {
        (self.bias() as u64) << self.fb
    }
    /// The NaN `Fmt.qnan` (used when the oracle's bits are not a NaN).
    pub fn qnan(self) -> u64 {
        (self.exp_max() << self.fb) + (1u64 << (self.fb - 1))
    }
    /// Mantissa and exponent of a finite pattern: `|x| = m · 2^e`.
    fn me(self, x: u64) -> (u64, i64) {
        if self.bexp(x) == 0 {
            (self.frac(x), self.emin() - self.fb as i64)
        } else {
            (self.frac(x) + (1u64 << self.fb), self.bexp(x) as i64 - self.bias() - self.fb as i64)
        }
    }
    fn to_q(self, x: u64) -> Q {
        let (m, e) = self.me(x);
        Q { neg: self.sgn(x), n: Big::from(m as u128), d: Big::from(1), e }
    }
    fn flush(self, ftz: bool, x: u64) -> u64 {
        if ftz && self.is_sub(x) { self.zero(self.sgn(x)) } else { x }
    }
    fn neg_bits(self, x: u64) -> u64 {
        x ^ self.sign_bit()
    }

    /// `|q|` rounded at last-place exponent `qe`: `(M, inexact)`.
    fn round_at(self, m: RMode, q: &Q, qe: i64) -> u128 {
        let (a, b) = q.scaled(qe);
        let (k, r) = a.divrem_small(&b);
        let r2 = r.shl(1);
        let up = match m {
            RMode::Rn => match r2.cmp(&b) {
                Ordering::Greater => true,
                Ordering::Equal => k % 2 == 1,
                Ordering::Less => false,
            },
            RMode::Rz => false,
            RMode::Rm => q.neg && !r.is_zero(),
            RMode::Rp => !q.neg && !r.is_zero(),
        };
        k + up as u128
    }

    /// `Fmt.encode` of `M · 2^qe` (`M ≥ 1`, in range).
    fn encode(self, neg: bool, mut mm: u128, mut qe: i64) -> u64 {
        let p = self.fb + 1;
        while mm >= 1u128 << p {
            assert!(mm % 2 == 0);
            mm >>= 1;
            qe += 1;
        }
        while mm < 1u128 << self.fb && qe > self.emin() - self.fb as i64 {
            mm <<= 1;
            qe -= 1;
        }
        let s = self.zero(neg);
        if mm < 1u128 << self.fb {
            s + mm as u64
        } else {
            let be = (qe + self.fb as i64 + self.bias()) as u64;
            s + (be << self.fb) + (mm as u64 - (1u64 << self.fb))
        }
    }

    /// `Fmt.round`.
    fn round(self, m: RMode, ftz: bool, q: &Q, zneg: bool) -> u64 {
        if q.is_zero() {
            return self.zero(zneg);
        }
        let neg = q.neg;
        let e = q.ilog2();
        let fb = self.fb as i64;
        let p = self.fb + 1;
        let pm = self.round_at(m, q, e - fb); // precRoundQ = pm · 2^(e − fb)
        let overflow = e > self.emax() || (e == self.emax() && pm == 1u128 << p);
        if overflow {
            let inf = m == RMode::Rn || (m == RMode::Rm && neg) || (m == RMode::Rp && !neg);
            return if inf { self.inf(neg) } else { self.max_fin(neg) };
        }
        let tiny = e < self.emin() && !(e == self.emin() - 1 && pm == 1u128 << p);
        if ftz && tiny {
            return self.zero(neg);
        }
        let qe = e.max(self.emin()) - fb;
        let mm = self.round_at(m, q, qe);
        if mm == 0 { self.zero(neg) } else { self.encode(neg, mm, qe) }
    }

    fn sat(self, on: bool, r: Option<u64>) -> Option<u64> {
        if !on {
            return r;
        }
        match r {
            None => Some(0),
            Some(x) if self.is_nan(x) || self.sgn(x) => Some(0),
            Some(x) if self.is_inf(x) || self.gt_one(x) => Some(self.one()),
            Some(x) => Some(x),
        }
    }
    fn gt_one(self, x: u64) -> bool {
        // positive finite: compare patterns
        x > self.one()
    }
}

fn add_q(a: &Q, b: &Q) -> Q {
    // both dyadic (d = 1)
    let e = a.e.min(b.e);
    let x = a.n.shl((a.e - e) as u64);
    let y = b.n.shl((b.e - e) as u64);
    let (neg, n) = if a.neg == b.neg {
        (a.neg, x.add(&y))
    } else {
        match x.cmp(&y) {
            Ordering::Less => (b.neg, y.sub(&x)),
            _ => (a.neg, x.sub(&y)),
        }
    };
    Q { neg, n, d: Big::from(1), e }
}

fn mul_q(a: &Q, b: &Q) -> Q {
    Q { neg: a.neg != b.neg, n: a.n.mul(&b.n), d: a.d.mul(&b.d), e: a.e + b.e }
}

fn add_core(f: Fmt, m: RMode, ftz: bool, a: u64, b: u64) -> Option<u64> {
    if f.is_nan(a) || f.is_nan(b) {
        return None;
    }
    if f.is_inf(a) && f.is_inf(b) {
        return if f.sgn(a) == f.sgn(b) { Some(f.inf(f.sgn(a))) } else { None };
    }
    if f.is_inf(a) {
        return Some(a);
    }
    if f.is_inf(b) {
        return Some(b);
    }
    let zneg = if f.is_zero(a) && f.is_zero(b) && f.sgn(a) == f.sgn(b) {
        f.sgn(a)
    } else {
        m == RMode::Rm
    };
    Some(f.round(m, ftz, &add_q(&f.to_q(a), &f.to_q(b)), zneg))
}

/// `Fp.fadd`.
pub fn fadd(f: Fmt, m: RMode, ftz: bool, sat: bool, a: u64, b: u64) -> Option<u64> {
    f.sat(sat, add_core(f, m, ftz, f.flush(ftz, a), f.flush(ftz, b)))
}

/// `Fp.fsub`.
pub fn fsub(f: Fmt, m: RMode, ftz: bool, sat: bool, a: u64, b: u64) -> Option<u64> {
    let b = f.flush(ftz, b);
    let b = if f.is_nan(b) { b } else { f.neg_bits(b) };
    f.sat(sat, add_core(f, m, ftz, f.flush(ftz, a), b))
}

/// `Fp.fmul`.
pub fn fmul(f: Fmt, m: RMode, ftz: bool, sat: bool, a: u64, b: u64) -> Option<u64> {
    let (a, b) = (f.flush(ftz, a), f.flush(ftz, b));
    let neg = f.sgn(a) != f.sgn(b);
    let invalid = (f.is_zero(a) && f.is_inf(b)) || (f.is_inf(a) && f.is_zero(b));
    let r = if f.is_nan(a) || f.is_nan(b) || invalid {
        None
    } else if f.is_inf(a) || f.is_inf(b) {
        Some(f.inf(neg))
    } else {
        Some(f.round(m, ftz, &mul_q(&f.to_q(a), &f.to_q(b)), neg))
    };
    f.sat(sat, r)
}

/// `Fp.ffma`.
pub fn ffma(f: Fmt, m: RMode, ftz: bool, sat: bool, a: u64, b: u64, c: u64) -> Option<u64> {
    let (a, b, c) = (f.flush(ftz, a), f.flush(ftz, b), f.flush(ftz, c));
    let pneg = f.sgn(a) != f.sgn(b);
    let invalid = (f.is_zero(a) && f.is_inf(b)) || (f.is_inf(a) && f.is_zero(b));
    let r = if f.is_nan(a) || f.is_nan(b) || f.is_nan(c) || invalid {
        None
    } else if f.is_inf(a) || f.is_inf(b) {
        if f.is_inf(c) && f.sgn(c) != pneg { None } else { Some(f.inf(pneg)) }
    } else if f.is_inf(c) {
        Some(c)
    } else {
        let zneg = if (f.is_zero(a) || f.is_zero(b)) && f.is_zero(c) && pneg == f.sgn(c) {
            pneg
        } else {
            m == RMode::Rm
        };
        let q = add_q(&mul_q(&f.to_q(a), &f.to_q(b)), &f.to_q(c));
        Some(f.round(m, ftz, &q, zneg))
    };
    f.sat(sat, r)
}

/// `Fp.fdiv`.
pub fn fdiv(f: Fmt, m: RMode, ftz: bool, a: u64, b: u64) -> Option<u64> {
    let (a, b) = (f.flush(ftz, a), f.flush(ftz, b));
    let neg = f.sgn(a) != f.sgn(b);
    if f.is_nan(a) || f.is_nan(b) {
        return None;
    }
    if (f.is_inf(a) && f.is_inf(b)) || (f.is_zero(a) && f.is_zero(b)) {
        return None;
    }
    if f.is_inf(a) {
        return Some(f.inf(neg));
    }
    if f.is_inf(b) {
        return Some(f.zero(neg));
    }
    if f.is_zero(b) {
        return Some(f.inf(neg));
    }
    let (qa, qb) = (f.to_q(a), f.to_q(b));
    let q = Q { neg, n: qa.n, d: qb.n, e: qa.e - qb.e };
    Some(f.round(m, ftz, &q, neg))
}

/// `Fp.frcp`.
pub fn frcp(f: Fmt, m: RMode, ftz: bool, a: u64) -> Option<u64> {
    fdiv(f, m, ftz, f.one(), a)
}

fn isqrt(n: u128) -> u128 {
    if n == 0 {
        return 0;
    }
    let mut x = (n as f64).sqrt() as u128;
    while x * x > n {
        x -= 1;
    }
    while (x + 1) * (x + 1) <= n {
        x += 1;
    }
    x
}

/// `Fp.fsqrt`.
pub fn fsqrt(f: Fmt, m: RMode, ftz: bool, a: u64) -> Option<u64> {
    let a = f.flush(ftz, a);
    if f.is_nan(a) {
        return None;
    }
    if f.is_zero(a) {
        return Some(a);
    }
    if f.sgn(a) {
        return None;
    }
    if f.is_inf(a) {
        return Some(a);
    }
    let q = f.to_q(a);
    let lg = q.ilog2();
    let e = lg.div_euclid(2).max(f.emin()) - f.fb as i64;
    // y = q / 4^e = A / B
    let (ya, yb) = q.scaled(2 * e);
    let (fl, _) = ya.divrem_small(&yb);
    let k = isqrt(fl);
    // y vs (k + ½)² ⇔ 4A vs (2k+1)² B ; y = k² ⇔ A = k² B
    let h = Big::from(2 * k + 1);
    let lhs = ya.shl(2);
    let rhs = h.mul(&h).mul(&yb);
    let exact = ya.cmp(&Big::from(k * k).mul(&yb)) == Ordering::Equal;
    let r = match m {
        RMode::Rn => match lhs.cmp(&rhs) {
            Ordering::Less => k,
            Ordering::Greater => k + 1,
            Ordering::Equal => k + k % 2,
        },
        RMode::Rz | RMode::Rm => k,
        RMode::Rp => {
            if exact {
                k
            } else {
                k + 1
            }
        }
    };
    Some(f.encode(false, r, e))
}

/// `Fp.fneg`.
pub fn fneg(f: Fmt, ftz: bool, a: u64) -> Option<u64> {
    let a = f.flush(ftz, a);
    if f.is_nan(a) { None } else { Some(f.neg_bits(a)) }
}

/// `Fp.fabs`.
pub fn fabs(f: Fmt, ftz: bool, a: u64) -> Option<u64> {
    let a = f.flush(ftz, a);
    if f.is_nan(a) { None } else { Some(a & !f.sign_bit()) }
}

/// Signed order of finite patterns as integers: sign-magnitude to a key.
fn key(f: Fmt, x: u64) -> i128 {
    let mag = (x & !f.sign_bit()) as i128;
    if f.sgn(x) { -mag - 1 } else { mag }
}

/// `Fp.ltSigned`: `a < b` as numbers with `-0 < +0` (non-NaN inputs).
fn lt_signed(f: Fmt, a: u64, b: u64) -> bool {
    // On non-NaN patterns, the order of magnitudes is the order of the bit
    // patterns, and `-0` gets key −1 below `+0`'s 0.
    key(f, a) < key(f, b)
}

/// `Fp.fminmax`.
pub fn fminmax(f: Fmt, is_max: bool, ftz: bool, nan: bool, a: u64, b: u64) -> Option<u64> {
    let (a, b) = (f.flush(ftz, a), f.flush(ftz, b));
    if f.is_nan(a) && f.is_nan(b) {
        return None;
    }
    if nan && (f.is_nan(a) || f.is_nan(b)) {
        return None;
    }
    if f.is_nan(a) {
        return Some(b);
    }
    if f.is_nan(b) {
        return Some(a);
    }
    Some(if is_max {
        if lt_signed(f, b, a) { a } else { b }
    } else if lt_signed(f, a, b) {
        a
    } else {
        b
    })
}

/// `Fp.FCmp`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum FCmp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Equ,
    Neu,
    Ltu,
    Leu,
    Gtu,
    Geu,
    Num,
    Nan,
}

impl FCmp {
    /// The PTX spelling, which is also the Lean constructor.
    pub fn name(self) -> &'static str {
        use FCmp::*;
        match self {
            Eq => "eq",
            Ne => "ne",
            Lt => "lt",
            Le => "le",
            Gt => "gt",
            Ge => "ge",
            Equ => "equ",
            Neu => "neu",
            Ltu => "ltu",
            Leu => "leu",
            Gtu => "gtu",
            Geu => "geu",
            Num => "num",
            Nan => "nan",
        }
    }
    /// Parse a spelling.
    pub fn from_name(s: &str) -> Option<FCmp> {
        use FCmp::*;
        Some(match s {
            "eq" => Eq,
            "ne" => Ne,
            "lt" => Lt,
            "le" => Le,
            "gt" => Gt,
            "ge" => Ge,
            "equ" => Equ,
            "neu" => Neu,
            "ltu" => Ltu,
            "leu" => Leu,
            "gtu" => Gtu,
            "geu" => Geu,
            "num" => Num,
            "nan" => Nan,
            _ => return None,
        })
    }
}

/// `Fp.fsetp`.
pub fn fsetp(f: Fmt, c: FCmp, ftz: bool, a: u64, b: u64) -> bool {
    let (a, b) = (f.flush(ftz, a), f.flush(ftz, b));
    let un = f.is_nan(a) || f.is_nan(b);
    let o = if f.is_zero(a) && f.is_zero(b) {
        Ordering::Equal
    } else if !un {
        key(f, a).cmp(&key(f, b))
    } else {
        Ordering::Equal
    };
    use FCmp::*;
    match c {
        Eq => !un && o == Ordering::Equal,
        Ne => !un && o != Ordering::Equal,
        Lt => !un && o == Ordering::Less,
        Le => !un && o != Ordering::Greater,
        Gt => !un && o == Ordering::Greater,
        Ge => !un && o != Ordering::Less,
        Equ => un || o == Ordering::Equal,
        Neu => un || o != Ordering::Equal,
        Ltu => un || o == Ordering::Less,
        Leu => un || o != Ordering::Greater,
        Gtu => un || o == Ordering::Greater,
        Geu => un || o != Ordering::Less,
        Num => !un,
        Nan => un,
    }
}

/// `roundInt m (toQ a)` for finite `a`, as a signed integer clamped to
/// `±2^70` (enough for every clamp below; the exact value beyond it does not
/// matter there).
fn round_int(f: Fmt, m: RMode, a: u64) -> i128 {
    let q = f.to_q(a);
    if q.is_zero() {
        return 0;
    }
    if q.ilog2() >= 70 {
        return if q.neg { -(1i128 << 70) } else { 1i128 << 70 };
    }
    let mag = f.round_at(m, &q, 0) as i128;
    if q.neg { -mag } else { mag }
}

/// `Fp.toInt`.
pub fn to_int(f: Fmt, m: RMode, ftz: bool, signed: bool, w: u32, a: u64) -> u64 {
    let a = f.flush(ftz, a);
    let (lo, hi): (i128, i128) = if signed {
        (-(1i128 << (w - 1)), (1i128 << (w - 1)) - 1)
    } else {
        (0, (1i128 << w) - 1)
    };
    let enc = |v: i128| (v.rem_euclid(1i128 << w)) as u64;
    if f.is_nan(a) {
        return if f == F64 || w == 64 { 1u64 << (w - 1) } else { 0 };
    }
    if f.is_inf(a) {
        return enc(if f.sgn(a) { lo } else { hi });
    }
    enc(round_int(f, m, a).clamp(lo, hi))
}

/// `Fp.ofInt`.
pub fn of_int(f: Fmt, m: RMode, ftz: bool, v: i128) -> u64 {
    let q = Q { neg: v < 0, n: Big::from(v.unsigned_abs()), d: Big::from(1), e: 0 };
    f.round(m, ftz, &q, false)
}

/// `Fp.roundIntegral`.
pub fn round_integral(f: Fmt, m: RMode, ftz: bool, a: u64) -> Option<u64> {
    let a = f.flush(ftz, a);
    if f.is_nan(a) {
        return None;
    }
    if f.is_inf(a) || f.is_zero(a) {
        return Some(a);
    }
    let q = f.to_q(a);
    if q.ilog2() >= f.fb as i64 {
        return Some(a); // already an integer
    }
    let v = f.round_at(m, &q, 0);
    Some(if v == 0 { f.zero(f.sgn(a)) } else { f.encode(q.neg, v, 0) })
}

/// `Fmt.sat`.
pub fn sat_bits(f: Fmt, on: bool, r: Option<u64>) -> Option<u64> {
    f.sat(on, r)
}

/// `Fp.convertF`.
pub fn convert_f(d: Fmt, s: Fmt, m: RMode, ftz: bool, sat: bool, a: u64) -> Option<u64> {
    let a = s.flush(ftz && s == F32, a);
    let r = if s.is_nan(a) {
        None
    } else if s.is_inf(a) {
        Some(d.inf(s.sgn(a)))
    } else if s.is_zero(a) {
        Some(d.zero(s.sgn(a)))
    } else {
        Some(d.round(m, ftz && d == F32, &s.to_q(a), s.sgn(a)))
    };
    d.sat(sat, r)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn known_values() {
        assert_eq!(fadd(F32, RMode::Rn, false, false, 0x3f80_0000, 0x3f80_0000), Some(0x4000_0000));
        assert_eq!(fmul(F32, RMode::Rn, true, false, 0x3f7f_ffff, 0x0080_0000), Some(0));
        assert_eq!(fmul(F32, RMode::Rn, false, false, 0x3f7f_ffff, 0x0080_0000), Some(0x0080_0000));
        assert_eq!(ffma(F32, RMode::Rn, true, false, 0xb280_0000, 0x0080_0000, 0x0080_0000), Some(0x0080_0000));
        assert_eq!(fmul(F32, RMode::Rp, false, false, 1, 0x3f00_0000), Some(1));
        assert_eq!(fsqrt(F32, RMode::Rn, false, 0x4000_0000), Some(0x3fb5_04f3));
        assert_eq!(fdiv(F32, RMode::Rn, false, 0x3f80_0000, 0x4040_0000), Some(0x3eaa_aaab));
        assert_eq!(fmul(F32, RMode::Rz, false, false, 0x7f7f_ffff, 0x4000_0000), Some(0x7f7f_ffff));
        assert_eq!(fsqrt(F64, RMode::Rn, false, 0x4000_0000_0000_0000), Some(0x3ff6_a09e_667f_3bcd));
        assert_eq!(to_int(F32, RMode::Rz, false, true, 32, 0x7f80_0000), 0x7fff_ffff);
    }
}
