//! `e5r.ptx.spec.v1`: what a model writes next to its PTX.
//!
//! ```json
//! { "schema": "e5r.ptx.spec.v1", "kernel": "saxpy", "class": "map32",
//!   "arrays": ["saxpy_x", "saxpy_y"], "output": "saxpy_y", "length": "saxpy_n",
//!   "scalars": ["saxpy_a"], "element": "saxpy_a * saxpy_x + saxpy_y",
//!   "schedule": { "kind": "stride", "bound": "2^64",
//!     "loop": { "head": "$L_loop",
//!       "registers": { "%rd3": "index64", "%rd5": "stride64", "%rd6": "length",
//!                      "%rd1": "base saxpy_x", "%rd2": "base saxpy_y",
//!                      "%r1": "scalar saxpy_a" } } } }
//! ```
//!
//! `element` is the value of output element `i`, over the elements `i` of
//! the arrays (by parameter name) and the scalars, with 32-bit wrapping
//! `+ - * & | ^ ~`, shifts by a constant (`<<`, `>>` logical), integer
//! literals and parentheses. The schedule is `guarded` (one element per
//! thread, `max_threads` the largest `G·B` claimed) or `stride` (a
//! grid-stride loop, `bound` the largest `n + G·B` claimed, and the loop
//! invariant as register roles at the loop head).
//!
//! With `"element_type": "f32"` the arrays and scalars are `.f32` and
//! `element` is an expression of the model's float operations, written like
//! the PTX instructions: `fma.rn(saxpy_a, saxpy_x, saxpy_y)`,
//! `add.rz.ftz(x, mul.rn(a, y))`, `sqrt.rn(x)`, `min.NaN(x, y)`, `neg(x)`,
//! with `0fXXXXXXXX` literals. `"result"` is `"bit_exact"` (the default:
//! the output has the expression's bits, or is some NaN where the expression
//! is NaN, `Ptx.Fp.feq32`) or `{"max_ulps": k}` (both NaN, the same
//! infinity, or finite and at most `k` representable numbers apart,
//! `Ptx.Fp.within32 k`).

use e5r_ptx::ast::{Kernel, Ty};
use serde_json::Value;

pub const SCHEMA: &str = "e5r.ptx.spec.v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    Arr(String),
    Scal(String),
    Lit(u32),
    Not(Box<Expr>),
    Neg(Box<Expr>),
    Bin(char, Box<Expr>, Box<Expr>),
    Shl(Box<Expr>, u32),
    Shr(Box<Expr>, u32),
    /// An `.f32` literal by its bits.
    FLit(u32),
    /// A float operation of the model (`Ptx.Auto.F32.*`).
    FOp(FOp, Vec<Expr>),
}

/// `op{.rnd}{.ftz}{.sat}{.NaN}` in a float element.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FOp {
    pub op: String,
    pub rnd: Option<e5r_ptx::fp::RMode>,
    pub ftz: bool,
    pub sat: bool,
    pub nan: bool,
}

/// How an output element is compared with `element`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Result32 {
    /// Integer maps: equality.
    Eq,
    /// Float maps: the same bits, or both NaN.
    BitExact,
    /// Float maps: within this many units in the last place.
    MaxUlps(u32),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Role {
    Idx(u32),
    Stride(u32),
    Len,
    Base(String),
    Ptr(String),
    PtrStride,
    Scalar(String),
    Const(u64),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Sched {
    Guarded {
        max_threads: u128,
    },
    Stride {
        bound: u128,
        head: String,
        regs: Vec<(String, Role)>,
    },
}

#[derive(Clone, Debug)]
pub struct Spec {
    pub kernel: String,
    pub arrays: Vec<String>,
    pub output: String,
    pub length: String,
    pub scalars: Vec<String>,
    pub element: Expr,
    pub element_text: String,
    pub sched: Sched,
    /// `"element_type": "f32"`.
    pub float: bool,
    pub result: Result32,
}

/// Why a spec cannot be checked: malformed (`Error`) or outside the class
/// (`Unsupported`).
#[derive(Debug, PartialEq, Eq)]
pub enum SpecError {
    Malformed(String),
    Unsupported(String),
}

fn malformed<T>(m: impl Into<String>) -> Result<T, SpecError> {
    Err(SpecError::Malformed(m.into()))
}

fn s<'a>(v: &'a Value, k: &str) -> Result<&'a str, SpecError> {
    v.get(k)
        .and_then(Value::as_str)
        .ok_or_else(|| SpecError::Malformed(format!("spec: \"{k}\" must be a string")))
}

fn strs(v: &Value, k: &str) -> Result<Vec<String>, SpecError> {
    match v.get(k) {
        None => Ok(Vec::new()),
        Some(Value::Array(a)) => a
            .iter()
            .map(|x| {
                x.as_str()
                    .map(str::to_string)
                    .ok_or_else(|| SpecError::Malformed(format!("spec: \"{k}\" must list strings")))
            })
            .collect(),
        _ => malformed(format!("spec: \"{k}\" must be an array")),
    }
}

/// `2^k`, decimal or `0x` hex.
pub fn number(t: &str) -> Option<u128> {
    let t = t.trim();
    if let Some((b, e)) = t.split_once('^') {
        let (b, e): (u128, u32) = (b.trim().parse().ok()?, e.trim().parse().ok()?);
        return b.checked_pow(e);
    }
    if let Some(h) = t.strip_prefix("0x") {
        return u128::from_str_radix(h, 16).ok();
    }
    t.parse().ok()
}

fn num(v: &Value, k: &str) -> Result<u128, SpecError> {
    match v.get(k) {
        Some(Value::Number(n)) => n
            .as_u64()
            .map(u128::from)
            .ok_or_else(|| SpecError::Malformed(format!("spec: \"{k}\" must be a natural number"))),
        Some(Value::String(t)) => number(t)
            .ok_or_else(|| SpecError::Malformed(format!("spec: \"{k}\": cannot read {t:?}"))),
        _ => malformed(format!("spec: \"{k}\" is required")),
    }
}

fn role(t: &str) -> Result<Role, SpecError> {
    let w: Vec<&str> = t.split_whitespace().collect();
    Ok(match w.as_slice() {
        ["index64"] => Role::Idx(64),
        ["index32"] => Role::Idx(32),
        ["stride64"] => Role::Stride(64),
        ["stride32"] => Role::Stride(32),
        ["length"] => Role::Len,
        ["ptr_stride"] => Role::PtrStride,
        ["base", a] => Role::Base(a.to_string()),
        ["ptr", a] => Role::Ptr(a.to_string()),
        ["scalar", a] => Role::Scalar(a.to_string()),
        ["const", n] => Role::Const(
            number(n)
                .and_then(|v| u64::try_from(v).ok())
                .ok_or_else(|| SpecError::Malformed(format!("register role {t:?}")))?,
        ),
        _ => return malformed(format!("unknown register role {t:?}")),
    })
}

pub fn parse(text: &str) -> Result<Spec, SpecError> {
    let v: Value =
        serde_json::from_str(text).map_err(|e| SpecError::Malformed(format!("spec: {e}")))?;
    if s(&v, "schema")? != SCHEMA {
        return malformed(format!("spec: schema must be {SCHEMA}"));
    }
    let class = s(&v, "class")?;
    if class != "map32" {
        return Err(SpecError::Unsupported(format!(
            "class {class:?} (only map32 is supported)"
        )));
    }
    let arrays = strs(&v, "arrays")?;
    let scalars = strs(&v, "scalars")?;
    let element_text = s(&v, "element")?.to_string();
    let float = match v.get("element_type").and_then(Value::as_str) {
        None | Some("u32") => false,
        Some("f32") => true,
        Some(t) => {
            return Err(SpecError::Unsupported(format!(
                "element_type {t:?} (u32 or f32)"
            )));
        }
    };
    let mut parser = Parser::new(&element_text, &arrays, &scalars);
    parser.float = float;
    let element = parser
        .parse()
        .map_err(|e| SpecError::Malformed(format!("element: {e}")))?;
    let result = match (float, v.get("result")) {
        (false, None) => Result32::Eq,
        (false, Some(_)) => return malformed("spec: \"result\" is for float elements"),
        (true, None) => Result32::BitExact,
        (true, Some(Value::String(t))) if t == "bit_exact" => Result32::BitExact,
        (true, Some(r)) => match r.get("max_ulps").and_then(Value::as_u64) {
            Some(k) if k < 1 << 31 => Result32::MaxUlps(k as u32),
            _ => return malformed("spec: \"result\" is \"bit_exact\" or {\"max_ulps\": k}"),
        },
    };
    let sc = v
        .get("schedule")
        .ok_or_else(|| SpecError::Malformed("spec: \"schedule\" is required".into()))?;
    let sched = match s(sc, "kind")? {
        "guarded" => Sched::Guarded {
            max_threads: num(sc, "max_threads")?,
        },
        "stride" => {
            let lp = sc
                .get("loop")
                .ok_or_else(|| SpecError::Malformed("stride schedule needs \"loop\"".into()))?;
            let regs = match lp.get("registers") {
                Some(Value::Object(o)) => o
                    .iter()
                    .map(|(r, x)| {
                        let t = x.as_str().ok_or_else(|| {
                            SpecError::Malformed(format!("register {r}: role must be a string"))
                        })?;
                        Ok((r.clone(), role(t)?))
                    })
                    .collect::<Result<Vec<_>, _>>()?,
                _ => return malformed("loop needs \"registers\""),
            };
            Sched::Stride {
                bound: num(sc, "bound")?,
                head: s(lp, "head")?.to_string(),
                regs,
            }
        }
        k => return Err(SpecError::Unsupported(format!("schedule {k:?}"))),
    };
    Ok(Spec {
        kernel: s(&v, "kernel")?.to_string(),
        arrays,
        output: s(&v, "output")?.to_string(),
        length: s(&v, "length")?.to_string(),
        scalars,
        element,
        element_text,
        sched,
        float,
        result,
    })
}

/// Everything about the kernel the class needs, checked before any Lean
/// runs. A failure here is `unsupported`, never a guess.
pub fn validate(sp: &Spec, k: &Kernel) -> Result<(), String> {
    use e5r_ptx::ast::{Instr, Space};
    if !k.shared.is_empty() {
        return Err("map32: the kernel declares .shared memory (outside the class)".into());
    }
    if let Some(st) = k.body.iter().find(|st| {
        matches!(
            st.instr,
            Instr::Atom(..)
                | Instr::Cas(..)
                | Instr::Red(..)
                | Instr::Bar
                | Instr::Ld(Space::Shared, ..)
                | Instr::St(Space::Shared, ..)
        )
    }) {
        return Err(format!(
            "map32: {} is outside the class (no shared memory, atomics or barriers)",
            e5r_ptx::print::instr(&st.instr)
        ));
    }
    let mut names: Vec<&String> = sp.arrays.iter().chain(&sp.scalars).collect();
    names.push(&sp.length);
    let mut seen = std::collections::HashSet::new();
    for n in &names {
        if !seen.insert(*n) {
            return Err(format!("{n} is named twice in the spec"));
        }
    }
    if !sp.arrays.contains(&sp.output) {
        return Err(format!("output {} is not one of the arrays", sp.output));
    }
    for (p, t) in &k.params {
        let ok = if sp.arrays.contains(p) {
            matches!(t, Ty::U64 | Ty::S64 | Ty::B64)
        } else if *p == sp.length {
            matches!(t, Ty::U32 | Ty::S32 | Ty::B32)
        } else if sp.scalars.contains(p) {
            if sp.float {
                *t == Ty::F32
            } else {
                matches!(t, Ty::U32 | Ty::S32 | Ty::B32)
            }
        } else {
            return Err(format!("parameter {p} is not named by the spec"));
        };
        if !ok {
            return Err(format!("parameter {p} has type .{} for its role", t.name()));
        }
    }
    for n in names {
        if !k.params.iter().any(|(p, _)| p == n) {
            return Err(format!("{n} is not a parameter of {}", k.name));
        }
    }
    let backward = k.body.iter().enumerate().any(|(i, st)| match &st.instr {
        e5r_ptx::ast::Instr::Bra(_, l) => k
            .labels
            .iter()
            .find(|(m, _)| m == l)
            .is_some_and(|(_, at)| *at <= i),
        _ => false,
    });
    match &sp.sched {
        Sched::Guarded { .. } if backward => {
            Err("guarded schedule but the kernel has a backward branch (a loop)".into())
        }
        Sched::Stride { head, regs, .. } => {
            if !k.labels.iter().any(|(l, _)| l == head) {
                return Err(format!("loop head {head} is not a label"));
            }
            for (r, x) in regs {
                let declared = k.regs.iter().any(|d| match d.count {
                    Some(n) => r
                        .strip_prefix(d.name.as_str())
                        .and_then(|i| i.parse::<u32>().ok())
                        .is_some_and(|i| i < n),
                    None => *r == d.name,
                });
                if !declared {
                    return Err(format!("loop register {r} is not declared"));
                }
                if let Role::Base(a) | Role::Ptr(a) = x {
                    if !sp.arrays.contains(a) {
                        return Err(format!("register {r}: {a} is not an array"));
                    }
                }
                if let Role::Scalar(a) = x {
                    if !sp.scalars.contains(a) {
                        return Err(format!("register {r}: {a} is not a scalar"));
                    }
                }
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

struct Parser<'a> {
    t: Vec<char>,
    i: usize,
    arrays: &'a [String],
    scalars: &'a [String],
    float: bool,
}

impl<'a> Parser<'a> {
    fn new(s: &str, arrays: &'a [String], scalars: &'a [String]) -> Self {
        Parser {
            t: s.chars().collect(),
            i: 0,
            arrays,
            scalars,
            float: false,
        }
    }
    fn ws(&mut self) {
        while self.t.get(self.i).is_some_and(|c| c.is_whitespace()) {
            self.i += 1;
        }
    }
    fn eat(&mut self, p: &str) -> bool {
        self.ws();
        let n = p.chars().count();
        if self.t.len() >= self.i + n && self.t[self.i..self.i + n].iter().copied().eq(p.chars()) {
            self.i += n;
            true
        } else {
            false
        }
    }
    fn parse(mut self) -> Result<Expr, String> {
        let e = if self.float {
            self.fexpr()?
        } else {
            self.bin(0)?
        };
        self.ws();
        if self.i < self.t.len() {
            return Err(format!("unexpected {:?} at {}", self.t[self.i], self.i));
        }
        Ok(e)
    }
    /// A float element: a call `op.mods(args)`, an array or scalar, or a
    /// `0f` literal.
    fn fexpr(&mut self) -> Result<Expr, String> {
        self.ws();
        let st = self.i;
        while self
            .t
            .get(self.i)
            .is_some_and(|c| c.is_ascii_alphanumeric() || matches!(*c, '_' | '$' | '.'))
        {
            self.i += 1;
        }
        let w: String = self.t[st..self.i].iter().collect();
        if w.is_empty() {
            return Err(format!("expected an operand at {st}"));
        }
        if let Some((v, 32)) = e5r_ptx::lex::float_value(&w) {
            return Ok(Expr::FLit(v as u32));
        }
        if !self.eat("(") {
            return if self.arrays.contains(&w) {
                Ok(Expr::Arr(w))
            } else if self.scalars.contains(&w) {
                Ok(Expr::Scal(w))
            } else {
                Err(format!(
                    "{w} is neither an array, a scalar nor a 0f literal"
                ))
            };
        }
        let parts: Vec<&str> = w.split('.').collect();
        let (op, mods) = parts.split_first().unwrap();
        let arity = match *op {
            "add" | "sub" | "mul" | "div" | "min" | "max" => 2,
            "fma" => 3,
            "sqrt" | "rcp" | "neg" | "abs" => 1,
            _ => return Err(format!("unknown float operation {op}")),
        };
        let rounded = matches!(*op, "add" | "sub" | "mul" | "div" | "fma" | "sqrt" | "rcp");
        let mut f = FOp {
            op: op.to_string(),
            rnd: None,
            ftz: false,
            sat: false,
            nan: false,
        };
        for m in mods {
            match *m {
                "rn" | "rz" | "rm" | "rp" if rounded && f.rnd.is_none() => {
                    f.rnd = e5r_ptx::ast::RMode::from_name(m)
                }
                "ftz" if !f.ftz => f.ftz = true,
                "sat" if matches!(*op, "add" | "sub" | "mul" | "fma") && !f.sat => f.sat = true,
                "NaN" if matches!(*op, "min" | "max") && !f.nan => f.nan = true,
                _ => return Err(format!("modifier .{m} on {op}")),
            }
        }
        if rounded && f.rnd.is_none() {
            return Err(format!("{op} needs a rounding modifier"));
        }
        let mut args = vec![self.fexpr()?];
        while args.len() < arity {
            if !self.eat(",") {
                return Err(format!("{op} takes {arity} operands"));
            }
            args.push(self.fexpr()?);
        }
        if !self.eat(")") {
            return Err(format!("missing ) after {op}"));
        }
        Ok(Expr::FOp(f, args))
    }

    // precedence, loosest first: | ^ & (<< >>) (+ -) *
    fn bin(&mut self, lvl: usize) -> Result<Expr, String> {
        const OPS: [&[&str]; 5] = [&["|"], &["^"], &["&"], &["+", "-"], &["*"]];
        if lvl == 5 {
            return self.shift();
        }
        let mut l = self.bin(lvl + 1)?;
        'outer: loop {
            for op in OPS[lvl] {
                if self.eat(op) {
                    let r = self.bin(lvl + 1)?;
                    l = Expr::Bin(op.chars().next().unwrap(), Box::new(l), Box::new(r));
                    continue 'outer;
                }
            }
            return Ok(l);
        }
    }
    fn shift(&mut self) -> Result<Expr, String> {
        let mut l = self.unary()?;
        loop {
            let left = if self.eat("<<") {
                true
            } else if self.eat(">>") {
                false
            } else {
                return Ok(l);
            };
            self.ws();
            let k = match self.unary()? {
                Expr::Lit(k) if k < 32 => k,
                _ => return Err("shift amounts must be literals below 32".into()),
            };
            l = if left {
                Expr::Shl(Box::new(l), k)
            } else {
                Expr::Shr(Box::new(l), k)
            };
        }
    }
    fn unary(&mut self) -> Result<Expr, String> {
        if self.eat("~") {
            return Ok(Expr::Not(Box::new(self.unary()?)));
        }
        if self.eat("-") {
            return Ok(Expr::Neg(Box::new(self.unary()?)));
        }
        if self.eat("(") {
            let e = self.bin(0)?;
            if !self.eat(")") {
                return Err("missing )".into());
            }
            return Ok(e);
        }
        self.ws();
        let st = self.i;
        while self
            .t
            .get(self.i)
            .is_some_and(|c| c.is_ascii_alphanumeric() || *c == '_' || *c == '$')
        {
            self.i += 1;
        }
        let w: String = self.t[st..self.i].iter().collect();
        if w.is_empty() {
            return Err(format!("expected an operand at {st}"));
        }
        if w.starts_with(|c: char| c.is_ascii_digit()) {
            let v = number(&w).ok_or(format!("bad literal {w}"))?;
            return u32::try_from(v)
                .map(Expr::Lit)
                .map_err(|_| format!("{w} does not fit 32 bits"));
        }
        if self.arrays.contains(&w) {
            Ok(Expr::Arr(w))
        } else if self.scalars.contains(&w) {
            Ok(Expr::Scal(w))
        } else {
            Err(format!("{w} is neither an array nor a scalar"))
        }
    }
}

impl Spec {
    /// The Lean relation of `MapSpec.rel`.
    pub fn rel_lean(&self) -> String {
        match self.result {
            Result32::Eq => "(fun a b => a = b)".into(),
            Result32::BitExact => "Ptx.Fp.feq32".into(),
            Result32::MaxUlps(k) => format!("(Ptx.Fp.within32 {k})"),
        }
    }

    /// Whether output word `got` meets the spec's value `want`.
    pub fn accepts(&self, got: u32, want: u32) -> bool {
        let f = e5r_ptx::fp::F32;
        let nan = |x: u32| f.is_nan(x as u64);
        match self.result {
            Result32::Eq => got == want,
            Result32::BitExact => got == want || (nan(got) && nan(want)),
            Result32::MaxUlps(k) => {
                let inf = |x: u32| x & 0x7fff_ffff == 0x7f80_0000;
                let ord = |x: u32| -> i64 {
                    if x & 0x8000_0000 != 0 {
                        -((x & 0x7fff_ffff) as i64)
                    } else {
                        x as i64
                    }
                };
                (nan(got) && nan(want))
                    || (inf(got) && got == want)
                    || (!nan(got)
                        && !inf(got)
                        && !nan(want)
                        && !inf(want)
                        && (ord(got) - ord(want)).unsigned_abs() <= k as u64)
            }
        }
    }
}

impl Expr {
    /// The value, for the counterexample search.
    pub fn eval(&self, arr: &dyn Fn(&str) -> u32, sc: &dyn Fn(&str) -> u32) -> u32 {
        match self {
            Expr::Arr(a) => arr(a),
            Expr::Scal(a) => sc(a),
            Expr::Lit(v) => *v,
            Expr::Not(e) => !e.eval(arr, sc),
            Expr::Neg(e) => e.eval(arr, sc).wrapping_neg(),
            Expr::Shl(e, k) => e.eval(arr, sc) << k,
            Expr::Shr(e, k) => e.eval(arr, sc) >> k,
            Expr::FLit(v) => *v,
            Expr::FOp(f, args) => {
                use e5r_ptx::fp;
                let v: Vec<u64> = args.iter().map(|a| a.eval(arr, sc) as u64).collect();
                let (m, ff) = (f.rnd.unwrap_or(fp::RMode::Rn), fp::F32);
                let r = match f.op.as_str() {
                    "add" => fp::fadd(ff, m, f.ftz, f.sat, v[0], v[1]),
                    "sub" => fp::fsub(ff, m, f.ftz, f.sat, v[0], v[1]),
                    "mul" => fp::fmul(ff, m, f.ftz, f.sat, v[0], v[1]),
                    "div" => fp::fdiv(ff, m, f.ftz, v[0], v[1]),
                    "fma" => fp::ffma(ff, m, f.ftz, f.sat, v[0], v[1], v[2]),
                    "sqrt" => fp::fsqrt(ff, m, f.ftz, v[0]),
                    "rcp" => fp::frcp(ff, m, f.ftz, v[0]),
                    "neg" => fp::fneg(ff, f.ftz, v[0]),
                    "abs" => fp::fabs(ff, f.ftz, v[0]),
                    "min" => fp::fminmax(ff, false, f.ftz, f.nan, v[0], v[1]),
                    _ => fp::fminmax(ff, true, f.ftz, f.nan, v[0], v[1]),
                };
                r.unwrap_or(ff.qnan()) as u32
            }
            Expr::Bin(o, a, b) => {
                let (x, y) = (a.eval(arr, sc), b.eval(arr, sc));
                match o {
                    '+' => x.wrapping_add(y),
                    '-' => x.wrapping_sub(y),
                    '*' => x.wrapping_mul(y),
                    '&' => x & y,
                    '|' => x | y,
                    _ => x ^ y,
                }
            }
        }
    }

    /// The Lean term, with `s` the scalars and `e` the elements.
    pub fn lean(&self) -> String {
        let q = |n: &str| serde_json::to_string(n).unwrap();
        match self {
            Expr::Arr(a) => format!("e {}", q(a)),
            Expr::Scal(a) => format!("s {}", q(a)),
            Expr::Lit(v) | Expr::FLit(v) => format!("({v}#32)"),
            Expr::FOp(f, args) => {
                let a: Vec<String> = args.iter().map(|x| format!("({})", x.lean())).collect();
                let m = f.rnd.map(|r| format!(" .{}", r.name())).unwrap_or_default();
                match f.op.as_str() {
                    "add" | "sub" | "mul" | "fma" => {
                        format!("(F32.{}{m} {} {} {})", f.op, f.ftz, f.sat, a.join(" "))
                    }
                    "div" | "sqrt" | "rcp" => {
                        format!("(F32.{}{m} {} {})", f.op, f.ftz, a.join(" "))
                    }
                    "neg" | "abs" => format!("(F32.{} {} {})", f.op, f.ftz, a.join(" ")),
                    op => format!(
                        "(F32.minmax {} {} {} {})",
                        op == "max",
                        f.ftz,
                        f.nan,
                        a.join(" ")
                    ),
                }
            }
            Expr::Not(e) => format!("(~~~({}))", e.lean()),
            Expr::Neg(e) => format!("(-({}))", e.lean()),
            Expr::Shl(e, k) => format!("(({}) <<< ({k} : Nat))", e.lean()),
            Expr::Shr(e, k) => format!("(({}) >>> ({k} : Nat))", e.lean()),
            Expr::Bin(o, a, b) => {
                let op = match o {
                    '+' => "+",
                    '-' => "-",
                    '*' => "*",
                    '&' => "&&&",
                    '|' => "|||",
                    _ => "^^^",
                };
                format!("(({}) {op} ({}))", a.lean(), b.lean())
            }
        }
    }
}
