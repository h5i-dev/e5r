//! The block classes of `e5r.ptx.spec.v1`: `reduce32` and `scan32`
//! (docs/verification/ptx.md, "M4 classes").
//!
//! ```json
//! { "schema": "e5r.ptx.spec.v1", "kernel": "reduce", "class": "reduce32",
//!   "result": "per_block",
//!   "input": "reduce_param_0", "output": "reduce_param_1", "length": "reduce_param_2",
//!   "shared": "_ZZ6reduceE1s", "max_block": 1024,
//!   "barriers": {
//!     "after_load": { "%r1": "ntid", "%r2": "ctaid", "%r3": "tid",
//!                     "%r7": "shared_tid", "%rd2": "output" },
//!     "loop": { "%r22": "stride", "%r2": "ctaid", "%r3": "tid",
//!               "%r7": "shared_tid", "%rd2": "output" } } }
//! ```
//!
//! The class fixes the algorithm (Ptx/Auto/Reduce32.lean, Ptx/Auto/Scan32.lean)
//! and the theorem; the spec names the parameters and the shared array, bounds
//! the block size, and says what the registers hold right after each barrier.
//! `reduce32` has two `bar.sync` (after the load, in the loop) and `result`
//! `per_block` (thread 0 stores `out[ctaid]`) or `atomic` (thread 0 adds to
//! `*out`); `scan32` has three (after the load, after a round's read, after
//! its add). The roles are claims the proof must establish, not assumptions:
//! a wrong role makes the proof fail, never the theorem false.

use super::spec::SpecError;
use e5r_ptx::ast::{Instr, Kernel, Ty};
use serde_json::Value;
use std::fmt::Write;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Class {
    /// `reduce32`, `result: per_block`.
    Reduce,
    /// `reduce32`, `result: atomic`.
    ReduceAtomic,
    /// `scan32`.
    Scan,
}

impl Class {
    pub fn name(self) -> &'static str {
        match self {
            Class::Reduce | Class::ReduceAtomic => "reduce32",
            Class::Scan => "scan32",
        }
    }
    /// The barrier sets the spec must describe, in program order.
    pub fn barriers(self) -> &'static [&'static str] {
        match self {
            Class::Reduce | Class::ReduceAtomic => &["after_load", "loop"],
            Class::Scan => &["after_load", "after_read", "after_add"],
        }
    }
    /// The Lean definition the theorem is stated with.
    pub fn definition(self) -> &'static str {
        match self {
            Class::Reduce => "Ptx.Auto.Reduce32.Correct",
            Class::ReduceAtomic => "Ptx.Auto.Reduce32.Atomic.Correct",
            Class::Scan => "Ptx.Auto.Scan32.Correct",
        }
    }
}

/// What a register holds right after a barrier.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Role {
    Ntid,
    Ctaid,
    Tid,
    Gid,
    SharedTid,
    SharedBase,
    Input,
    Output,
    Length,
    /// `reduce32`, `loop`: the stride of the phase that just ended.
    Stride,
    /// `reduce32`, `loop`: the stride of the phase before it (twice the
    /// stride; the block size after the first tree phase).
    StridePrev,
    /// `scan32`, `after_read` / `after_add`: the round's offset `2^k`.
    Offset,
    /// `scan32`, `after_read`: the value the thread read in the round.
    Read,
    /// A predicate: `gid >= length`.
    GidGeLen,
    /// A predicate: `gid < length`.
    GidLtLen,
    /// `scan32`, `after_read`: a predicate, `tid < offset`.
    TidLtOffset,
}

impl Role {
    fn parse(t: &str) -> Option<Role> {
        Some(match t.trim() {
            "ntid" => Role::Ntid,
            "ctaid" => Role::Ctaid,
            "tid" => Role::Tid,
            "gid" => Role::Gid,
            "shared_tid" => Role::SharedTid,
            "shared_base" => Role::SharedBase,
            "input" => Role::Input,
            "output" => Role::Output,
            "length" => Role::Length,
            "stride" => Role::Stride,
            "stride_prev" => Role::StridePrev,
            "offset" => Role::Offset,
            "read" => Role::Read,
            "gid >= length" => Role::GidGeLen,
            "gid < length" => Role::GidLtLen,
            "tid < offset" => Role::TidLtOffset,
            _ => return None,
        })
    }
    fn is_pred(self) -> bool {
        matches!(self, Role::GidGeLen | Role::GidLtLen | Role::TidLtOffset)
    }
    /// The barrier sets the role may appear in.
    fn allowed(self, class: Class, set: &str) -> bool {
        match self {
            Role::Stride | Role::StridePrev => {
                matches!(class, Class::Reduce | Class::ReduceAtomic) && set == "loop"
            }
            Role::Offset => class == Class::Scan && set != "after_load",
            Role::Read | Role::TidLtOffset => class == Class::Scan && set == "after_read",
            _ => true,
        }
    }
}

#[derive(Clone, Debug)]
pub struct BlockSpec {
    pub kernel: String,
    pub class: Class,
    pub input: String,
    pub output: String,
    pub length: String,
    pub shared: String,
    pub max_block: u32,
    pub barriers: Vec<(String, Vec<(String, Role)>)>,
}

fn malformed<T>(m: impl Into<String>) -> Result<T, SpecError> {
    Err(SpecError::Malformed(m.into()))
}

fn s<'a>(v: &'a Value, k: &str) -> Result<&'a str, SpecError> {
    v.get(k)
        .and_then(Value::as_str)
        .ok_or_else(|| SpecError::Malformed(format!("spec: \"{k}\" must be a string")))
}

/// Parse a `reduce32` or `scan32` spec (the schema and class already read).
pub fn parse(v: &Value, class: &str) -> Result<BlockSpec, SpecError> {
    let class = match (class, v.get("result").and_then(Value::as_str)) {
        ("reduce32", Some("per_block")) => Class::Reduce,
        ("reduce32", Some("atomic")) => Class::ReduceAtomic,
        ("reduce32", Some(r)) => {
            return Err(SpecError::Unsupported(format!(
                "reduce32 result {r:?} (per_block or atomic)"
            )));
        }
        ("reduce32", None) => return malformed("reduce32 needs \"result\""),
        ("scan32", _) => Class::Scan,
        (c, _) => return Err(SpecError::Unsupported(format!("class {c:?}"))),
    };
    let max_block = match v.get("max_block") {
        Some(Value::Number(n)) => n
            .as_u64()
            .and_then(|x| u32::try_from(x).ok())
            .ok_or_else(|| SpecError::Malformed("max_block must be a natural number".into()))?,
        _ => return malformed("spec: \"max_block\" is required"),
    };
    if !(1..=1024).contains(&max_block) || !max_block.is_power_of_two() {
        return Err(SpecError::Unsupported(format!(
            "max_block {max_block} (a power of two from 1 to 1024)"
        )));
    }
    let bs = match v.get("barriers") {
        Some(Value::Object(o)) => o,
        _ => return malformed("spec: \"barriers\" must be an object"),
    };
    let mut barriers = Vec::new();
    for want in class.barriers() {
        let Some(Value::Object(regs)) = bs.get(*want) else {
            return malformed(format!("barriers: \"{want}\" must be an object"));
        };
        let mut roles = Vec::new();
        for (r, x) in regs {
            let t = x.as_str().ok_or_else(|| {
                SpecError::Malformed(format!("{want} {r}: role must be a string"))
            })?;
            let role = Role::parse(t)
                .ok_or_else(|| SpecError::Malformed(format!("{want} {r}: unknown role {t:?}")))?;
            if !role.allowed(class, want) {
                return malformed(format!("{want} {r}: role {t:?} is not allowed here"));
            }
            roles.push((r.clone(), role));
        }
        barriers.push((want.to_string(), roles));
    }
    if let Some(extra) = bs.keys().find(|k| !class.barriers().contains(&k.as_str())) {
        return malformed(format!("barriers: unknown set {extra:?}"));
    }
    Ok(BlockSpec {
        kernel: s(v, "kernel")?.to_string(),
        class,
        input: s(v, "input")?.to_string(),
        output: s(v, "output")?.to_string(),
        length: s(v, "length")?.to_string(),
        shared: s(v, "shared")?.to_string(),
        max_block,
        barriers,
    })
}

/// What the generated proof needs from the kernel.
#[derive(Clone, Debug)]
pub struct Shape {
    /// The `bar.sync` statements, in program order.
    pub bars: Vec<usize>,
    /// The shared array's size in words and its alignment.
    pub words: u64,
    pub align: u32,
}

/// Names the generated file defines next to the kernel.
const RESERVED: [&str; 10] = [
    "spec",
    "code",
    "fit",
    "phaseT",
    "T_last",
    "T_odd",
    "T_even",
    "obligations",
    "correct",
    "lo32_ofInt_zero",
];

fn declared(k: &Kernel, r: &str) -> Option<Ty> {
    k.regs.iter().find_map(|d| {
        let ok = match d.count {
            Some(n) => r
                .strip_prefix(d.name.as_str())
                .and_then(|i| i.parse::<u32>().ok())
                .is_some_and(|i| i < n),
            None => r == d.name,
        };
        ok.then_some(d.ty)
    })
}

/// What the theorem statement needs from the kernel, checked before any
/// Lean runs. A failure here is `unsupported`, never a guess.
pub fn validate(sp: &BlockSpec, k: &Kernel) -> Result<(), String> {
    let c = sp.class.name();
    if RESERVED.contains(&k.name.as_str()) {
        return Err(format!(
            "{c}: kernel name {} is reserved by the proof file",
            k.name
        ));
    }
    let names = [&sp.input, &sp.output, &sp.length];
    if names[0] == names[1] || names[0] == names[2] || names[1] == names[2] {
        return Err("input, output and length must be different parameters".into());
    }
    if k.params.len() != 3 {
        return Err(format!(
            "{c}: the kernel has {} parameters (input, output, length)",
            k.params.len()
        ));
    }
    for (p, t) in &k.params {
        let ok = if *p == sp.input || *p == sp.output {
            matches!(t, Ty::U64 | Ty::S64 | Ty::B64)
        } else if *p == sp.length {
            matches!(t, Ty::U32 | Ty::S32 | Ty::B32)
        } else {
            return Err(format!("parameter {p} is not named by the spec"));
        };
        if !ok {
            return Err(format!("parameter {p} has type .{} for its role", t.name()));
        }
    }
    Ok(())
}

/// Whether the kernel has the shape the class's proof handles: the shared
/// array, the number of `bar.sync`, and registers for the roles. A failure
/// here leaves the counterexample search, which needs only the statement.
pub fn shape(sp: &BlockSpec, k: &Kernel) -> Result<Shape, String> {
    let c = sp.class.name();
    let Some(d) = k.shared.iter().find(|d| d.name == sp.shared) else {
        return Err(format!("{c}: no .shared variable {}", sp.shared));
    };
    let (size, align) = (d.size(), d.alignment());
    if size % 4 != 0 || align % 4 != 0 || align == 0 {
        return Err(format!(
            "{c}: .shared {} must be whole 32-bit words, 4-aligned (size {size}, align {align})",
            sp.shared
        ));
    }
    if size / 4 < sp.max_block as u64 {
        return Err(format!(
            "{c}: .shared {} has {} words, fewer than max_block {}",
            sp.shared,
            size / 4,
            sp.max_block
        ));
    }
    let bars: Vec<usize> = k
        .body
        .iter()
        .enumerate()
        .filter(|(_, st)| matches!(st.instr, Instr::Bar))
        .map(|(i, _)| i)
        .collect();
    let want = sp.class.barriers().len();
    if bars.len() != want {
        return Err(format!(
            "{c}: the kernel has {} bar.sync, the class has {want}",
            bars.len()
        ));
    }
    if k.body
        .iter()
        .any(|st| st.guard.is_some() && matches!(st.instr, Instr::Bar))
    {
        return Err(format!("{c}: a predicated bar.sync"));
    }
    for (set, roles) in &sp.barriers {
        for (r, role) in roles {
            let Some(ty) = declared(k, r) else {
                return Err(format!("{set}: register {r} is not declared"));
            };
            if (ty == Ty::Pred) != role.is_pred() {
                return Err(format!(
                    "{set}: register {r} has type .{} for its role",
                    ty.name()
                ));
            }
        }
    }
    Ok(Shape {
        bars,
        words: size / 4,
        align,
    })
}

fn q(s: &str) -> String {
    serde_json::to_string(s).unwrap()
}

/// The hypothesis name for a register.
fn hyp(r: &str) -> String {
    let t: String = r
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect();
    format!("hR_{}", t.trim_start_matches('_'))
}

const GID: &str = "t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat";

/// `reg = value` for one role; `r`/`p` are how the state's registers and
/// predicates are written, `k` the round or phase expression.
fn role_eq(r: &str, p: &str, reg: &str, role: Role, k: &str) -> String {
    let v = match role {
        Role::Ntid => "ext32 A.B".to_string(),
        Role::Ctaid => "ext32 t.ctaid.x".into(),
        Role::Tid => "ext32 t.tid.x".into(),
        Role::Gid => format!("ext32 (BitVec.ofNat 32 ({GID}))"),
        Role::SharedTid => "ext32 (BitVec.ofNat 32 (A.sb.toNat + 4 * t.tid.x.toNat))".into(),
        Role::SharedBase => "ext32 (BitVec.ofNat 32 A.sb.toNat)".into(),
        Role::Input => "A.x".into(),
        Role::Output => "A.out".into(),
        Role::Length => "ext32 A.n".into(),
        Role::Stride => format!("ext32 (BitVec.ofNat 32 (stride A {k}))"),
        Role::StridePrev => {
            let p = if k == "(k + 1)" {
                "k".to_string()
            } else {
                format!("({k} - 1)")
            };
            format!("ext32 (BitVec.ofNat 32 (stride A {p}))")
        }
        Role::Offset => format!("ext32 (BitVec.ofNat 32 (2 ^ {k}))"),
        Role::Read => format!("ext32 (rv A m₀ t.ctaid.x.toNat {k} t.tid.x.toNat)"),
        Role::GidGeLen => format!("decide (A.n.toNat ≤ {GID})"),
        Role::GidLtLen => format!("decide ({GID} < A.n.toNat)"),
        Role::TidLtOffset => format!("decide (t.tid.x.toNat < 2 ^ {k})"),
    };
    if role.is_pred() {
        format!("{p} {} = {v}", q(reg))
    } else {
        format!("{r} {} = {v}", q(reg))
    }
}

fn conj(roles: &[(String, Role)], r: &str, p: &str, k: &str) -> String {
    if roles.is_empty() {
        return "True".into();
    }
    roles
        .iter()
        .map(|(reg, role)| role_eq(r, p, reg, *role, k))
        .collect::<Vec<_>>()
        .join(" ∧\n      ")
}

fn pat(roles: &[(String, Role)]) -> String {
    if roles.is_empty() {
        return "-".into();
    }
    roles
        .iter()
        .map(|(r, _)| hyp(r))
        .collect::<Vec<_>>()
        .join(", ")
}

fn hyps(roles: &[(String, Role)]) -> String {
    roles.iter().map(|(r, _)| format!(", {}", hyp(r))).collect()
}

const REDUCE: &str = include_str!("templates/reduce32.lean");
const SCAN: &str = include_str!("templates/scan32.lean");

const TREE_ALTS: &str = "      all_goals (try and_intros)
      all_goals first
        | trivial@EXTRA_ALTS@
        | (exfalso; omega)
        | exact accessOk_elem_mem (N := @W@) (by simp) fsb sal (by omega)
        | exact fun y hy => ⟨trivial, by omega, hy⟩
        | exact fun y hy => .inl ⟨trivial, by omega, hy⟩
        | exact fun y hy => .inr ⟨trivial, by omega, hy⟩
        | exact fun y hy => ⟨rfl, by omega, hy⟩
        | exact fun y hy => .inl ⟨rfl, by omega, hy⟩
        | exact fun y hy => .inr ⟨rfl, by omega, hy⟩
        | (rintro ⟨sp, y⟩ ⟨-, hlt, -⟩; exfalso; omega)
        | (rintro ⟨sp, y⟩ ⟨hsp, hlt, hy⟩
           try simp only at hsp
           subst hsp
           refine wr_cells fsbB hi hy ?_
           simp only [lo32_ext32, lo32_rd_b4, hmin, hmin1]
           rw [rd32_cells fsbB hi, rd32_cells fsbB (by omega)]
           simp only [Reduce32.V, hlt, ↓reduceIte]
           try exact BitVec.add_comm _ _)
        | (simp (config := { failIfUnchanged := false }) only [code, phaseT, upd, String.reduceEq,
             ↓reduceIte, true_and, and_true]
           all_goals (try and_intros)
           all_goals ptx_reg4)
      done";

const LAST_ALTS: &str = "      all_goals (try and_intros)
      all_goals first
        | trivial@EXTRA_ALTS@
        | (exfalso; omega)
        | exact accessOk_elem_mem (N := @W@) (by simp) fsb sal (by omega)
        | exact accessOk_elem_mem (N := A.G.toNat) (by simp) fout oal (by omega)
        | exact fun y hy => ⟨trivial, by omega, hy⟩
        | exact fun y hy => .inl ⟨trivial, by omega, hy⟩
        | exact fun y hy => .inl ⟨rfl, by omega, hy⟩
        | (rintro ⟨sp, y⟩ ⟨-, h0, -⟩; exfalso; omega)
        | (rintro ⟨sp, y⟩ ⟨hsp, h0, hy⟩
           try simp only at hsp
           subst hsp
           refine wr_lo32 ?_ hy
           simp only [lo32_ext32, lo32_rd_b4]
           rw [rd32_cells fsbB (by omega)])
      done";

const LAST_ALTS_ATOMIC: &str = "      all_goals (try and_intros)
      all_goals first
        | trivial@EXTRA_ALTS@
        | (exfalso; omega)
        | exact accessOk_elem_mem (N := @W@) (by simp) fsb sal (by omega)
        | exact accessOk_elem_mem (N := 1) (by simp) fout oal (by omega)
        | exact elem_zero _
        | (refine ⟨_, addsTo_add _, fun v => ⟨?_, fun _ h => h.elim, trivial⟩⟩
           funext a
           simp only [Ghost.acc, add32_op, lo32_rd_b4, lo32_ext32, lo32_zero, BitVec.zero_add, elem_zero A.out]
           rw [rd32_cells fsbB (by omega)]
           by_cases ha : a = A.out
           · subst ha; simp [show t.tid.x.toNat = 0 by omega]
           · simp [ha])
        | exact fun y hy => ⟨trivial, by omega, hy⟩
        | exact fun y hy => .inl ⟨trivial, by omega, hy⟩
        | exact fun y hy => .inl ⟨rfl, by omega, hy⟩
        | (rintro ⟨sp, y⟩ ⟨-, h0, -⟩; exfalso; omega)
      done";

/// The atomic class's ghost and cell goals.
const ATOMIC_EXTRA: &str = "
        | (intro _ h; exact h.elim)
        | (funext a; split
           · next h => first | exact absurd h.1 (by omega) | exact absurd h.2.1 (by omega)
           · rfl)";

const READ_ALTS: &str = "      all_goals (try and_intros)
      all_goals first
        | trivial
        | (exfalso; omega)
        | (intro _ h; exact h.elim)
        | exact accessOk_elem_mem (N := @W@) (by simp) fsb sal (by omega)
        | exact fun y hy => .inl ⟨trivial, by omega, hy⟩
        | exact fun y hy => .inl ⟨rfl, by omega, hy⟩
        | (simp (config := { failIfUnchanged := false }) only [code, Code.Tc, phaseT, upd,
             String.reduceEq, ↓reduceIte, true_and, and_true, show 2 * i + 1 + 1 ≠ 1 by omega,
             show (2 * i + 1 + 1) % 2 = 0 by omega, show (2 * i + 1 + 1) / 2 - 1 = i by omega]
           all_goals (try and_intros)
           all_goals first
             | ptx_reg4
             | rfl
             | assumption
             | (simp only [Ptx.Auto.ult_toNat, Ptx.Auto.ule_toNat, decide_eq_decide]; ptx_nat4)
             | (rw [rd_b4, rd32_cells fsbB (by omega)]
                simp only [Scan32.rv, show 2 ^ i ≤ t.tid.x.toNat by omega, ↓reduceIte])
             | (simp only [Scan32.rv, lo32_ofInt_zero, show ¬ 2 ^ i ≤ t.tid.x.toNat by omega, ↓reduceIte]
                first | done | rfl))
      done";

const STORE_ALTS: &str = "      all_goals (try and_intros)
      all_goals first
        | trivial
        | (exfalso; omega)
        | exact accessOk_elem_mem (N := @W@) (by simp) fsb sal (by omega)
        | exact accessOk_elem_mem (N := A.n.toNat) (by simp) fout oal (by omega)
        | exact fun y hy => .inl ⟨trivial, by omega, hy⟩
        | exact fun y hy => .inl ⟨rfl, by omega, hy⟩
        | exact fun y hy => ⟨trivial, by omega, hy⟩
        | exact fun y hy => ⟨rfl, by omega, hy⟩
        | (rintro ⟨sp, y⟩ ⟨-, hlt, -⟩; exfalso; omega)
        | (rintro ⟨sp, y⟩ ⟨hsp, hlt, hy⟩
           try simp only at hsp
           subst hsp
           show _ = cells _ _ _ m₀ y
           rw [← elem_elem] at hy ⊢
           refine wr_cells (fits_tail fout (c := t.ctaid.x.toNat * A.B.toNat) (M := _) (by omega))
             (by omega) hy ?_
           simp only [lo32_ext32, lo32_rd_b4]
           rw [rd32_cells fsbB hi])
      done";

pub fn spec_text(sp: &BlockSpec) -> String {
    let j = sp.max_block.trailing_zeros();
    let mut s = String::new();
    writeln!(
        s,
        "def spec : Block.Spec where\n  input := {}\n  output := {}\n  length := {}\n  shared := {}\n  maxJ := {j}\n",
        q(&sp.input),
        q(&sp.output),
        q(&sp.length),
        q(&sp.shared)
    )
    .unwrap();
    for (n, v) in [
        ("input", q(&sp.input)),
        ("output", q(&sp.output)),
        ("length", q(&sp.length)),
        ("shared", q(&sp.shared)),
        ("maxJ", j.to_string()),
    ] {
        writeln!(s, "@[simp] theorem spec_{n} : spec.{n} = {v} := rfl").unwrap();
    }
    s
}

/// The Lean `spec` definition, for the result document.
pub fn lean_spec(sp: &BlockSpec) -> String {
    let t = spec_text(sp);
    t[..t.find("\n\n").unwrap_or(t.len())].to_string()
}

/// The proof attempt: `theorem E5rCheck.correct : <class>.Correct spec K`.
pub fn proof(k: &Kernel, sp: &BlockSpec, sh: &Shape, header: &str) -> String {
    let kn = format!("«{}»", k.name);
    let roles =
        |n: &str| -> &[(String, Role)] { &sp.barriers.iter().find(|(m, _)| m == n).unwrap().1 };
    let common = [
        ("@HEADER@", header.trim_end().to_string()),
        ("@KERNEL_DEF@", e5r_ptx::lean::kernel_def(k)),
        ("@SPEC_DEF@", spec_text(sp)),
        ("@N@", (k.body.len() + 2).to_string()),
        ("@ALIGN@", sh.align.to_string()),
        ("@SHNAME@", q(&sp.shared)),
    ];
    let mut t = match sp.class {
        Class::Reduce | Class::ReduceAtomic => {
            let atomic = sp.class == Class::ReduceAtomic;
            let mp = if atomic {
                "Reduce32.Atomic."
            } else {
                "Reduce32."
            };
            let (l, p) = (roles("after_load"), roles("loop"));
            let eval = format!(
                "ptx_eval, {kn}, Block.Args.launch, Block.Args.params, spec_input, spec_output,\n        \
                 spec_length, {mp}mem, Phased.J, {mp}phased, code, Code.Tc, phaseT, List.map_cons,\n        \
                 List.map_nil"
            );
            let last = if atomic { LAST_ALTS_ATOMIC } else { LAST_ALTS };
            let mut t = REDUCE
                .replace("@TREE_ALTS@", TREE_ALTS)
                .replace("@LAST_ALTS@", last)
                .replace("@EXTRA_ALTS@", if atomic { ATOMIC_EXTRA } else { "" })
                .replace("@NS@", mp)
                .replace("@EVAL@", &eval);
            for (a, b) in [
                ("@PC1@", (sh.bars[0] + 1).to_string()),
                ("@PCL@", (sh.bars[1] + 1).to_string()),
                ("@BPC0@", sh.bars[0].to_string()),
                ("@BPCL@", sh.bars[1].to_string()),
                ("@T1@", conj(l, "s.r", "s.p", "")),
                ("@TL@", conj(p, "s.r", "s.p", "(k + 1)")),
                ("@LAST1@", conj(l, "r", "p", "")),
                ("@LASTL@", conj(p, "r", "p", "A.j")),
                ("@PAT1@", pat(l)),
                ("@PATL@", pat(p)),
                ("@HYP1@", hyps(l)),
                ("@HYPL@", hyps(p)),
            ] {
                t = t.replace(a, &b);
            }
            t
        }
        Class::Scan => {
            let (l, r, a) = (roles("after_load"), roles("after_read"), roles("after_add"));
            let eval = format!(
                "ptx_eval, {kn}, Block.Args.launch, Block.Args.params, spec_input, spec_output,\n        \
                 spec_length, Scan32.mem, Phased.J, Scan32.phased, code, List.map_cons, List.map_nil"
            );
            let mut t = SCAN
                .replace("@READ_ALTS@", READ_ALTS)
                .replace("@STORE_ALTS@", STORE_ALTS)
                .replace("@EVAL@", &eval);
            for (x, y) in [
                ("@PC1@", (sh.bars[0] + 1).to_string()),
                ("@PCR@", (sh.bars[1] + 1).to_string()),
                ("@PCA@", (sh.bars[2] + 1).to_string()),
                ("@BPC0@", sh.bars[0].to_string()),
                ("@BPCR@", sh.bars[1].to_string()),
                ("@BPCA@", sh.bars[2].to_string()),
                ("@T1@", conj(l, "s.r", "s.p", "")),
                ("@TR@", conj(r, "s.r", "s.p", "(p / 2 - 1)")),
                ("@TA@", conj(a, "s.r", "s.p", "(p / 2 - 1)")),
                ("@LAST1@", conj(l, "r", "p", "")),
                ("@LASTR@", conj(r, "r", "p", "i")),
                ("@LASTA@", conj(a, "r", "p", "(i - 1)")),
                ("@PAT1@", pat(l)),
                ("@PATR@", pat(r)),
                ("@PATA@", pat(a)),
                ("@HYP1@", hyps(l)),
                ("@HYPR@", hyps(r)),
                ("@HYPA@", hyps(a)),
            ] {
                t = t.replace(x, &y);
            }
            t
        }
    };
    for (a, b) in common {
        t = t.replace(a, &b);
    }
    t = t.replace("@K@", &kn).replace("@W@", &sh.words.to_string());
    t
}

/// Kernel and spec in namespace `E5rSpec`, for the supplied-proof route.
pub fn statement_prelude(k: &Kernel, sp: &BlockSpec, header: &str) -> String {
    let import = match sp.class {
        Class::Scan => "Ptx.Auto.Scan32",
        _ => "Ptx.Auto.Reduce32",
    };
    format!(
        "/-\n{}\n-/\nimport {import}\n\nnamespace E5rSpec\nopen Ptx Ptx.Auto Ptx.Auto.Block\n\n{}{}",
        header.trim_end(),
        e5r_ptx::lean::kernel_def(k),
        spec_text(sp)
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hypothesis_names_are_identifiers() {
        assert_eq!(hyp("%r22"), "hR_r22");
        assert_eq!(hyp("%rd2"), "hR_rd2");
        assert_eq!(hyp("%p1"), "hR_p1");
    }

    #[test]
    fn roles_are_checked_per_barrier() {
        let v: Value = serde_json::from_str(
            r#"{"kernel":"k","result":"per_block","input":"a","output":"b","length":"n",
                "shared":"s","max_block":256,
                "barriers":{"after_load":{"%r1":"stride"},"loop":{}}}"#,
        )
        .unwrap();
        assert!(matches!(
            parse(&v, "reduce32"),
            Err(SpecError::Malformed(_))
        ));
        let v: Value = serde_json::from_str(
            r#"{"kernel":"k","result":"per_block","input":"a","output":"b","length":"n",
                "shared":"s","max_block":300,
                "barriers":{"after_load":{},"loop":{}}}"#,
        )
        .unwrap();
        assert!(matches!(
            parse(&v, "reduce32"),
            Err(SpecError::Unsupported(_))
        ));
    }
}
