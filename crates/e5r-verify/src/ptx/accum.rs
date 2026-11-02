//! The `accum` class of `e5r.ptx.spec.v1` (docs/verification-ptx.md,
//! "Atomics"): every thread combines one input element into one output word
//! with a commutative, associative atomic.
//!
//! ```json
//! { "schema": "e5r.ptx.spec.v1", "kernel": "acc_min_s32", "class": "accum",
//!   "op": "min", "type": "s32",
//!   "input": "acc_min_s32_param_0", "output": "acc_min_s32_param_1",
//!   "length": "acc_min_s32_param_2" }
//! ```
//!
//! `op` is `add`, `min`, `max`, `and`, `or` or `xor`; `type` the element
//! type: `u32 s32 b32 u64 s64 b64` (`min`/`max` compare signed for `s`,
//! unsigned otherwise). The statement is `Accum.Correct spec K`
//! (Ptx/Auto/Accum.lean); the generated proof is the one phase obligation.
//! `exch` and `cas` are not a class: their result depends on the order.

use super::blocksearch::{self, Check, Choice, Ran, Witness};
use super::spec::SpecError;
use e5r_ptx::ast::{Kernel, Ty};
use e5r_ptx::interp::{self, Dim3, Mem};
use serde_json::{Value, json};
use std::collections::HashMap;
use std::fmt::Write;

#[derive(Clone, Debug)]
pub struct AccumSpec {
    pub kernel: String,
    pub input: String,
    pub output: String,
    pub length: String,
    pub op: String,
    pub ty: String,
    /// The Lean algebra (Ptx/Logic/CellAlgs.lean).
    pub alg: &'static str,
    pub wide: bool,
}

fn s<'a>(v: &'a Value, k: &str) -> Result<&'a str, SpecError> {
    v.get(k)
        .and_then(Value::as_str)
        .ok_or_else(|| SpecError::Malformed(format!("spec: \"{k}\" must be a string")))
}

/// The algebra of `op` at `ty`.
fn alg(op: &str, ty: &str) -> Option<&'static str> {
    Some(match (op, ty) {
        ("add", "u32" | "s32") => "add32",
        ("add", "u64" | "s64") => "add64",
        ("min", "u32") => "minu32",
        ("min", "s32") => "mins32",
        ("min", "u64") => "minu64",
        ("min", "s64") => "mins64",
        ("max", "u32") => "maxu32",
        ("max", "s32") => "maxs32",
        ("max", "u64") => "maxu64",
        ("max", "s64") => "maxs64",
        ("and", "b32" | "u32" | "s32") => "and32",
        ("or", "b32" | "u32" | "s32") => "or32",
        ("xor", "b32" | "u32" | "s32") => "xor32",
        ("and", "b64" | "u64" | "s64") => "and64",
        ("or", "b64" | "u64" | "s64") => "or64",
        ("xor", "b64" | "u64" | "s64") => "xor64",
        _ => return None,
    })
}

pub fn parse(v: &Value) -> Result<AccumSpec, SpecError> {
    let op = s(v, "op")?.to_string();
    let ty = s(v, "type")?.to_string();
    let Some(a) = alg(&op, &ty) else {
        return Err(SpecError::Unsupported(format!(
            "accum: atomic {op}.{ty} (add, min, max, and, or, xor at 32 or 64 bits; exch and cas are order-dependent)"
        )));
    };
    Ok(AccumSpec {
        kernel: s(v, "kernel")?.to_string(),
        input: s(v, "input")?.to_string(),
        output: s(v, "output")?.to_string(),
        length: s(v, "length")?.to_string(),
        wide: ty.ends_with("64"),
        op,
        ty,
        alg: a,
    })
}

/// What the statement needs from the kernel.
pub fn validate(sp: &AccumSpec, k: &Kernel) -> Result<(), String> {
    if ["spec", "obligation", "correct"].contains(&k.name.as_str()) {
        return Err(format!("accum: kernel name {} is reserved by the proof file", k.name));
    }
    let names = [&sp.input, &sp.output, &sp.length];
    if names[0] == names[1] || names[0] == names[2] || names[1] == names[2] {
        return Err("input, output and length must be different parameters".into());
    }
    if k.params.len() != 3 {
        return Err(format!("accum: the kernel has {} parameters (input, output, length)", k.params.len()));
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

fn q(s: &str) -> String {
    serde_json::to_string(s).unwrap()
}

pub fn spec_text(sp: &AccumSpec) -> String {
    let k = if sp.wide { 2 } else { 1 };
    let sz = if sp.wide { ".b8" } else { ".b4" };
    let mut t = String::new();
    writeln!(
        t,
        "def spec : Accum.Spec where\n  input := {}\n  output := {}\n  length := {}\n  alg := {}\n",
        q(&sp.input),
        q(&sp.output),
        q(&sp.length),
        sp.alg
    )
    .unwrap();
    for (n, v) in [("input", q(&sp.input)), ("output", q(&sp.output)), ("length", q(&sp.length))] {
        writeln!(t, "@[simp] theorem spec_{n} : spec.{n} = {v} := rfl").unwrap();
    }
    writeln!(t, "@[simp] theorem spec_k : spec.k = {k} := rfl").unwrap();
    writeln!(t, "@[simp] theorem spec_sz : spec.alg.sz = {sz} := rfl").unwrap();
    t
}

pub fn lean_spec(sp: &AccumSpec) -> String {
    let t = spec_text(sp);
    t[..t.find("\n\n").unwrap_or(t.len())].to_string()
}

pub fn statement_prelude(k: &Kernel, sp: &AccumSpec, header: &str) -> String {
    format!(
        "/-\n{}\n-/\nimport Ptx.Auto.Accum\n\nnamespace E5rSpec\nopen Ptx Ptx.Auto Ptx.Auto.Accum\n\n{}{}",
        header.trim_end(),
        e5r_ptx::lean::kernel_def(k),
        spec_text(sp)
    )
}

const TEMPLATE: &str = include_str!("templates/accum.lean");

/// The proof attempt: `theorem E5rCheck.correct : Accum.Correct spec K`.
pub fn proof(k: &Kernel, sp: &AccumSpec, header: &str) -> String {
    let kn = format!("«{}»", k.name);
    let gid = "t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat";
    let (idx, access, _, trunc, valsimp) = if sp.wide {
        (
            format!("2 * ({gid})"),
            "    | exact accessOk_elem2_b8 (base := A.x) (N := A.n.toNat) (by simp) fx (by simpa using xal) (by omega)\n    \
             | exact accessOk_elem2_b8 (base := A.out) (N := 1) (i := 0) (by simp) fout (by simpa using oal) (by omega)"
                .to_string(),
            "",
            "rfl",
            "spec_sz",
        )
    } else {
        (
            gid.to_string(),
            "    | exact accessOk_elem_mem (base := A.x) (N := A.n.toNat) (by simp) fx (by simpa using xal) (by omega)\n    \
             | exact accessOk_elem_mem (base := A.out) (N := 1) (by simp) fout (by simpa using oal) (by omega)"
                .to_string(),
            "",
            "(trunc_b4_ext32 _)",
            "spec_sz, rd_b4, lo32_ext32, Nat.one_mul",
        )
    };
    let accum = format!("accum_{}", sp.alg);
    TEMPLATE
        .replace("@HEADER@", header.trim_end())
        .replace("@KERNEL_DEF@", &e5r_ptx::lean::kernel_def(k))
        .replace("@SPEC_DEF@", &spec_text(sp))
        .replace("@N@", &(k.body.len() + 2).to_string())
        .replace("@IDX@", &idx)
        .replace("@ACCESS@", &access)
        .replace("@ACCUM@", &accum)
        .replace("@TRUNC@", trunc)
        .replace("@VALSIMP@", valsimp)
        .replace("@K@", &kn)
}

/// One concrete launch.
#[derive(Clone, Debug)]
pub struct World {
    pub g: u32,
    pub b: u32,
    pub n: u32,
    pub x: u64,
    pub out: u64,
    pub mem: Mem,
}

fn bytes(sp: &AccumSpec) -> u32 {
    if sp.wide { 8 } else { 4 }
}

fn mask(sp: &AccumSpec, v: u64) -> u64 {
    if sp.wide { v } else { v & 0xffff_ffff }
}

/// The algebra's operation, as Rust computes it.
fn op(sp: &AccumSpec, a: u64, b: u64) -> u64 {
    let (a, b) = (mask(sp, a), mask(sp, b));
    let signed = sp.ty.starts_with('s');
    let lt = |x: u64, y: u64| {
        if signed {
            if sp.wide { (x as i64) < (y as i64) } else { (x as u32 as i32) < (y as u32 as i32) }
        } else {
            x < y
        }
    };
    mask(
        sp,
        match sp.op.as_str() {
            "add" => a.wrapping_add(b),
            "and" => a & b,
            "or" => a | b,
            "xor" => a ^ b,
            "min" => if lt(b, a) { b } else { a },
            _ => if lt(a, b) { b } else { a },
        },
    )
}

fn pattern(sp: &AccumSpec, i: u32) -> u64 {
    let v = (i as u64 + 1).wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ 0x8040_2010_0804_0201;
    mask(sp, v)
}

fn worlds(sp: &AccumSpec) -> Vec<World> {
    let mut v = Vec::new();
    let w = bytes(sp) as u64;
    for g in 1..=3u32 {
        for b in [1u32, 2, 3, 4, 8] {
            let gb = g * b;
            let mut ns = vec![gb, gb.saturating_sub(1), gb + 1, 1, 0, 1 << 31, u32::MAX];
            ns.sort();
            ns.dedup();
            for n in ns {
                let x = 0x1000u64;
                let out = (x + w * n as u64 + 0x40).div_ceil(0x100) * 0x100;
                let mut mem = Mem::default();
                for i in 0..n.min(gb + 1) {
                    mem.wr(x + w * i as u64, bytes(sp), pattern(sp, i));
                }
                mem.wr(out, bytes(sp), mask(sp, 0xc3c3_c3c3_c3c3_c3c3));
                v.push(World { g, b, n, x, out, mem });
            }
        }
    }
    v.sort_by_key(|w| (w.g * w.b, w.n));
    v
}

fn launch(sp: &AccumSpec, w: &World) -> interp::Launch {
    let mut params = HashMap::new();
    params.insert(sp.input.clone(), w.x);
    params.insert(sp.output.clone(), w.out);
    params.insert(sp.length.clone(), w.n as u64);
    let wb = bytes(sp) as u128;
    interp::Launch {
        grid: Dim3 { x: w.g, y: 1, z: 1 },
        block: Dim3 { x: w.b, y: 1, z: 1 },
        params,
        sym: HashMap::new(),
        alloc: vec![
            interp::Region { base: w.x, size: wb * w.n as u128 },
            interp::Region { base: w.out, size: wb },
        ],
    }
}

/// Search the small launches; the first candidate and how many ran.
pub fn search(k: &Kernel, sp: &AccumSpec) -> (Option<(World, Witness)>, usize) {
    let mut tried = 0;
    let wb = bytes(sp);
    for w in worlds(sp) {
        tried += 1;
        let l = launch(sp, &w);
        let mut g = w.mem.clone();
        let fuel = 64 * (k.body.len() + 4) * (w.g * w.b) as usize + 64;
        let (end, ch, evs) = blocksearch::run(k, &l, &mut g, fuel);
        match end {
            Ran::Fault(thread, why) => {
                return (Some((w, Witness::Fault { sched: ch, thread, why })), tried);
            }
            Ran::Fuel => continue,
            Ran::Done => {}
        }
        if let Some(r) = blocksearch::race(&ch, &evs) {
            return (Some((w, r)), tried);
        }
        let mut want = w.mem.rd(w.out, wb);
        for i in 0..(w.g * w.b) {
            if i < w.n {
                want = op(sp, want, w.mem.rd(w.x + wb as u64 * i as u64, wb));
            }
        }
        let got = g.rd(w.out, wb);
        if got != want {
            return (Some((w, Witness::Wrong { sched: ch, check: Check::Value(0), got, want })), tried);
        }
        let mut keys: Vec<u64> = g.bytes.keys().chain(w.mem.bytes.keys()).copied().collect();
        keys.sort();
        keys.dedup();
        for a in keys {
            let inside = a >= w.out && a < w.out + wb as u64;
            if !inside && g.get(a) != w.mem.get(a) {
                let (gv, wv) = (g.get(a) as u64, w.mem.get(a) as u64);
                return (
                    Some((w, Witness::Wrong { sched: ch, check: Check::Frame(a), got: gv, want: wv })),
                    tried,
                );
            }
        }
    }
    (None, tried)
}

pub fn describe(w: &World, wit: &Witness) -> Value {
    let mut v = json!({
        "kind": wit.kind(),
        "launch": {"grid": w.g, "block": w.b, "n": w.n, "x": format!("{:#x}", w.x),
                   "out": format!("{:#x}", w.out)},
        "initial_memory": "x[i] = ((i + 1) * 0x9e3779b97f4a7c15) ^ 0x8040201008040201 (masked to the element size), out = 0xc3..c3, every other byte 0; registers 0",
    });
    match wit {
        Witness::Fault { thread, why, sched } => {
            v["thread"] = json!(thread.map(|(c, t)| json!({"ctaid": c, "tid": t})));
            v["reason"] = json!(why);
            v["schedule_length"] = json!(sched.len());
        }
        Witness::Race { t, u, x, y, byte, .. } => {
            v["first"] = json!({"ctaid": t.0, "tid": t.1, "access": blocksearch::acc_json(x)});
            v["second"] = json!({"ctaid": u.0, "tid": u.1, "access": blocksearch::acc_json(y)});
            v["byte"] = json!(format!("{byte:#x}"));
        }
        Witness::Wrong { check, got, want, .. } => {
            if let Check::Frame(a) = check {
                v["byte"] = json!(format!("{a:#x}"));
            }
            v["got"] = json!(format!("{got:#x}"));
            v["want"] = json!(format!("{want:#x}"));
        }
    }
    v
}

/// The refutation: `theorem E5rCheck.refuted : ¬ Accum.Correct spec K`.
pub fn refutation(k: &Kernel, sp: &AccumSpec, header: &str, w: &World, wit: &Witness) -> String {
    use blocksearch::{bv, sched, tid};
    let kn = format!("«{}»", k.name);
    let mut s = String::new();
    writeln!(
        s,
        "/-\n{}\n-/\nimport Ptx.Auto.Accum\nimport Ptx.Logic.Schedule\n\n\
         set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n\
         namespace E5rCheck\nopen Ptx Ptx.Auto Ptx.Auto.Accum\n",
        header.trim_end()
    )
    .unwrap();
    s.push_str(&e5r_ptx::lean::kernel_def(k));
    s.push_str(&spec_text(sp));
    let mut mem = String::from("0");
    let mut bs: Vec<(&u64, &u8)> = w.mem.bytes.iter().filter(|(_, v)| **v != 0).collect();
    bs.sort();
    for (a, v) in bs.iter().rev() {
        mem = format!("if x = {} then {} else {mem}", bv(**a as u128, 64), bv(**v as u128, 8));
    }
    writeln!(
        s,
        "def A₀ : Accum.Args spec where\n  G := {}\n  B := {}\n  n := {}\n  x := {}\n  out := {}\n\n\
         def m₀ : Mem := fun x => {mem}\n\n\
         abbrev L₀ : Launch := A₀.launch\n\
         def c₀ : Cfg := Cfg.init (fun _ _ => 0) (fun _ _ => false) m₀ (fun _ _ => 0)\n\
         def tid (c t : BitVec 32) : Tid := ⟨⟨c, 0, 0⟩, ⟨t, 0, 0⟩⟩\n\n\
         theorem pre : A₀.Pre := by\n  unfold Args.Pre Fits\n  decide +kernel\n\n\
         theorem refuted : ¬ Accum.Correct spec {kn} := by\n  intro h\n  \
         obtain ⟨hnf, -, -, hrf, -, hfin⟩ := h A₀ pre m₀ (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => false)",
        bv(w.g as u128, 32),
        bv(w.b as u128, 32),
        bv(w.n as u128, 32),
        bv(w.x as u128, 64),
        bv(w.out as u128, 64)
    )
    .unwrap();
    match wit {
        Witness::Fault { sched: cs, .. } => writeln!(
            s,
            "  obtain ⟨c, hr, hf⟩ := exec_any (K := {kn}) (L := L₀) (c₀ := c₀) (p := faultsB {kn} L₀)\n    \
             (cs := {}) (by decide +kernel)\n  exact hnf c hr (faultsB_spec hf)",
            sched(cs)
        )
        .unwrap(),
        Witness::Race { s1, s2, t, u, byte, .. } => writeln!(
            s,
            "  exact race_of_exec (K := {kn}) (L := L₀) (c₀ := c₀) (t := {}) (u := {}) (b := {})\n    \
             (cs₁ := {}) (cs₂ := {}) (by decide +kernel) hrf",
            tid(*t),
            tid(*u),
            bv(*byte as u128, 64),
            sched(s1),
            sched(s2)
        )
        .unwrap(),
        Witness::Wrong { sched: cs, check, .. } => {
            let (lhs, rhs, proj, arg) = match check {
                Check::Value(_) => (
                    "rd c.mem A₀.out spec.alg.sz".to_string(),
                    "spec.alg.op (rd m₀ A₀.out spec.alg.sz) (afold spec.alg (fun i => if i < A₀.n.toNat \
                     then A₀.elt m₀ i else spec.alg.e) (A₀.G.toNat * A₀.B.toNat))"
                        .to_string(),
                    ".1",
                    String::new(),
                ),
                Check::Frame(a) => (
                    format!("c.mem {}", bv(*a as u128, 64)),
                    format!("m₀ {}", bv(*a as u128, 64)),
                    ".2",
                    format!(" {} (by decide +kernel)", bv(*a as u128, 64)),
                ),
            };
            writeln!(
                s,
                "  obtain ⟨c, hr, hp⟩ := exec_any (K := {kn}) (L := L₀) (c₀ := c₀)\n    \
                 (p := fun c => doneB {kn} L₀ c && decide ({lhs} ≠ {rhs}))\n    \
                 (cs := {}) (by decide +kernel)\n  \
                 simp only [Bool.and_eq_true, decide_eq_true_eq] at hp\n  \
                 exact hp.2 ((hfin c hr (doneB_spec hp.1)){proj}{arg})",
                sched(cs)
            )
            .unwrap();
        }
    }
    s.push_str("\nend E5rCheck\n\n#print axioms E5rCheck.refuted\n");
    let _ = Choice::Rel(0);
    s
}
