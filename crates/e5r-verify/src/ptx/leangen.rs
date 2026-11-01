//! The Lean files a check runs: the proof attempt and, when the search finds
//! one, the refutation. Both are fixed templates filled from the PTX and the
//! spec; nothing in them is written per kernel by a person.

use super::search::{Witness, World};
use super::spec::{Role, Sched, Spec};
use e5r_ptx::ast::Kernel;
use std::fmt::Write;

fn q(s: &str) -> String {
    serde_json::to_string(s).unwrap()
}

fn list(v: &[String]) -> String {
    format!(
        "[{}]",
        v.iter().map(|x| q(x)).collect::<Vec<_>>().join(", ")
    )
}

fn role(r: &Role) -> String {
    match r {
        Role::Idx(64) => ".idx .w64".into(),
        Role::Idx(_) => ".idx .w32".into(),
        Role::Stride(64) => ".stride .w64".into(),
        Role::Stride(_) => ".stride .w32".into(),
        Role::Len => ".len".into(),
        Role::Base(a) => format!(".base {}", q(a)),
        Role::Ptr(a) => format!(".ptr {}", q(a)),
        Role::PtrStride => ".ptrStride".into(),
        Role::Scalar(a) => format!(".scalar {}", q(a)),
        Role::Const(v) => format!(".const (BitVec.ofNat 64 {v})"),
    }
}

pub fn kname(k: &Kernel) -> String {
    format!("«{}»", k.name)
}

/// Kernel, spec and the `ptx_spec` lemmas: shared by both files.
fn prelude(k: &Kernel, sp: &Spec, header: &str, extra_import: &str) -> String {
    let mut s = String::new();
    writeln!(
        s,
        "/-\n{}\n-/\nimport Ptx.Auto.Tactic{extra_import}\n",
        header.trim_end()
    )
    .unwrap();
    s.push_str(
        "set_option maxHeartbeats 1000000\nset_option linter.unusedVariables false\nset_option linter.unusedSimpArgs false\n\n",
    );
    s.push_str("namespace E5rCheck\nopen Ptx Ptx.Auto\n\n");
    s.push_str(&e5r_ptx::lean::kernel_def(k));
    let sched = match &sp.sched {
        Sched::Guarded { max_threads } => format!(".guarded {max_threads}"),
        Sched::Stride { bound, .. } => format!(".stride {bound}"),
    };
    let f = format!("fun s e => {}", sp.element.lean());
    writeln!(
        s,
        "def spec : MapSpec where\n  arrays := {}\n  out := {}\n  len := {}\n  scalars := {}\n  f := {f}\n  sched := {sched}\n",
        list(&sp.arrays),
        q(&sp.output),
        q(&sp.length),
        list(&sp.scalars)
    )
    .unwrap();
    for (n, v) in [
        ("arrays", list(&sp.arrays)),
        ("out", q(&sp.output)),
        ("len", q(&sp.length)),
        ("scalars", list(&sp.scalars)),
        (
            "f",
            format!("({f} : (String → BitVec 32) → (String → BitVec 32) → BitVec 32)"),
        ),
        ("sched", sched.clone()),
    ] {
        writeln!(s, "@[ptx_spec] theorem spec_{n} : spec.{n} = {v} := rfl").unwrap();
    }
    s.push('\n');
    if let Sched::Stride { head, regs, .. } = &sp.sched {
        let pc = k.labels.iter().find(|(l, _)| l == head).unwrap().1;
        let regs: Vec<String> = regs
            .iter()
            .map(|(r, x)| format!("({}, {})", q(r), role(x)))
            .collect();
        let regs = format!("[{}]", regs.join(", "));
        writeln!(
            s,
            "def loop : Loop where\n  head := {pc}\n  regs := {regs}\n"
        )
        .unwrap();
        writeln!(s, "@[ptx_spec] theorem loop_head : loop.head = {pc} := rfl").unwrap();
        writeln!(
            s,
            "@[ptx_spec] theorem loop_regs : loop.regs = {regs} := rfl\n"
        )
        .unwrap();
    }
    s
}

fn bases(sp: &Spec) -> String {
    sp.arrays
        .iter()
        .map(|a| format!("A.base {}", q(a)))
        .collect::<Vec<_>>()
        .join(", ")
}

/// The proof attempt: `theorem E5rCheck.correct : spec.Correct K`.
pub fn proof(k: &Kernel, sp: &Spec, header: &str) -> String {
    let mut s = prelude(k, sp, header, "");
    let kn = kname(k);
    let fuel = 2 * k.body.len() + 8;
    match &sp.sched {
        Sched::Guarded { .. } => {
            writeln!(
                s,
                "theorem thread : spec.GuardedOk {kn} := by\n  ptx_guarded {kn} {fuel} [{}]\n\n\
                 theorem correct : spec.Correct {kn} :=\n  correct_of_threadOk (threadOk_of_guardedOk spec_sched thread)\n",
                bases(sp)
            )
            .unwrap();
        }
        Sched::Stride { head, .. } => {
            let pc = k.labels.iter().find(|(l, _)| l == head).unwrap().1;
            writeln!(
                s,
                "theorem entry : spec.EntryOk loop {kn} := by\n  ptx_stride_entry {kn} {pc} {fuel}\n\n\
                 theorem body : spec.BodyOk loop {kn} := by\n  ptx_stride_body {kn} {pc} {fuel} [{}]\n\n\
                 theorem correct : spec.Correct {kn} :=\n  correct_of_threadOk (threadOk_of_stride entry body)\n",
                bases(sp)
            )
            .unwrap();
        }
    }
    s.push_str("end E5rCheck\n\n#print axioms E5rCheck.correct\n");
    s
}

fn bv(v: u128, w: u32) -> String {
    format!("({v}#{w})")
}

fn tid(t: (u32, u32)) -> String {
    format!("(tid {} {})", t.0, t.1)
}

/// What `simp` needs to run the kernel on the concrete world.
fn eval_set(kn: &str) -> String {
    format!(
        "okSteps, stepMem, ptx_eval, {kn}, L₀, MapSpec.launch, MapSpec.params, A₀, ptx_spec, c₀, \
         Cfg.init, tid, accessOk, Region.holds, lo32, ext32, m₀, rd, rd32, wr, Cfg.advance, Cfg.res, \
         trace, updT, Cfg.pending, Action.acc, List.mem_cons, List.not_mem_nil, elem"
    )
}

/// The refutation: `theorem E5rCheck.refuted : ¬ spec.Correct K`, from a
/// counterexample the search found. The kernel replays it.
pub fn refutation(k: &Kernel, sp: &Spec, header: &str, w: &World, wit: &Witness) -> String {
    let mut s = prelude(k, sp, header, "\nimport Ptx.Logic.Refute");
    let kn = kname(k);
    let ev = eval_set(&kn);
    let mut base = String::from("0");
    for (a, b) in w.bases.iter().rev() {
        base = format!("if a = {} then {} else {base}", q(a), bv(*b as u128, 64));
    }
    let mut sc = String::from("0");
    for (a, v) in w.scalars.iter().rev() {
        sc = format!("if a = {} then {} else {sc}", q(a), bv(*v as u128, 32));
    }
    let mut mem = String::from("0");
    let mut bytes: Vec<(&u64, &u8)> = w.mem.bytes.iter().filter(|(_, v)| **v != 0).collect();
    bytes.sort();
    for (a, v) in bytes.iter().rev() {
        mem = format!(
            "if x = {} then {} else {mem}",
            bv(**a as u128, 64),
            bv(**v as u128, 8)
        );
    }
    writeln!(
        s,
        "def A₀ : Args where\n  G := {}\n  B := {}\n  n := {}\n  base := fun a => {base}\n  sc := fun a => {sc}\n\n\
         def m₀ : Mem := fun x => {mem}\n\n\
         abbrev L₀ : Launch := spec.launch A₀\n\
         def c₀ : Cfg := Cfg.init (fun _ _ => 0) (fun _ _ => false) m₀\n\
         def tid (c t : BitVec 32) : Tid := ⟨⟨c, 0, 0⟩, ⟨t, 0, 0⟩⟩\n\n\
         theorem pre : spec.Pre A₀ := by\n  simp [MapSpec.Pre, MapSpec.SchedOk, MapSpec.Sep, Fits, ptx_spec, A₀]\n",
        bv(w.g as u128, 32),
        bv(w.b as u128, 32),
        bv(w.n as u128, 32)
    )
    .unwrap();
    let mem_t = |t: (u32, u32)| {
        format!(
            "  have h{0}_{1} : {2} ∈ L₀.threads := by\n    rw [mem_threads]; simp only [Launch.Thread, L₀, MapSpec.launch, A₀, tid]; decide\n",
            t.0,
            t.1,
            tid(t)
        )
    };
    s.push_str("theorem refuted : ¬ spec.Correct ");
    s.push_str(&kn);
    s.push_str(" := by\n  intro h\n  obtain ⟨hnf, -, -, hrf, -, hfin⟩ := h A₀ m₀ (fun _ _ => 0) (fun _ _ => false) pre\n");
    match wit {
        Witness::Fault { t, steps, .. } => {
            s.push_str(&mem_t(*t));
            writeln!(
                s,
                "  exact hnf _ (reach_thread' (j := {steps}) h{0}_{1} (by simp [{ev}]))\n    ⟨{2}, h{0}_{1}, by simp [{ev}]⟩",
                t.0,
                t.1,
                tid(*t)
            )
            .unwrap();
        }
        Witness::Race {
            t,
            j,
            x,
            u,
            i,
            y,
            byte,
        } => {
            s.push_str(&mem_t(*t));
            if u != t {
                s.push_str(&mem_t(*u));
            }
            let acc = |a: &(u64, u32, bool)| {
                format!("some ({}, .b{}, {})", bv(a.0 as u128, 64), a.1, a.2)
            };
            let (ht, hu) = (format!("h{}_{}", t.0, t.1), format!("h{}_{}", u.0, u.1));
            writeln!(
                s,
                "  let c₁ := c₀.advance {kn} L₀ {t1} {j}\n  let c₂ := c₀.advance {kn} L₀ {u1} {i}\n\
                 \x20 have r₁ : Reach {kn} L₀ c₀ c₁ := reach_thread' {ht} (by simp [{ev}])\n\
                 \x20 have r₂ : Reach {kn} L₀ c₀ c₂ := reach_thread' {hu} (by simp [{ev}])\n\
                 \x20 have p₁ : c₁.pending {kn} L₀ {t1} = {ax} := by simp [c₁, {ev}]\n\
                 \x20 have p₂ : c₂.pending {kn} L₀ {u1} = {ay} := by simp [c₂, {ev}]\n\
                 \x20 exact hrf c₁ c₂ r₁ r₂ _ {ht} _ {hu} (by decide) _ _ p₁ p₂ ⟨{w}, {byte}, by decide, by decide⟩",
                t1 = tid(*t),
                u1 = tid(*u),
                ax = acc(x),
                ay = acc(y),
                w = if x.2 { ".inl rfl" } else { ".inr rfl" },
                byte = bv(*byte as u128, 64)
            )
            .unwrap();
        }
        Witness::Wrong { order, check } => {
            for (t, _) in order {
                s.push_str(&mem_t(*t));
            }
            let mut prev = "c₀".to_string();
            for (n, (t, j)) in order.iter().enumerate() {
                writeln!(
                    s,
                    "  let d{n} := {prev}.advance {kn} L₀ {} {j}\n  have r{n} : Reach {kn} L₀ {prev} d{n} := reach_thread' h{}_{} (by simp [{ev}{}])",
                    tid(*t),
                    t.0,
                    t.1,
                    (0..n).map(|m| format!(", d{m}")).collect::<String>()
                )
                .unwrap();
                prev = format!("d{n}");
            }
            let last = order.len() - 1;
            let mut reach = "r0".to_string();
            for n in 1..order.len() {
                reach = format!("(Reach.trans {reach} r{n})");
            }
            let ds: String = (0..order.len()).map(|m| format!(", d{m}")).collect();
            let all: Vec<String> = order.iter().map(|(t, _)| tid(*t)).collect();
            writeln!(
                s,
                "  have hall : L₀.threads = [{}] := by decide\n\
                 \x20 have hd : Done {kn} L₀ d{last} := by\n    intro t ht\n    rw [hall] at ht\n    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht\n    rcases ht with {} <;> simp [{ev}{ds}]",
                all.join(", "),
                (0..order.len()).map(|_| "rfl").collect::<Vec<_>>().join(" | "),
            )
            .unwrap();
            let fin = format!("hfin d{last} {reach} hd (by decide)");
            match check {
                super::search::Check::Value { index } => writeln!(
                    s,
                    "  have hv := ({fin}).1 {index} (by decide)\n  revert hv\n  simp [MapSpec.val{ds}, {ev}]"
                )
                .unwrap(),
                super::search::Check::Frame { byte } => writeln!(
                    s,
                    "  have hv := ({fin}).2 {} (by simp [{ev}, elem, covers] <;> decide)\n  revert hv\n  simp [{ev}{ds}]",
                    bv(*byte as u128, 64)
                )
                .unwrap(),
            }
        }
    }
    s.push_str("\nend E5rCheck\n\n#print axioms E5rCheck.refuted\n");
    s
}
