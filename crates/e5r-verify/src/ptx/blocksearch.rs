//! Counterexamples for the block classes: small launches run on the
//! (untrusted) interpreter with one schedule of the whole grid, recorded as
//! the choices `Ptx.Cfg.exec` replays (Ptx/Logic/Schedule.lean). A candidate
//! counts only when the Lean kernel has replayed it against the class
//! theorem's statement; the interpreter only proposes.

use super::block::{BlockSpec, Class};
use e5r_ptx::ast::Kernel;
use e5r_ptx::interp::{self, Access, Dim3, End, Kind, Mem, Sp, TState};
use serde_json::{Value, json};
use std::collections::HashMap;
use std::fmt::Write;

/// Run thread `(cta, tid)` for `n` steps, or release CTA `cta`'s barrier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Choice {
    Run((u32, u32), usize),
    Rel(u32),
}

/// One concrete launch.
#[derive(Clone, Debug)]
pub struct World {
    pub g: u32,
    pub b: u32,
    pub j: u32,
    pub n: u32,
    pub x: u64,
    pub out: u64,
    pub sh: Vec<(String, u64)>,
    pub mem: Mem,
}

#[derive(Clone, Debug)]
pub enum Check {
    /// The output word at this index (`per_block`: block, `scan32`: element;
    /// `atomic`: the one word).
    Value(u64),
    /// A byte outside the output that changed.
    Frame(u64),
}

#[derive(Clone, Debug)]
pub enum Witness {
    Fault {
        sched: Vec<Choice>,
        thread: Option<(u32, u32)>,
        why: String,
    },
    Race {
        s1: Vec<Choice>,
        s2: Vec<Choice>,
        t: (u32, u32),
        u: (u32, u32),
        x: Access,
        y: Access,
        byte: u64,
    },
    Wrong {
        sched: Vec<Choice>,
        check: Check,
        got: u64,
        want: u64,
    },
}

impl Witness {
    pub fn kind(&self) -> &'static str {
        match self {
            Witness::Fault { .. } => "fault",
            Witness::Race { .. } => "race",
            Witness::Wrong { .. } => "wrong_value",
        }
    }
}

/// How many words the output region has.
fn out_len(c: Class, w: &World) -> u64 {
    match c {
        Class::Reduce => w.g as u64,
        Class::ReduceAtomic => 1,
        Class::Scan => w.n as u64,
    }
}

fn pattern(i: u32) -> u32 {
    (i.wrapping_add(1)).wrapping_mul(0x0101_0101) ^ 0x8040_2010
}

fn world(k: &Kernel, sp: &BlockSpec, g: u32, b: u32, n: u32) -> World {
    let j = if sp.class == Class::Scan {
        32 - (b - 1).leading_zeros() // rounds: smallest R with b <= 2^R
    } else {
        b.trailing_zeros()
    };
    let x = 0x1000u64;
    let out = (x + 4 * n as u64 + 0x40).div_ceil(0x100) * 0x100;
    let mut mem = Mem::default();
    for i in 0..n {
        mem.wr(x + 4 * i as u64, 4, pattern(i) as u64);
    }
    let mut w = World {
        g,
        b,
        j,
        n,
        x,
        out,
        sh: Vec::new(),
        mem,
    };
    for i in 0..out_len(sp.class, &w) {
        w.mem.wr(out + 4 * i, 4, 0xC3C3_C3C3);
    }
    let lay = interp::layout(k, 0);
    w.sh = k
        .shared
        .iter()
        .map(|d| (d.name.clone(), lay[&d.name]))
        .collect();
    w
}

/// The launches the search tries, smallest first, inside the class's `Pre`.
fn worlds(k: &Kernel, sp: &BlockSpec) -> Vec<World> {
    let mut v = Vec::new();
    let bs: Vec<u32> = match sp.class {
        Class::Scan => (1..=8).filter(|b| *b <= sp.max_block).collect(),
        _ => [1, 2, 4, 8].into_iter().filter(|b| *b <= sp.max_block).collect(),
    };
    for g in 1..=3u32 {
        for &b in &bs {
            let gb = g * b;
            let mut ns: Vec<u32> = if sp.class == Class::Scan {
                vec![gb, gb.saturating_sub(1), 1, 0]
            } else {
                vec![gb, gb.saturating_sub(1), gb + 1, 1, 0]
            };
            ns.sort();
            ns.dedup();
            if sp.class == Class::Scan {
                ns.retain(|n| *n <= gb);
            }
            for n in ns {
                v.push(world(k, sp, g, b, n));
            }
        }
    }
    v.sort_by_key(|w| (w.g * w.b, w.n));
    v
}

struct Ev {
    t: (u32, u32),
    cta: u32,
    phase: usize,
    access: Access,
    prefix: usize,
    within: usize,
}

enum Ran {
    Done,
    Fault(Option<(u32, u32)>, String),
    Fuel,
}

fn launch(sp: &BlockSpec, w: &World) -> interp::Launch {
    let mut params = HashMap::new();
    params.insert(sp.input.clone(), w.x);
    params.insert(sp.output.clone(), w.out);
    params.insert(sp.length.clone(), w.n as u64);
    let len = out_len(sp.class, w);
    interp::Launch {
        grid: Dim3 { x: w.g, y: 1, z: 1 },
        block: Dim3 { x: w.b, y: 1, z: 1 },
        params,
        sym: w.sh.iter().cloned().collect(),
        alloc: vec![
            interp::Region {
                base: w.x,
                size: 4 * w.n as u128,
            },
            interp::Region {
                base: w.out,
                size: 4 * len as u128,
            },
        ],
    }
}

/// The schedule `interp::run_grid` follows, recorded.
fn run(k: &Kernel, l: &interp::Launch, g: &mut Mem, fuel: usize) -> (Ran, Vec<Choice>, Vec<Ev>) {
    let al = l.allocs(k);
    let mut ch = Vec::new();
    let mut evs = Vec::new();
    let mut left = fuel;
    for cta in 0..l.grid.x {
        let mut sh = Mem::default();
        let n = l.block.x;
        let ctxs: Vec<_> = (0..n)
            .map(|t| l.ctx(Dim3 { x: cta, y: 0, z: 0 }, Dim3 { x: t, y: 0, z: 0 }))
            .collect();
        let mut ts = vec![TState::default(); n as usize];
        let mut phase = 0;
        loop {
            let mut ends = Vec::new();
            for t in 0..n {
                let prefix = ch.len();
                let (e, acc) =
                    interp::run_until_wait(k, &al, &ctxs[t as usize], &mut ts[t as usize], g, &mut sh, left);
                for (st, a) in acc {
                    evs.push(Ev {
                        t: (cta, t),
                        cta,
                        phase,
                        access: a,
                        prefix,
                        within: st,
                    });
                }
                let used = match &e {
                    End::Halted(u) | End::Wait(u) => *u,
                    End::Fault(u, why) => {
                        ch.push(Choice::Run((cta, t), *u));
                        return (Ran::Fault(Some((cta, t)), why.clone()), ch, evs);
                    }
                    End::OutOfFuel => return (Ran::Fuel, ch, evs),
                };
                ch.push(Choice::Run((cta, t), used));
                left -= used;
                ends.push(e);
            }
            let waiting: Vec<usize> = (0..ends.len())
                .filter(|i| matches!(ends[*i], End::Wait(_)))
                .collect();
            if waiting.is_empty() {
                break;
            }
            let pc = ts[waiting[0]].pc;
            if waiting.len() != ts.len() || waiting.iter().any(|i| ts[*i].pc != pc) {
                return (Ran::Fault(None, "barrier diverged".into()), ch, evs);
            }
            for s in ts.iter_mut() {
                s.pc += 1;
            }
            ch.push(Choice::Rel(cta));
            phase += 1;
            if left == 0 {
                return (Ran::Fuel, ch, evs);
            }
            left -= 1;
        }
    }
    (Ran::Done, ch, evs)
}

fn overlap(x: &Access, y: &Access) -> Option<u64> {
    let lo = x.addr.max(y.addr);
    let hi = (x.addr + x.size as u64).min(y.addr + y.size as u64);
    (lo < hi).then_some(lo)
}

/// The first pair of accesses `RaceFree` forbids.
fn race(ch: &[Choice], evs: &[Ev]) -> Option<Witness> {
    for (i, a) in evs.iter().enumerate() {
        for b in &evs[i + 1..] {
            if a.t == b.t || a.access.sp != b.access.sp {
                continue;
            }
            if a.access.sp == Sp::Shared && a.cta != b.cta {
                continue;
            }
            if a.access.kind == Kind::Read && b.access.kind == Kind::Read {
                continue;
            }
            let Some(byte) = overlap(&a.access, &b.access) else {
                continue;
            };
            if a.access.kind == Kind::Atomic
                && b.access.kind == Kind::Atomic
                && a.access.addr == b.access.addr
                && a.access.size == b.access.size
            {
                continue;
            }
            if a.cta == b.cta && a.phase != b.phase {
                continue;
            }
            let pre = |e: &Ev| {
                let mut s = ch[..e.prefix].to_vec();
                s.push(Choice::Run(e.t, e.within));
                s
            };
            return Some(Witness::Race {
                s1: pre(a),
                s2: pre(b),
                t: a.t,
                u: b.t,
                x: a.access,
                y: b.access,
                byte,
            });
        }
    }
    None
}

fn rd32(m: &Mem, a: u64) -> u32 {
    m.rd(a, 4) as u32
}

/// What the class theorem says the output holds.
fn expected(sp: &BlockSpec, w: &World, m0: &Mem) -> Vec<(u64, u32)> {
    let xi = |i: u64| rd32(m0, w.x + 4 * i);
    let (b, n) = (w.b as u64, w.n as u64);
    match sp.class {
        Class::Reduce => (0..w.g as u64)
            .map(|c| {
                let s = (0..b)
                    .filter(|i| c * b + i < n)
                    .fold(0u32, |s, i| s.wrapping_add(xi(c * b + i)));
                (c, s)
            })
            .collect(),
        Class::ReduceAtomic => {
            let s = (0..w.g as u64 * b)
                .filter(|i| *i < n)
                .fold(rd32(m0, w.out), |s, i| s.wrapping_add(xi(i)));
            vec![(0, s)]
        }
        Class::Scan => (0..n)
            .map(|i| {
                let s = (0..=i % b).fold(0u32, |s, j| s.wrapping_add(xi(i / b * b + j)));
                (i, s)
            })
            .collect(),
    }
}

fn out_addr(sp: &BlockSpec, w: &World, i: u64) -> u64 {
    match sp.class {
        Class::ReduceAtomic => w.out,
        _ => w.out + 4 * i,
    }
}

/// Search the small launches; the first candidate and how many launches ran.
pub fn search(k: &Kernel, sp: &BlockSpec) -> (Option<(World, Witness)>, usize) {
    let mut tried = 0;
    for w in worlds(k, sp) {
        tried += 1;
        let l = launch(sp, &w);
        let mut g = w.mem.clone();
        let fuel = 64 * (k.body.len() + 4) * (w.g * w.b) as usize + 64;
        let (end, ch, evs) = run(k, &l, &mut g, fuel);
        match end {
            Ran::Fault(thread, why) => {
                return (
                    Some((
                        w,
                        Witness::Fault {
                            sched: ch,
                            thread,
                            why,
                        },
                    )),
                    tried,
                );
            }
            Ran::Fuel => continue,
            Ran::Done => {}
        }
        if let Some(r) = race(&ch, &evs) {
            return (Some((w, r)), tried);
        }
        let exp = expected(sp, &w, &w.mem);
        for (i, v) in &exp {
            let got = rd32(&g, out_addr(sp, &w, *i));
            if got != *v {
                let check = Check::Value(*i);
                return (
                    Some((
                        w,
                        Witness::Wrong {
                            sched: ch,
                            check,
                            got: got as u64,
                            want: *v as u64,
                        },
                    )),
                    tried,
                );
            }
        }
        let olen = out_len(sp.class, &w);
        let mut keys: Vec<u64> = g.bytes.keys().chain(w.mem.bytes.keys()).copied().collect();
        keys.sort();
        keys.dedup();
        for a in keys {
            let inside = a >= w.out && a < w.out + 4 * olen;
            if !inside && g.get(a) != w.mem.get(a) {
                return (
                    Some((
                        w.clone(),
                        Witness::Wrong {
                            sched: ch,
                            check: Check::Frame(a),
                            got: g.get(a) as u64,
                            want: w.mem.get(a) as u64,
                        },
                    )),
                    tried,
                );
            }
        }
    }
    (None, tried)
}

fn acc_json(a: &Access) -> Value {
    json!({"space": if a.sp == Sp::Shared {"shared"} else {"global"},
           "address": format!("{:#x}", a.addr), "bytes": a.size,
           "kind": match a.kind { Kind::Read => "read", Kind::Write => "write", Kind::Atomic => "atomic" }})
}

/// The counterexample, for the result document.
pub fn describe(w: &World, wit: &Witness) -> Value {
    let mut v = json!({
        "kind": wit.kind(),
        "launch": {"grid": w.g, "block": w.b, "log": w.j, "n": w.n,
                   "x": format!("{:#x}", w.x), "out": format!("{:#x}", w.out),
                   "shared": w.sh.iter().map(|(n, a)| json!({"name": n, "at": format!("{a:#x}")})).collect::<Vec<_>>()},
        "initial_memory": "x[i] = ((i + 1) * 0x01010101) ^ 0x80402010, output words 0xc3c3c3c3, every other byte 0; registers and shared memory 0",
    });
    match wit {
        Witness::Fault { thread, why, sched } => {
            v["thread"] = json!(thread.map(|(c, t)| json!({"ctaid": c, "tid": t})));
            v["reason"] = json!(why);
            v["schedule_length"] = json!(sched.len());
        }
        Witness::Race { t, u, x, y, byte, .. } => {
            v["first"] = json!({"ctaid": t.0, "tid": t.1, "access": acc_json(x)});
            v["second"] = json!({"ctaid": u.0, "tid": u.1, "access": acc_json(y)});
            v["byte"] = json!(format!("{byte:#x}"));
        }
        Witness::Wrong { check, got, want, .. } => {
            match check {
                Check::Value(i) => v["index"] = json!(i),
                Check::Frame(a) => v["byte"] = json!(format!("{a:#x}")),
            }
            v["got"] = json!(format!("{got:#x}"));
            v["want"] = json!(format!("{want:#x}"));
        }
    }
    v
}

fn bv(v: u128, w: u32) -> String {
    format!("({v}#{w})")
}

fn tid(t: (u32, u32)) -> String {
    format!("(tid {} {})", t.0, t.1)
}

fn sched(cs: &[Choice]) -> String {
    let items: Vec<String> = cs
        .iter()
        .map(|c| match c {
            Choice::Run(t, n) => format!(".run {} {n}", tid(*t)),
            Choice::Rel(b) => format!(".rel ⟨{}, 0, 0⟩", bv(*b as u128, 32)),
        })
        .collect();
    format!("[{}]", items.join(",\n    "))
}

/// The refutation: `theorem E5rCheck.refuted : ¬ <class>.Correct spec K`.
pub fn refutation(k: &Kernel, sp: &BlockSpec, header: &str, w: &World, wit: &Witness) -> String {
    let kn = format!("«{}»", k.name);
    let (import, correct, pre, len) = match sp.class {
        Class::Reduce => (
            "Ptx.Auto.Reduce32",
            "Reduce32.Correct",
            "Reduce32.Pre",
            "A₀.G.toNat",
        ),
        Class::ReduceAtomic => (
            "Ptx.Auto.Reduce32",
            "Reduce32.Atomic.Correct",
            "Reduce32.Pre",
            "1",
        ),
        Class::Scan => ("Ptx.Auto.Scan32", "Scan32.Correct", "Scan32.Pre", "A₀.n.toNat"),
    };
    let mut s = String::new();
    writeln!(
        s,
        "/-\n{}\n-/\nimport {import}\nimport Ptx.Logic.Schedule\n\n\
         set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n\
         namespace E5rCheck\nopen Ptx Ptx.Auto Ptx.Auto.Block\n",
        header.trim_end()
    )
    .unwrap();
    s.push_str(&e5r_ptx::lean::kernel_def(k));
    s.push_str(&super::block::spec_text(sp));
    let mut shf = String::from("0");
    for (n, a) in w.sh.iter().rev() {
        shf = format!(
            "if v = {} then {} else {shf}",
            serde_json::to_string(n).unwrap(),
            bv(*a as u128, 64)
        );
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
        "def A₀ : Block.Args spec where\n  G := {}\n  B := {}\n  j := {}\n  n := {}\n  x := {}\n  out := {}\n  sh := fun v => {shf}\n\n\
         def m₀ : Mem := fun x => {mem}\n\n\
         abbrev L₀ : Launch := A₀.launch {len}\n\
         def c₀ : Cfg := Cfg.init (fun _ _ => 0) (fun _ _ => false) m₀ (fun _ _ => 0)\n\
         def tid (c t : BitVec 32) : Tid := ⟨⟨c, 0, 0⟩, ⟨t, 0, 0⟩⟩\n\n\
         theorem pre : {pre} {kn}{} A₀ := by\n  unfold {pre} LayoutOk Fits\n  decide +kernel\n",
        bv(w.g as u128, 32),
        bv(w.b as u128, 32),
        w.j,
        bv(w.n as u128, 32),
        bv(w.x as u128, 64),
        bv(w.out as u128, 64),
        if sp.class == Class::Scan {
            String::new()
        } else {
            format!(" {len}")
        },
    )
    .unwrap();
    writeln!(
        s,
        "theorem refuted : ¬ {correct} spec {kn} := by\n  intro h\n  \
         obtain ⟨hnf, -, -, hrf, -, hfin⟩ := h A₀ pre m₀ (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => false)"
    )
    .unwrap();
    match wit {
        Witness::Fault { sched: cs, .. } => {
            writeln!(
                s,
                "  obtain ⟨c, hr, hf⟩ := exec_any (K := {kn}) (L := L₀) (c₀ := c₀) (p := faultsB {kn} L₀)\n    \
                 (cs := {}) (by decide +kernel)\n  exact hnf c hr (faultsB_spec hf)",
                sched(cs)
            )
            .unwrap();
        }
        Witness::Race {
            s1, s2, t, u, byte, ..
        } => {
            writeln!(
                s,
                "  exact hrf (race_of_exec (K := {kn}) (L := L₀) (c₀ := c₀) (t := {}) (u := {}) (b := {})\n    \
                 (cs₁ := {}) (cs₂ := {}) (by decide +kernel))",
                tid(*t),
                tid(*u),
                bv(*byte as u128, 64),
                sched(s1),
                sched(s2)
            )
            .unwrap();
        }
        Witness::Wrong {
            sched: cs, check, ..
        } => {
            let (lhs, rhs, proj, arg) = match (sp.class, check) {
                (Class::Reduce, Check::Value(i)) => (
                    format!("rd32 c.mem (elem A₀.out {i})"),
                    format!("accUpTo (fun i => A₀.seg m₀ {i} i) A₀.B.toNat"),
                    ".1",
                    format!(" {i} (by decide +kernel)"),
                ),
                (Class::Scan, Check::Value(i)) => (
                    format!("rd32 c.mem (elem A₀.out {i})"),
                    format!(
                        "accUpTo (fun j => rd32 m₀ (elem A₀.x ({i} / A₀.B.toNat * A₀.B.toNat + j))) ({i} % A₀.B.toNat + 1)"
                    ),
                    ".1",
                    format!(" {i} (by decide +kernel)"),
                ),
                (Class::ReduceAtomic, Check::Value(_)) => (
                    "rd32 c.mem A₀.out".to_string(),
                    "rd32 m₀ A₀.out + accUpTo (fun i => if i < A₀.n.toNat then rd32 m₀ (elem A₀.x i) else 0) \
                     (A₀.G.toNat * A₀.B.toNat)"
                        .to_string(),
                    ".1",
                    String::new(),
                ),
                (_, Check::Frame(a)) => (
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
    s
}
