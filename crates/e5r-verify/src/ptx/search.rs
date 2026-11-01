//! Counterexample search with the concrete interpreter (untrusted; every
//! witness is replayed in Lean before it is reported).
//!
//! Small launches run every thread: alone from the initial memory (faults,
//! and pairs of conflicting accesses, which are races in the model because
//! each solo prefix is a reachable interleaving), then one after another to
//! the end (a wrong element or a changed byte outside the output). Launches
//! at the edge of the spec's claimed range are too large to run whole; there
//! the search runs chosen threads alone (the last ones, those around `2^31`
//! and `2^32`, and the owners of every element they touch) and looks for
//! faults and races.

use super::spec::{Sched, Spec};
use e5r_ptx::ast::Kernel;
use e5r_ptx::interp::{self, Access, Ctx, Dim3, End, Mem, Region};
use std::collections::{BTreeMap, HashMap};

/// A concrete launch and initial memory, inside the spec's `Pre`.
#[derive(Clone, Debug)]
pub struct World {
    pub g: u32,
    pub b: u32,
    pub n: u32,
    pub bases: Vec<(String, u64)>,
    pub scalars: Vec<(String, u32)>,
    pub mem: Mem,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Check {
    Value { index: u64 },
    Frame { byte: u64 },
}

/// Threads are `(ctaid.x, tid.x)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Witness {
    /// Thread `t`, alone, faults after `steps` legal steps.
    Fault {
        t: (u32, u32),
        steps: usize,
        why: String,
    },
    /// After `j` solo steps `t` is about to access, and after `i` solo steps
    /// `u` is about to access, a common `byte`, one of them storing.
    Race {
        t: (u32, u32),
        j: usize,
        x: Access,
        u: (u32, u32),
        i: usize,
        y: Access,
        byte: u64,
    },
    /// The threads run one after another (`steps` each) to the end, and the
    /// final memory breaks the spec.
    Wrong {
        order: Vec<((u32, u32), usize)>,
        check: Check,
    },
}

impl Witness {
    pub fn kind(&self) -> &'static str {
        match self {
            Witness::Fault { .. } => "fault",
            Witness::Race { .. } => "race",
            Witness::Wrong {
                check: Check::Value { .. },
                ..
            } => "wrong_value",
            Witness::Wrong {
                check: Check::Frame { .. },
                ..
            } => "frame",
        }
    }
}

const FUEL: usize = 20_000;

impl World {
    fn regions(&self) -> Vec<Region> {
        self.bases
            .iter()
            .map(|(_, b)| Region {
                base: *b,
                size: 4 * self.n as u128,
            })
            .collect()
    }
    fn ctx(&self, sp: &Spec, t: (u32, u32)) -> Ctx {
        let mut params = HashMap::new();
        for (a, b) in &self.bases {
            params.insert(a.clone(), *b);
        }
        for (a, v) in &self.scalars {
            params.insert(a.clone(), *v as u64);
        }
        params.insert(sp.length.clone(), self.n as u64);
        Ctx {
            tid: Dim3 { x: t.1, y: 0, z: 0 },
            ntid: Dim3 {
                x: self.b,
                y: 1,
                z: 1,
            },
            ctaid: Dim3 { x: t.0, y: 0, z: 0 },
            nctaid: Dim3 {
                x: self.g,
                y: 1,
                z: 1,
            },
            params,
        }
    }
    fn base(&self, a: &str) -> u64 {
        self.bases.iter().find(|(x, _)| x == a).unwrap().1
    }
    fn threads(&self) -> Vec<(u32, u32)> {
        (0..self.g)
            .flat_map(|c| (0..self.b).map(move |t| (c, t)))
            .collect()
    }
}

fn solo(k: &Kernel, sp: &Spec, w: &World, t: (u32, u32)) -> (End, Vec<(usize, Access)>) {
    let al = w.regions();
    let c = w.ctx(sp, t);
    let mut m = w.mem.clone();
    let mut s = interp::TState::default();
    let mut acc = Vec::new();
    for i in 0..FUEL {
        match interp::step(k, &al, &c, &mut s, &mut m) {
            interp::Res::Ok(a) => acc.extend(a.map(|a| (i, a))),
            interp::Res::Halted => return (End::Halted(i), acc),
            interp::Res::Fault(why) => return (End::Fault(i, why), acc),
        }
    }
    (End::OutOfFuel, acc)
}

fn conflict(x: &Access, y: &Access) -> Option<u64> {
    if !(x.2 || y.2) {
        return None;
    }
    let lo = x.0.max(y.0) as u128;
    let hi = (x.0 as u128 + x.1 as u128).min(y.0 as u128 + y.1 as u128);
    (lo < hi).then_some(lo as u64)
}

/// Faults and races among the given threads' solo runs.
fn solo_witness(k: &Kernel, sp: &Spec, w: &World, ts: &[(u32, u32)]) -> Option<Witness> {
    let mut logs = Vec::new();
    for &t in ts {
        let (end, acc) = solo(k, sp, w, t);
        if let End::Fault(steps, why) = end {
            return Some(Witness::Fault { t, steps, why });
        }
        logs.push((t, acc));
    }
    for (a, (t, la)) in logs.iter().enumerate() {
        for (u, lb) in logs.iter().skip(a + 1) {
            for (j, x) in la {
                for (i, y) in lb {
                    if let Some(byte) = conflict(x, y) {
                        return Some(Witness::Race {
                            t: *t,
                            j: *j,
                            x: *x,
                            u: *u,
                            i: *i,
                            y: *y,
                            byte,
                        });
                    }
                }
            }
        }
    }
    None
}

fn sequential(k: &Kernel, sp: &Spec, w: &World) -> Option<Witness> {
    let al = w.regions();
    let mut m = w.mem.clone();
    let mut order = Vec::new();
    for t in w.threads() {
        let c = w.ctx(sp, t);
        match interp::run_solo(k, &al, &c, &mut m, FUEL) {
            (End::Halted(steps), _) => order.push((t, steps)),
            _ => return None, // faults were looked for already; fuel: unknown
        }
    }
    let out = w.base(&sp.output);
    let el = |m: &Mem, a: &str, i: u64| m.rd(w.base(a).wrapping_add(4 * i), 4) as u32;
    for i in 0..w.n as u64 {
        let want = sp.element.eval(&|a| el(&w.mem, a, i), &|s| {
            w.scalars
                .iter()
                .find(|(x, _)| x == s)
                .map_or(0, |(_, v)| *v)
        });
        if m.rd(out.wrapping_add(4 * i), 4) as u32 != want {
            return Some(Witness::Wrong {
                order,
                check: Check::Value { index: i },
            });
        }
    }
    let lo = out;
    let hi = out as u128 + 4 * w.n as u128;
    let mut changed: Vec<u64> = m
        .bytes
        .iter()
        .filter(|(a, v)| {
            w.mem.get(**a) != **v && !((lo as u128) <= **a as u128 && (**a as u128) < hi)
        })
        .map(|(a, _)| *a)
        .collect();
    changed.sort();
    changed.first().map(|b| Witness::Wrong {
        order,
        check: Check::Frame { byte: *b },
    })
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

fn small_world(sp: &Spec, g: u32, b: u32, n: u32, alias: bool, rng: &mut Rng) -> World {
    let mut bases = Vec::new();
    let mut next = 0x10000u64;
    let mut shared = None;
    for a in &sp.arrays {
        let base = if alias && *a != sp.output {
            *shared.get_or_insert_with(|| {
                next += 0x10000;
                next
            })
        } else {
            next += 0x10000;
            next
        };
        bases.push((a.clone(), base));
    }
    let mut mem = Mem::default();
    for (_, base) in &bases {
        for i in 0..n as u64 {
            mem.wr(base + 4 * i, 4, rng.next() & 0xffff_ffff);
        }
    }
    let scalars = sp
        .scalars
        .iter()
        .map(|s| (s.clone(), (rng.next() & 0xffff) as u32 | 2))
        .collect();
    World {
        g,
        b,
        n,
        bases,
        scalars,
        mem,
    }
}

fn in_range(sp: &Spec, g: u32, b: u32, n: u32) -> bool {
    let (gb, n) = (g as u128 * b as u128, n as u128);
    match sp.sched {
        Sched::Guarded { max_threads } => n <= gb && gb <= max_threads,
        Sched::Stride { bound, .. } => n + gb <= bound,
    }
}

/// Look for a counterexample; returns the first one found and how many
/// launches were tried.
pub fn search(k: &Kernel, sp: &Spec) -> (Option<(World, Witness)>, usize) {
    let mut rng = Rng(0x5eed_1234_abcd_ef01);
    let mut tried = 0;
    let shapes = [
        (1, 1),
        (1, 2),
        (2, 1),
        (2, 2),
        (1, 3),
        (3, 1),
        (1, 4),
        (2, 3),
    ];
    for &(g, b) in &shapes {
        for n in [0u32, 1, 2, 3, 4, 5, 7] {
            if !in_range(sp, g, b, n) {
                continue;
            }
            for alias in [false, true] {
                if alias && sp.arrays.len() < 3 {
                    continue;
                }
                tried += 1;
                let w = small_world(sp, g, b, n, alias, &mut rng);
                if let Some(x) = solo_witness(k, sp, &w, &w.threads()) {
                    return (Some((w, x)), tried);
                }
                if let Some(x) = sequential(k, sp, &w) {
                    return (Some((w, x)), tried);
                }
            }
        }
    }
    for w in edge_worlds(sp) {
        tried += 1;
        let s = w.g as u64 * w.b as u64;
        let mut gids: Vec<u64> = [
            0,
            1,
            s - 1,
            s.saturating_sub(2),
            1 << 31,
            (1 << 31) - 1,
            (1 << 31) + 1,
        ]
        .into_iter()
        .filter(|g| *g < s)
        .collect();
        // the owners of everything the chosen threads touch
        let out = w.base(&sp.output);
        for _ in 0..2 {
            let ts: Vec<(u32, u32)> = gids
                .iter()
                .map(|g| ((g / w.b as u64) as u32, (g % w.b as u64) as u32))
                .collect();
            for t in &ts {
                let (_, acc) = solo(k, sp, &w, *t);
                for (_, a) in acc {
                    if a.0 >= out && ((a.0 - out) / 4) < w.n as u64 {
                        let owner = ((a.0 - out) / 4) % s;
                        if !gids.contains(&owner) {
                            gids.push(owner);
                        }
                    }
                }
            }
        }
        gids.sort();
        gids.dedup();
        let ts: Vec<(u32, u32)> = gids
            .iter()
            .map(|g| ((g / w.b as u64) as u32, (g % w.b as u64) as u32))
            .collect();
        if let Some(x) = solo_witness(k, sp, &w, &ts) {
            return (Some((w, x)), tried);
        }
    }
    (None, tried)
}

/// Launches at the top of the claimed range, with the arrays far apart and
/// zero memory.
fn edge_worlds(sp: &Spec) -> Vec<World> {
    let mut v = Vec::new();
    let mk = |g: u32, b: u32, n: u32| {
        let bases = sp
            .arrays
            .iter()
            .enumerate()
            .map(|(i, a)| (a.clone(), (i as u64 + 1) << 36))
            .collect();
        let scalars = sp.scalars.iter().map(|s| (s.clone(), 3)).collect();
        World {
            g,
            b,
            n,
            bases,
            scalars,
            mem: Mem::default(),
        }
    };
    let cands: [(u32, u32); 4] = [
        (1 << 16, 1 << 15),
        ((1 << 16) + 1, 1 << 15),
        (1 << 16, (1 << 16) - 1),
        (65535, 65535),
    ];
    for (g, b) in cands {
        let gb = g as u128 * b as u128;
        for n in [
            gb.min(u32::MAX as u128) as u32,
            u32::MAX,
            (gb as u32).wrapping_sub(1),
            1 << 31,
        ] {
            if in_range(sp, g, b, n) {
                v.push(mk(g, b, n));
            }
        }
    }
    v
}

pub fn describe(w: &World, x: &Witness) -> serde_json::Value {
    let bases: BTreeMap<_, _> = w
        .bases
        .iter()
        .map(|(a, b)| (a.clone(), format!("{b:#x}")))
        .collect();
    let scalars: BTreeMap<_, _> = w.scalars.iter().cloned().collect();
    let detail = match x {
        Witness::Fault { t, steps, why } => serde_json::json!({
            "thread": {"ctaid": t.0, "tid": t.1}, "after_steps": steps, "fault": why }),
        Witness::Race {
            t, j, u, i, byte, ..
        } => serde_json::json!({
            "first": {"ctaid": t.0, "tid": t.1, "after_steps": j},
            "second": {"ctaid": u.0, "tid": u.1, "after_steps": i}, "byte": format!("{byte:#x}") }),
        Witness::Wrong { order, check } => serde_json::json!({
            "schedule": order.iter().map(|(t, s)| serde_json::json!({"ctaid": t.0, "tid": t.1, "steps": s})).collect::<Vec<_>>(),
            "check": match check {
                Check::Value { index } => serde_json::json!({"element": index}),
                Check::Frame { byte } => serde_json::json!({"byte_changed_outside_output": format!("{byte:#x}")}),
            } }),
    };
    serde_json::json!({
        "kind": x.kind(),
        "launch": {"grid": [w.g, 1, 1], "block": [w.b, 1, 1], "n": w.n, "bases": bases, "scalars": scalars},
        "initial_registers": "zero",
        "detail": detail,
    })
}
