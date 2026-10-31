/-
Grid execution: every thread of every CTA, interleaved over shared global
memory.

`Step` picks any thread that can step and runs one of its instructions, so the
executions of a launch are all interleavings of its threads at instruction
granularity. Warps are not scheduled in lockstep and no fairness is assumed:
this is a superset of the schedules a GPU can produce for the subset (no
barriers, atomics, shared memory or warp-level instructions).

The interleaving model is sequentially consistent. PTX's memory model is
weaker, but for programs without data races (no two conflicting accesses from
different threads that are not ordered by synchronization) the PTX model
gives sequentially consistent results, so race freedom proved here is what
licenses reading the remaining results in this model. That transfer is an
assumption about NVIDIA's model, recorded in docs/verification-ptx.md, not a
theorem of this development.
-/
import Ptx.Semantics.Instruction

namespace Ptx

/-- A thread: its CTA index and its index inside the CTA. -/
structure Tid where
  ctaid : Dim3
  tid : Dim3
  deriving Repr, DecidableEq, Inhabited

structure Launch where
  grid : Dim3
  block : Dim3
  params : String → Val
  alloc : List Region

def Launch.ctx (L : Launch) (t : Tid) : Ctx :=
  { tid := t.tid, ntid := L.block, ctaid := t.ctaid, nctaid := L.grid, params := L.params }

/-- Indices `0 .. n-1` of one dimension. -/
def range32 (n : BitVec 32) : List (BitVec 32) := (List.range n.toNat).map (BitVec.ofNat 32)

def dims (v : Dim3) : List Dim3 :=
  (range32 v.z).flatMap fun z => (range32 v.y).flatMap fun y =>
    (range32 v.x).map fun x => { x, y, z }

/-- Every thread of the launch. -/
def Launch.threads (L : Launch) : List Tid :=
  (dims L.grid).flatMap fun c => (dims L.block).map fun t => { ctaid := c, tid := t }

def Launch.Thread (L : Launch) (t : Tid) : Prop :=
  t.ctaid.x.toNat < L.grid.x.toNat ∧ t.ctaid.y.toNat < L.grid.y.toNat ∧
  t.ctaid.z.toNat < L.grid.z.toNat ∧ t.tid.x.toNat < L.block.x.toNat ∧
  t.tid.y.toNat < L.block.y.toNat ∧ t.tid.z.toNat < L.block.z.toNat

theorem mem_range32 {n i : BitVec 32} : i ∈ range32 n ↔ i.toNat < n.toNat := by
  simp only [range32, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    simp only [BitVec.toNat_ofNat]
    have := n.isLt; rw [Nat.mod_eq_of_lt (by omega)]; exact hk
  · intro h; exact ⟨i.toNat, h, by simp⟩

theorem mem_dims {v d : Dim3} :
    d ∈ dims v ↔ d.x.toNat < v.x.toNat ∧ d.y.toNat < v.y.toNat ∧ d.z.toNat < v.z.toNat := by
  rcases d with ⟨x, y, z⟩
  simp only [dims, List.mem_flatMap, List.mem_map, mem_range32]
  constructor
  · rintro ⟨z', hz, y', hy, x', hx, h⟩
    cases h; exact ⟨hx, hy, hz⟩
  · rintro ⟨hx, hy, hz⟩; exact ⟨z, hz, y, hy, x, hx, rfl⟩

theorem mem_threads {L : Launch} {t : Tid} : t ∈ L.threads ↔ L.Thread t := by
  rcases t with ⟨c, d⟩
  simp only [Launch.threads, List.mem_flatMap, List.mem_map, mem_dims, Launch.Thread]
  constructor
  · rintro ⟨c', hc, d', hd, h⟩
    cases h; exact ⟨hc.1, hc.2.1, hc.2.2, hd.1, hd.2.1, hd.2.2⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩; exact ⟨c, ⟨h1, h2, h3⟩, d, ⟨h4, h5, h6⟩, rfl⟩

structure Cfg where
  ts : Tid → TState
  mem : Mem

/-- Initial configuration. Register contents `r0`/`p0` are arbitrary. -/
def Cfg.init (r0 : Tid → String → Val) (p0 : Tid → String → Bool) (m0 : Mem) : Cfg :=
  { ts := fun t => { pc := 0, r := r0 t, p := p0 t }, mem := m0 }

def updT (f : Tid → TState) (t : Tid) (s : TState) : Tid → TState :=
  fun u => if u = t then s else f u

section
variable (K : Kernel) (L : Launch)

def Cfg.res (c : Cfg) (t : Tid) : Res := stepMem K L.alloc (L.ctx t) (c.ts t) c.mem

/-- One instruction of one thread. -/
def Step (c c' : Cfg) : Prop :=
  ∃ t ∈ L.threads, ∃ s' m', c.res K L t = .ok s' m' ∧ c' = { ts := updT c.ts t s', mem := m' }

inductive Reach : Cfg → Cfg → Prop
  | refl (c : Cfg) : Reach c c
  | tail {c₁ c₂ c₃ : Cfg} : Reach c₁ c₂ → Step K L c₂ c₃ → Reach c₁ c₃

/-- `n` steps. -/
inductive Steps : Nat → Cfg → Cfg → Prop
  | refl (c : Cfg) : Steps 0 c c
  | tail {n : Nat} {c₁ c₂ c₃ : Cfg} : Steps n c₁ c₂ → Step K L c₂ c₃ → Steps (n + 1) c₁ c₃

/-- Some thread faults: an out-of-bounds or misaligned access, an unsupported
form, a missing label, or running off the end of the body. -/
def Faults (c : Cfg) : Prop := ∃ t ∈ L.threads, c.res K L t = .fault

/-- Every thread has executed `ret`/`exit`. -/
def Done (c : Cfg) : Prop := ∀ t ∈ L.threads, c.res K L t = .halted

/-- The access thread `t` is about to make. -/
def Cfg.pending (c : Cfg) (t : Tid) : Option (Addr × Size × Bool) :=
  (action K (L.ctx t) (c.ts t)).acc

/-- Two accesses conflict: they share a byte and at least one is a store. -/
def Conflict (x y : Addr × Size × Bool) : Prop :=
  (x.2.2 = true ∨ y.2.2 = true) ∧ ∃ b, covers x.1 x.2.1.bytes b ∧ covers y.1 y.2.1.bytes b

/-- No access any thread makes in any execution conflicts with an access of a
different thread in any execution. There is no synchronization in the subset,
so this is data-race freedom (and stronger than requiring the two accesses to
be simultaneously enabled in one execution). -/
def RaceFree (c₀ : Cfg) : Prop :=
  ∀ c₁ c₂, Reach K L c₀ c₁ → Reach K L c₀ c₂ → ∀ t ∈ L.threads, ∀ u ∈ L.threads, t ≠ u →
    ∀ x y, c₁.pending K L t = some x → c₂.pending K L u = some y → ¬ Conflict x y

end

theorem Reach.of_steps {K L} {n : Nat} {c c' : Cfg} (h : Steps K L n c c') : Reach K L c c' := by
  induction h with
  | refl => exact .refl _
  | tail _ hs ih => exact .tail ih hs

theorem Reach.steps {K L} {c c' : Cfg} (h : Reach K L c c') : ∃ n, Steps K L n c c' := by
  induction h with
  | refl => exact ⟨0, .refl _⟩
  | tail _ hs ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, .tail hn hs⟩

end Ptx
