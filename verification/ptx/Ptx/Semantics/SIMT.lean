/-
Grid execution: every thread of every CTA, interleaved over global memory and
the shared memory of its CTA, with CTA-wide barriers.

`Step` either picks any thread that can step and runs one of its
instructions, or releases a CTA whose threads all wait at the same `bar.sync`.
The executions of a launch are therefore all interleavings of its threads at
instruction granularity that respect the barriers. Warps are not scheduled in
lockstep and no fairness is assumed: this is a superset of the schedules a GPU
can produce for the subset.

`bar.sync` is `barrier.sync.aligned`: every thread of the CTA must reach the
same barrier instruction (PTX ISA, `bar`). A CTA in which one thread waits
while another has finished, or waits at a different `bar.sync`, can never be
released; the model counts that as a fault (`Diverged`). The GPU waits only
for threads that have not exited, so it runs some kernels the model refuses;
the model is stricter, never more lenient.

`Cfg.ph` counts the barriers each CTA has passed. It does not influence
execution; it is the phase that `RaceFree` is relative to.

The interleaving model is sequentially consistent and PTX's memory model is
weaker. What licenses reading results in this model is the form of race
freedom proved here: two different threads never make conflicting accesses
unless both are atomics on the same location, or they are in one CTA and a
barrier separates them (different phases). That under the PTX axioms such
a program behaves as in the interleaving model is an assumption about
NVIDIA's model (PTX ISA §8), recorded in docs/verification-ptx.md, not a
theorem of this development.
-/
import Ptx.Semantics.Instruction

namespace Ptx

/-- A thread: its CTA index and its index inside the CTA. -/
structure Tid where
  ctaid : Dim3
  tid : Dim3
  deriving Repr, DecidableEq, Inhabited

/-- A launch: the shape, the parameter values, the global allocations, and
where each `.shared` variable is placed in the shared window (the same in
every CTA). -/
structure Launch where
  grid : Dim3
  block : Dim3
  params : String → Val
  alloc : List Region
  shared : String → Addr := fun _ => 0
  /-- The bits of every NaN a floating-point instruction produces, as a
  function of the thread and its state (PTX leaves them unspecified;
  `Ptx/Semantics/Float.lean`). Theorems about float kernels quantify over
  it; integer instructions never read it. -/
  nan : Tid → TState → Val := fun _ _ => 0

def Launch.ctx (L : Launch) (t : Tid) : Ctx :=
  { tid := t.tid, ntid := L.block, ctaid := t.ctaid, nctaid := L.grid, params := L.params,
    sym := L.shared, nan := L.nan t }

/-- The shared variables of `K` as placed by the launch. -/
def Launch.sregions (L : Launch) (K : Kernel) : List Region :=
  K.shared.map fun v => ⟨L.shared v.name, v.size⟩

/-- The allocations of each space. -/
def Launch.allocs (L : Launch) (K : Kernel) : Sp → List Region
  | .global => L.alloc
  | .shared => L.sregions K

@[simp] theorem Launch.allocs_global (L : Launch) (K : Kernel) : L.allocs K .global = L.alloc := rfl
@[simp] theorem Launch.allocs_shared (L : Launch) (K : Kernel) : L.allocs K .shared = L.sregions K := rfl

/-- A placement ptxas could choose: each shared variable aligned as declared,
inside the 32-bit shared window, and no two overlapping. Theorems about
kernels with `.shared` variables assume this and nothing more about where
the variables are. -/
def LayoutOk (K : Kernel) (sh : String → Addr) : Prop :=
  (∀ v ∈ K.shared, (sh v.name).toNat % v.align = 0 ∧ (sh v.name).toNat + v.size ≤ 2 ^ 32) ∧
  K.shared.Pairwise fun v w =>
    (sh v.name).toNat + v.size ≤ (sh w.name).toNat ∨ (sh w.name).toNat + w.size ≤ (sh v.name).toNat

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
  /-- The shared memory of each CTA. -/
  sh : Dim3 → Mem
  /-- How many barriers each CTA has passed. -/
  ph : Dim3 → Nat

/-- Initial configuration. Register contents `r0`/`p0` and shared memory
`sh0` are arbitrary. -/
def Cfg.init (r0 : Tid → String → Val) (p0 : Tid → String → Bool) (m0 : Mem) (sh0 : Dim3 → Mem) :
    Cfg :=
  { ts := fun t => { pc := 0, r := r0 t, p := p0 t }, mem := m0, sh := sh0, ph := fun _ => 0 }

def updT (f : Tid → TState) (t : Tid) (s : TState) : Tid → TState :=
  fun u => if u = t then s else f u

def updC (f : Dim3 → Mem) (b : Dim3) (m : Mem) : Dim3 → Mem :=
  fun d => if d = b then m else f d

/-- What a thread of CTA `b` sees. -/
def Cfg.heap (c : Cfg) (b : Dim3) : Heap := ⟨c.mem, c.sh b⟩

/-- Thread `t` moves to `s` and leaves its view of memory as `h`. -/
def Cfg.write (c : Cfg) (t : Tid) (s : TState) (h : Heap) : Cfg :=
  { c with ts := updT c.ts t s, mem := h.g, sh := updC c.sh t.ctaid h.s }

/-- Every thread of CTA `b` passes its barrier. -/
def Cfg.release (c : Cfg) (b : Dim3) : Cfg :=
  { c with ts := fun t => if t.ctaid = b then (c.ts t).skip else c.ts t,
           ph := fun d => if d = b then c.ph d + 1 else c.ph d }

section
variable (K : Kernel) (L : Launch)

def Cfg.res (c : Cfg) (t : Tid) : TRes := tstep K (L.allocs K) (L.ctx t) (c.ts t) (c.heap t.ctaid)

/-- CTA `b` has a thread, and all its threads wait at the same `bar.sync`. -/
def BarReady (c : Cfg) (b : Dim3) : Prop :=
  (∃ t ∈ L.threads, t.ctaid = b) ∧
    ∃ pc, ∀ t ∈ L.threads, t.ctaid = b → c.res K L t = .wait ∧ (c.ts t).pc = pc

/-- One instruction of one thread, or the release of one CTA's barrier. -/
def Step (c c' : Cfg) : Prop :=
  (∃ t ∈ L.threads, ∃ s' h', c.res K L t = .ok s' h' ∧ c' = c.write t s' h') ∨
  (∃ b, BarReady K L c b ∧ c' = c.release b)

inductive Reach : Cfg → Cfg → Prop
  | refl (c : Cfg) : Reach c c
  | tail {c₁ c₂ c₃ : Cfg} : Reach c₁ c₂ → Step K L c₂ c₃ → Reach c₁ c₃

/-- `n` steps. -/
inductive Steps : Nat → Cfg → Cfg → Prop
  | refl (c : Cfg) : Steps 0 c c
  | tail {n : Nat} {c₁ c₂ c₃ : Cfg} : Steps n c₁ c₂ → Step K L c₂ c₃ → Steps (n + 1) c₁ c₃

/-- A thread waits at a barrier that cannot complete: another thread of its
CTA has finished, or waits at a different `bar.sync`. -/
def Diverged (c : Cfg) : Prop :=
  ∃ t ∈ L.threads, ∃ u ∈ L.threads, t.ctaid = u.ctaid ∧ c.res K L t = .wait ∧
    (c.res K L u = .halted ∨ (c.res K L u = .wait ∧ (c.ts u).pc ≠ (c.ts t).pc))

/-- Some thread faults (an out-of-bounds or misaligned access, an unsupported
form, a missing label, running off the end of the body), or a barrier has
diverged. -/
def Faults (c : Cfg) : Prop := (∃ t ∈ L.threads, c.res K L t = .fault) ∨ Diverged K L c

/-- Every thread has executed `ret`/`exit`. -/
def Done (c : Cfg) : Prop := ∀ t ∈ L.threads, c.res K L t = .halted

/-- The access thread `t` is about to make. -/
def Cfg.pending (c : Cfg) (t : Tid) : Option Acc :=
  (action K (L.ctx t) (c.ts t)).acc

end

/-- Access `x` of thread `t` and access `y` of thread `u` conflict: the same
space (and, for shared memory, the same CTA), a common byte, and at least
one of them writes. -/
def Conflict (t : Tid) (x : Acc) (u : Tid) (y : Acc) : Prop :=
  x.sp = y.sp ∧ (x.sp = .shared → t.ctaid = u.ctaid) ∧ (x.kind ≠ .read ∨ y.kind ≠ .read) ∧
    ∃ b, covers x.a x.sz.bytes b ∧ covers y.a y.sz.bytes b

section
variable (K : Kernel) (L : Launch)

/-- For any two configurations of any two executions, the pending accesses of
two different threads either do not conflict, or are atomics on exactly the
same location, or belong to one CTA in different phases (a `bar.sync`
separates them in every execution that makes both). This implies PTX's
data-race freedom (ISA §8.7.1: conflicting accesses neither morally strong nor
ordered by causality): atomics on one location are morally strong, and the
barrier orders the accesses of its CTA. -/
def RaceFree (c₀ : Cfg) : Prop :=
  ∀ c₁ c₂, Reach K L c₀ c₁ → Reach K L c₀ c₂ → ∀ t ∈ L.threads, ∀ u ∈ L.threads, t ≠ u →
    ∀ x y, c₁.pending K L t = some x → c₂.pending K L u = some y → Conflict t x u y →
      (x.kind = .atomic ∧ y.kind = .atomic ∧ x.a = y.a ∧ x.sz = y.sz) ∨
      (t.ctaid = u.ctaid ∧ c₁.ph t.ctaid ≠ c₂.ph u.ctaid)

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
