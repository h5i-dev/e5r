/-
M3: the elementwise-map class, stated once and proved once.

A `MapSpec` is what a model writes next to its PTX: which `.u64` parameters
are arrays of 32-bit elements, which one is the output, which `.u32`
parameter is the length `n`, which `.u32` parameters are scalars, the value
`f` every output element must hold (a function of the scalars and of the
elements at the same index, read from the initial memory), and the schedule:

* `guarded mx`: thread `gid` handles element `gid` when `gid < n`; the launch
  must have `n ≤ G·B ≤ mx` threads (`mx` is where the kernel's index
  arithmetic stops being exact, e.g. `2^31` for a signed 32-bit index);
* `stride bd`: a grid-stride loop, thread `gid` handles `gid, gid + G·B, …`;
  the launch must have `n + G·B ≤ bd` (`2^64` for a 64-bit index, `2^32` or
  `2^31` for a 32-bit one).

`MapSpec.Correct K` is the theorem a check proves: for every 1-D launch that
meets `Pre` (arrays fit in the address space, are 4-byte aligned, the output
overlaps no other array, the launch is in the schedule's range), every
initial memory, every initial register content and every interleaving, the
six clauses of `vadd_correct` and `saxpy_correct` hold.

`correct_of_threadOk` reduces it to one obligation per thread, `ThreadOk`:
thread `g` alone, from the initial memory, reaches `ret` with every access
legal, loads only at its own indices `i ≡ g (mod G·B)` of the arrays, stores
only at its own indices of the output, and leaves `f` at each of them. That
obligation is what the `ptx_map` tactics discharge (Ptx/Auto/Tactic.lean).
-/
import Ptx.Logic.Launch1D
import Ptx.Tactics.Eval

namespace Ptx.Auto
open Ptx

inductive Sched where
  | guarded (maxThreads : Nat)
  | stride (bound : Nat)
  deriving Repr, DecidableEq

structure MapSpec where
  arrays : List String
  out : String
  len : String
  scalars : List String
  f : (String → BitVec 32) → (String → BitVec 32) → BitVec 32
  sched : Sched
  /-- How an output element is compared with `f`: equality, or for float
  maps `Fp.feq32` (equal bits, or both NaN; `Ptx/Auto/FloatMap.lean`). -/
  rel : BitVec 32 → BitVec 32 → Prop := fun a b => a = b

/-- The launch-time values a theorem quantifies over. -/
structure Args where
  G : BitVec 32
  B : BitVec 32
  n : BitVec 32
  base : String → Addr
  sc : String → BitVec 32
  /-- The NaN oracle of the launch (`Launch.nan`); integer kernels never read it. -/
  nan : Tid → TState → Val := fun _ _ => 0

namespace MapSpec
variable (S : MapSpec) (A : Args)

/-- Parameter values: array bases, the length and the scalars, `.u32`
parameters zero-extended. A parameter the spec does not name reads as 0;
the checker refuses kernels that have one. -/
def params : String → Val := fun p =>
  if p ∈ S.arrays then A.base p else if p = S.len then ext32 A.n
  else if p ∈ S.scalars then ext32 (A.sc p) else 0

def launch : Launch :=
  { grid := ⟨A.G, 1, 1⟩, block := ⟨A.B, 1, 1⟩, params := S.params A,
    alloc := S.arrays.map fun a => ⟨A.base a, 4 * A.n.toNat⟩, nan := A.nan }

/-- Two arrays of `N` elements share no byte. -/
def Sep (a b : Addr) (N : Nat) : Prop := a.toNat + 4 * N ≤ b.toNat ∨ b.toNat + 4 * N ≤ a.toNat

def SchedOk : Sched → Prop
  | .guarded mx => A.n.toNat ≤ A.G.toNat * A.B.toNat ∧ A.G.toNat * A.B.toNat ≤ mx
  | .stride bd => A.n.toNat + A.G.toNat * A.B.toNat ≤ bd

def Pre : Prop :=
  S.out ∈ S.arrays ∧
  (∀ a ∈ S.arrays, Fits (A.base a) A.n.toNat ∧ (A.base a).toNat % 4 = 0) ∧
  (∀ a ∈ S.arrays, a ≠ S.out → Sep (A.base a) (A.base S.out) A.n.toNat) ∧
  SchedOk A S.sched

/-- The value output element `i` must hold, from the initial memory. -/
def val (m₀ : Mem) (i : Nat) : BitVec 32 := S.f A.sc fun a => rd32 m₀ (elem (A.base a) i)

/-- The class statement. The kernel declares no `.shared` variable (so the
launch's placement of them is irrelevant); for every launch in `Pre`, every
initial global memory, shared memory and register content, and every
execution: the clauses below. -/
def Correct (K : Kernel) : Prop :=
  K.shared = [] ∧
  ∀ (A : Args) (m₀ : Mem) (s₀ : Dim3 → Mem) (r₀ : Tid → String → Val) (p₀ : Tid → String → Bool),
    S.Pre A →
    let L := S.launch A
    let c₀ := Cfg.init r₀ p₀ m₀ s₀
    (∀ c, Reach K L c₀ c → ¬ Faults K L c) ∧
    (∀ c, Reach K L c₀ c → Done K L c ∨ ∃ c', Step K L c c') ∧
    (∃ bound, ∀ j c, Steps K L j c₀ c → j ≤ bound) ∧
    RaceFree K L c₀ ∧
    (∃ c, Reach K L c₀ c ∧ Done K L c) ∧
    (∀ c, Reach K L c₀ c → Done K L c → 0 < A.G.toNat * A.B.toNat →
      (∀ i < A.n.toNat, S.rel (rd32 c.mem (elem (A.base S.out) i)) (S.val A m₀ i)) ∧
      (∀ x, (∀ i < A.n.toNat, ¬ covers (elem (A.base S.out) i) 4 x) → c.mem x = m₀ x))

/-- Element `i` belongs to the thread with global index `g`. -/
def Own (g i : Nat) : Prop := i % (A.G.toNat * A.B.toNat) = g

def R (g : Nat) (x : Addr) : Prop :=
  ∃ i < A.n.toNat, Own A g i ∧ ∃ a ∈ S.arrays, covers (elem (A.base a) i) 4 x

def W (g : Nat) (x : Addr) : Prop :=
  ∃ i < A.n.toNat, Own A g i ∧ covers (elem (A.base S.out) i) 4 x

def Post (m₀ : Mem) (g : Nat) (M : Mem) : Prop :=
  ∀ i < A.n.toNat, Own A g i → S.rel (rd32 M (elem (A.base S.out) i)) (S.val A m₀ i)

/-- The per-thread obligation. -/
def ThreadOk (K : Kernel) : Prop :=
  ∀ A, S.Pre A → ∀ (m₀ : Mem), ∀ t ∈ (S.launch A).threads, ∀ (r : String → Val) (p : String → Bool),
    Safe K (S.launch A).alloc ((S.launch A).ctx t) (S.R A (gid A.B t)) (S.W A (gid A.B t))
      (fun s m => action K ((S.launch A).ctx t) s = .done ∧ S.Post A m₀ (gid A.B t) m) ⟨0, r, p⟩ m₀

end MapSpec

theorem launch_oneD (S : MapSpec) (A : Args) : (S.launch A).OneD A.G A.B := ⟨rfl, rfl⟩

theorem mul32_le (x y : BitVec 32) : x.toNat * y.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
  Nat.mul_le_mul (by have := x.isLt; omega) (by have := y.isLt; omega)

theorem thread_facts {S : MapSpec} {A : Args} {t : Tid} (ht : t ∈ (S.launch A).threads) :
    (t.ctaid.x.toNat < A.G.toNat ∧ t.tid.x.toNat < A.B.toNat ∧ t.ctaid.y = 0 ∧ t.ctaid.z = 0 ∧
      t.tid.y = 0 ∧ t.tid.z = 0) ∧ gid A.B t < A.G.toNat * A.B.toNat :=
  ⟨(launch_oneD S A).thread ht, (launch_oneD S A).gid_lt ht⟩

theorem own_unique {A : Args} {g₁ g₂ i : Nat} (h₁ : MapSpec.Own A g₁ i) (h₂ : MapSpec.Own A g₂ i) :
    g₁ = g₂ := by
  unfold MapSpec.Own at h₁ h₂; omega

theorem correct_of_threadOk {S : MapSpec} {K : Kernel} (hsh : K.shared = []) (h : S.ThreadOk K) :
    S.Correct K := by
  refine ⟨hsh, ?_⟩
  intro A m₀ s₀ r₀ p₀ hpre L c₀
  obtain ⟨hout, hfit, hsep, hsch⟩ := hpre
  have h1 := launch_oneD S A
  let SS := A.G.toNat * A.B.toNat
  let N := A.n.toNat
  have hfo := (hfit S.out hout).1
  have hsolo : ∀ t ∈ L.threads, ∃ k, Solo K L.alloc (L.ctx t) (S.R A (gid A.B t))
      (S.W A (gid A.B t)) (s0 r₀ p₀ m₀ t) m₀ k ∧
      S.Post A m₀ (gid A.B t) (trace K L.alloc (L.ctx t) k (s0 r₀ p₀ m₀ t) m₀).2 :=
    fun t ht => (h A ⟨hout, hfit, hsep, hsch⟩ m₀ t ht (r₀ t) (p₀ t)).solo
  have hdisj : ∀ t ∈ L.threads, ∀ u ∈ L.threads, t ≠ u → ∀ x,
      S.W A (gid A.B t) x → ¬ S.R A (gid A.B u) x ∧ ¬ S.W A (gid A.B u) x := by
    intro t ht u hu htu x ⟨i, hi, hoi, hc⟩
    have own_ne : ∀ j, MapSpec.Own A (gid A.B u) j → i ≠ j := by
      intro j hoj hij; subst hij
      exact htu (h1.gid_inj ht hu (own_unique hoi hoj))
    refine ⟨fun ⟨j, hj, hoj, a, ha, hc'⟩ => ?_, fun ⟨j, hj, hoj, hc'⟩ =>
      elem_disjoint hfo hi hj (own_ne j hoj) hc hc'⟩
    by_cases hao : a = S.out
    · subst hao; exact elem_disjoint hfo hi hj (own_ne j hoj) hc hc'
    · have hs := hsep a ha hao
      exact elem_disjoint₂ hfo (hfit a ha).1 (by unfold MapSpec.Sep at hs; omega) hi hj hc hc'
  obtain ⟨bound, g⟩ := grid_sound (R := fun t => S.R A (gid A.B t))
    (W := fun t => S.W A (gid A.B t)) (P := fun t => S.Post A m₀ (gid A.B t)) hsolo hdisj s₀
  refine ⟨g.noFault, g.progress, ⟨bound, g.bounded⟩, g.raceFree, g.exists_done, ?_⟩
  intro cfg hr hd hS
  obtain ⟨hown, hrest⟩ := g.final cfg hr hd
  refine ⟨fun i hi => ?_, fun x hx => hrest x fun t _ ⟨j, hj, _, hc⟩ => hx j hj hc⟩
  have hgi : i % SS < SS := Nat.mod_lt _ hS
  obtain ⟨hm, hg⟩ := h1.owner_mem (i := i % SS) hgi
  obtain ⟨M, hP, hM⟩ := hown _ hm
  have ho : MapSpec.Own A (gid A.B (owner A.B (i % SS))) i := by
    unfold MapSpec.Own; rw [hg]
  rw [rd32_congr fun x hx => hM x ⟨i, hi, ho, hx⟩]
  exact hP i hi ho

end Ptx.Auto

/-! ## Footprint monotonicity and the facts every obligation uses -/

namespace Ptx

theorem InFoot.mono {R W R' W' : Addr → Prop} {acc : Acc}
    (hR : ∀ x, R x → R' x) (hW : ∀ x, W x → W' x) (h : InFoot R W acc) : InFoot R' W' acc :=
  ⟨h.global, h.plain, fun x hx => (h.bytes x hx).imp (hW x) fun ⟨h1, h2⟩ => ⟨h1, hR x h2⟩⟩

theorem Safe.foot_mono {K : Kernel} {al : List Region} {c : Ctx} {R W R' W' : Addr → Prop}
    {J : TState → Mem → Prop} {s m} (hR : ∀ x, R x → R' x) (hW : ∀ x, W x → W' x)
    (h : Safe K al c R W J s m) : Safe K al c R' W' J s m := by
  induction h with
  | stop hj => exact .stop hj
  | next ha _ ih => exact .next ha ih
  | load ha hok hf _ ih => exact .load ha hok (hf.mono hR hW) ih
  | store ha hok hf _ ih => exact .store ha hok (hf.mono hR hW) ih

end Ptx

namespace Ptx.Auto
open Ptx

namespace MapSpec
variable {S : MapSpec} {A : Args}

theorem launch_alloc : (S.launch A).alloc = S.arrays.map fun a => ⟨A.base a, 4 * A.n.toNat⟩ :=
  rfl
theorem launch_params : (S.launch A).params = S.params A := rfl
theorem launch_grid : (S.launch A).grid = ⟨A.G, 1, 1⟩ := rfl
theorem launch_block : (S.launch A).block = ⟨A.B, 1, 1⟩ := rfl

theorem pre_fit (h : S.Pre A) {a : String} (ha : a ∈ S.arrays) : Fits (A.base a) A.n.toNat :=
  (h.2.1 a ha).1

theorem pre_align (h : S.Pre A) {a : String} (ha : a ∈ S.arrays) : (A.base a).toNat % 4 = 0 :=
  (h.2.1 a ha).2

theorem accessOk_elem (h : S.Pre A) {a : String} (ha : a ∈ S.arrays) {i : Nat} (hi : i < A.n.toNat) :
    accessOk (S.launch A).alloc (elem (A.base a) i) .b4 = true := by
  simp only [accessOk, launch_alloc, Size.bytes_b4, Bool.and_eq_true, beq_iff_eq,
    aligned_elem (pre_fit h ha) hi (pre_align h ha), true_and, List.any_map, List.any_eq_true]
  exact ⟨a, ha, holds_elem (pre_fit h ha) hi⟩

/-- An element of an output that overlaps no other array is not in that array. -/
theorem out_sep (h : S.Pre A) {a : String} (ha : a ∈ S.arrays) (hao : a ≠ S.out) {i j : Nat}
    (hi : i < A.n.toNat) (hj : j < A.n.toNat) {x : Addr} (hx : covers (elem (A.base S.out) i) 4 x) :
    ¬ covers (elem (A.base a) j) 4 x := by
  have hs := h.2.2.1 a ha hao
  exact elem_disjoint₂ (pre_fit h h.1) (pre_fit h ha) (by unfold Sep at hs; omega) hi hj hx

end MapSpec

/-! ## One element per thread: `guarded` -/

namespace MapSpec
variable (S : MapSpec) (A : Args)

/-- The footprint and postcondition of the thread that handles element `i`
alone (and nothing if `i ≥ n`). -/
def ER (i : Nat) (x : Addr) : Prop := i < A.n.toNat ∧ ∃ a ∈ S.arrays, covers (elem (A.base a) i) 4 x
def EW (i : Nat) (x : Addr) : Prop := i < A.n.toNat ∧ covers (elem (A.base S.out) i) 4 x
def EPost (m₀ : Mem) (i : Nat) (M : Mem) : Prop :=
  i < A.n.toNat → S.rel (rd32 M (elem (A.base S.out) i)) (S.val A m₀ i)

def GuardedOk (K : Kernel) : Prop :=
  ∀ A, S.Pre A → ∀ (m₀ : Mem), ∀ t ∈ (S.launch A).threads, ∀ (r : String → Val) (p : String → Bool),
    Safe K (S.launch A).alloc ((S.launch A).ctx t) (S.ER A (gid A.B t)) (S.EW A (gid A.B t))
      (fun s m => action K ((S.launch A).ctx t) s = .done ∧ S.EPost A m₀ (gid A.B t) m) ⟨0, r, p⟩ m₀

end MapSpec

section
variable {S : MapSpec} {A : Args}

theorem MapSpec.infoot_load {i : Nat} {a : String} (ha : a ∈ S.arrays) (hi : i < A.n.toNat) :
    InFoot (S.ER A i) (S.EW A i) ⟨.global, elem (A.base a) i, .b4, .read⟩ :=
  ⟨rfl, nofun, fun _ hx => .inr ⟨rfl, hi, a, ha, hx⟩⟩

theorem MapSpec.infoot_store {i : Nat} {o : String} (ho : S.out = o) (hi : i < A.n.toNat) :
    InFoot (S.ER A i) (S.EW A i) ⟨.global, elem (A.base o) i, .b4, .write⟩ :=
  ⟨rfl, nofun, fun _ hx => .inl ⟨hi, ho ▸ hx⟩⟩

theorem own_self {A : Args} {g : Nat} (hg : g < A.G.toNat * A.B.toNat) : MapSpec.Own A g g :=
  Nat.mod_eq_of_lt hg

theorem threadOk_of_guardedOk {K : Kernel} {mx : Nat} (hs : S.sched = .guarded mx) (h : S.GuardedOk K) :
    S.ThreadOk K := by
  intro A hpre m₀ t ht r p
  have hg := (launch_oneD S A).gid_lt ht
  have hn : A.n.toNat ≤ A.G.toNat * A.B.toNat := by
    have := hpre.2.2.2; rw [hs] at this; exact this.1
  refine ((h A hpre m₀ t ht r p).foot_mono ?_ ?_).weaken ?_
  · intro x ⟨hi, a, ha, hx⟩; exact ⟨_, hi, own_self hg, a, ha, hx⟩
  · intro x ⟨hi, hx⟩; exact ⟨_, hi, own_self hg, hx⟩
  · intro s m ⟨hd, hp⟩
    refine ⟨hd, fun i hi ho => ?_⟩
    have : i = gid A.B t := by
      unfold MapSpec.Own at ho; rwa [Nat.mod_eq_of_lt (by omega)] at ho
    subst this; exact hp hi

end

end Ptx.Auto

/-! ## Grid-stride loops: `stride`

The model names the loop head and says what each live register holds there,
as a function of the current element `i`: the index itself, the stride
`G·B`, the length, an array base, a pointer to element `i`, the pointer
stride `4·G·B`, a scalar, or a constant. That is the loop invariant; the
memory half of it is generic (`threadOk_of_stride` maintains it).

The two obligations are local. `EntryOk`: from the first instruction,
without touching memory, reach the head with element `gid`. `BodyOk`: from
the head at element `i`, with the arrays still initial at `i`, either
(`i < n`) touch only element `i`, leave `f` in the output there and come
back to the head at `i + G·B`, or (`n ≤ i`) touch nothing and finish, or
(`i < n ≤ i + G·B`, a loop tested at the bottom) handle element `i` and
finish. -/

namespace Ptx.Auto
open Ptx

inductive Role where
  | idx (w : Width)
  | stride (w : Width)
  | len
  | base (a : String)
  | ptr (a : String)
  | ptrStride
  | scalar (s : String)
  | const (v : Val)
  deriving Repr, DecidableEq

def Role.eval (A : Args) (i : Nat) : Role → Val
  | .idx .w8 => BitVec.ofNat 64 (i % 2 ^ 8)
  | .idx .w16 => BitVec.ofNat 64 (i % 2 ^ 16)
  | .idx .w64 => BitVec.ofNat 64 i
  | .idx .w32 => BitVec.ofNat 64 (i % 2 ^ 32)
  | .stride .w8 => BitVec.ofNat 64 (A.G.toNat * A.B.toNat % 2 ^ 8)
  | .stride .w16 => BitVec.ofNat 64 (A.G.toNat * A.B.toNat % 2 ^ 16)
  | .stride .w64 => BitVec.ofNat 64 (A.G.toNat * A.B.toNat)
  | .stride .w32 => BitVec.ofNat 64 (A.G.toNat * A.B.toNat % 2 ^ 32)
  | .len => ext32 A.n
  | .base a => A.base a
  | .ptr a => elem (A.base a) i
  | .ptrStride => BitVec.ofNat 64 (4 * (A.G.toNat * A.B.toNat))
  | .scalar s => ext32 (A.sc s)
  | .const v => v

structure Loop where
  head : Nat
  regs : List (String × Role)

/-- Each listed register holds its role's value. -/
def RegsOk (A : Args) (i : Nat) (s : TState) : List (String × Role) → Prop
  | [] => True
  | (r, x) :: l => s.r r = x.eval A i ∧ RegsOk A i s l

def Loop.At (Lp : Loop) (A : Args) (i : Nat) (s : TState) : Prop :=
  s.pc = Lp.head ∧ RegsOk A i s Lp.regs

namespace MapSpec
variable (S : MapSpec) (A : Args)

def EntryOk (Lp : Loop) (K : Kernel) : Prop :=
  ∀ A, S.Pre A → ∀ (m₀ : Mem), ∀ t ∈ (S.launch A).threads, ∀ (r : String → Val) (p : String → Bool),
    Safe K (S.launch A).alloc ((S.launch A).ctx t) (fun _ => False) (fun _ => False)
      (fun s m => Lp.At A (gid A.B t) s ∧ m = m₀) ⟨0, r, p⟩ m₀

def BodyOk (Lp : Loop) (K : Kernel) : Prop :=
  ∀ A, S.Pre A → ∀ (m₀ : Mem), ∀ t ∈ (S.launch A).threads, ∀ i,
    i % (A.G.toNat * A.B.toNat) = gid A.B t → i < A.n.toNat + A.G.toNat * A.B.toNat →
    ∀ s m, Lp.At A i s →
    (∀ a ∈ S.arrays, i < A.n.toNat → rd m (elem (A.base a) i) .b4 = rd m₀ (elem (A.base a) i) .b4) →
    Safe K (S.launch A).alloc ((S.launch A).ctx t) (S.ER A i) (S.EW A i)
      (fun s' m' =>
        (i < A.n.toNat ∧ Lp.At A (i + A.G.toNat * A.B.toNat) s' ∧
          S.rel (rd32 m' (elem (A.base S.out) i)) (S.val A m₀ i) ∧
          ∀ x, ¬ covers (elem (A.base S.out) i) 4 x → m' x = m x) ∨
        (A.n.toNat ≤ i ∧ action K ((S.launch A).ctx t) s' = .done ∧ m' = m) ∨
        (i < A.n.toNat ∧ A.n.toNat ≤ i + A.G.toNat * A.B.toNat ∧
          action K ((S.launch A).ctx t) s' = .done ∧
          S.rel (rd32 m' (elem (A.base S.out) i)) (S.val A m₀ i) ∧
          ∀ x, ¬ covers (elem (A.base S.out) i) 4 x → m' x = m x)) s m

end MapSpec

section
variable {S : MapSpec} {K : Kernel} {Lp : Loop}

/-- The loop head after the elements below `i` of thread `g` are done. -/
def StrideInv (S : MapSpec) (Lp : Loop) (A : Args) (m₀ : Mem) (g : Nat) (v : Nat) (s : TState) (m : Mem) :
    Prop :=
  ∃ i, v = A.n.toNat + A.G.toNat * A.B.toNat - i ∧ i % (A.G.toNat * A.B.toNat) = g ∧ g ≤ i ∧
    i < A.n.toNat + A.G.toNat * A.B.toNat ∧ Lp.At A i s ∧
    (∀ j < A.n.toNat, MapSpec.Own A g j → j < i → S.rel (rd32 m (elem (A.base S.out) j)) (S.val A m₀ j)) ∧
    (∀ x, (∀ j < A.n.toNat, MapSpec.Own A g j → j < i → ¬ covers (elem (A.base S.out) j) 4 x) →
      m x = m₀ x)

/-- Two elements of thread `g` at most one stride apart are the same. -/
theorem own_between {SS g i j : Nat} (hi : i % SS = g) (hj : j % SS = g) (h1 : i ≤ j) (h2 : j < i + SS) :
    j = i := by
  have ei := Nat.div_add_mod i SS
  have ej := Nat.div_add_mod j SS
  have : j / SS = i / SS := by
    rcases Nat.lt_trichotomy (j / SS) (i / SS) with h | h | h
    · have := Nat.mul_le_mul_left SS (Nat.succ_le_of_lt h); rw [Nat.mul_succ] at this; omega
    · exact h
    · have := Nat.mul_le_mul_left SS (Nat.succ_le_of_lt h); rw [Nat.mul_succ] at this; omega
  rw [this] at ej; omega

theorem threadOk_of_stride (he : S.EntryOk Lp K)
    (hb : S.BodyOk Lp K) : S.ThreadOk K := by
  intro A hpre m₀ t ht r p
  obtain ⟨hout, hfit, hsep, hsch⟩ := hpre
  have hg := (launch_oneD S A).gid_lt ht
  let SS := A.G.toNat * A.B.toNat
  let N := A.n.toNat
  let g := gid A.B t
  have hSS : 0 < SS := by omega
  have hfo := (hfit S.out hout).1
  refine ((he A ⟨hout, hfit, hsep, hsch⟩ m₀ t ht r p).foot_mono
    (R' := S.R A g) (W' := S.W A g) (fun _ h => h.elim) (fun _ h => h.elim)).mono ?_
  intro s m ⟨hat, hm⟩
  rw [hm]
  have hinv : StrideInv S Lp A m₀ g (N + SS - g) s m₀ :=
    ⟨g, rfl, Nat.mod_eq_of_lt hg, Nat.le_refl _, by omega, hat,
      fun j _ hoj hj => absurd hj (by have := Nat.mod_le j (A.G.toNat * A.B.toNat); unfold MapSpec.Own at hoj; omega),
      fun _ _ => rfl⟩
  refine Safe.loop (I := StrideInv S Lp A m₀ g) ?_ _ s m₀ hinv
  intro v s m ⟨i, hv, hio, hgi, hiN, hat, hdone, hframe⟩
  -- the arrays are still initial at element `i`
  have hin : ∀ a ∈ S.arrays, i < N → rd m (elem (A.base a) i) .b4 = rd m₀ (elem (A.base a) i) .b4 := by
    intro a ha hi
    apply rd_congr; intro x hx
    apply hframe; intro j hj hoj hji hcj
    by_cases hao : a = S.out
    · subst hao; exact elem_disjoint hfo hj hi (by omega) hcj hx
    · exact MapSpec.out_sep (S := S) ⟨hout, hfit, hsep, hsch⟩ ha hao hj hi hcj hx
  have body := hb A ⟨hout, hfit, hsep, hsch⟩ m₀ t ht i hio hiN s m hat hin
  refine (body.foot_mono ?_ ?_).weaken ?_
  · intro x ⟨hi, a, ha, hx⟩; exact ⟨i, hi, hio, a, ha, hx⟩
  · intro x ⟨hi, hx⟩; exact ⟨i, hi, hio, hx⟩
  · intro s' m' h
    rcases h with ⟨hi, hat', hval, hfr⟩ | ⟨hni, hd, hm'⟩ | ⟨hi, hlast, hd, hval, hfr⟩
    · left
      refine ⟨N + SS - (i + SS), by omega, i + SS, rfl, by rw [Nat.add_mod_right]; exact hio,
        by omega, by omega, hat', ?_, ?_⟩
      · intro j hj hoj hji
        by_cases hlt : j < i
        · rw [rd32_congr fun x hx => hfr x fun hc => elem_disjoint hfo hi hj (by omega) hc hx]
          exact hdone j hj hoj hlt
        · have : j = i := own_between hio hoj (by omega) hji
          subst this; exact hval
      · intro x hx
        have hc : ¬ covers (elem (A.base S.out) i) 4 x := hx i hi hio (by omega)
        rw [hfr x hc]
        exact hframe x fun j hj hoj hji => hx j hj hoj (by omega)
    · right
      subst hm'
      exact ⟨hd, fun j hj hoj => hdone j hj hoj (by omega)⟩
    · right
      refine ⟨hd, fun j hj hoj => ?_⟩
      by_cases hlt : j < i
      · rw [rd32_congr fun x hx => hfr x fun hc => elem_disjoint hfo hi hj (by omega) hc hx]
        exact hdone j hj hoj hlt
      · have : j = i := own_between hio hoj (by omega) (by omega)
        subst this; exact hval

end

end Ptx.Auto
