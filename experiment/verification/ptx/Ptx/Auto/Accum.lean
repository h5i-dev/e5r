/-
Check class `accum`: every thread combines one input element into one
output word with an atomic, for any commutative, associative atomic of PTX
at 32 or 64 bits (Ptx/Logic/CellAlgs.lean).

```c
unsigned i = blockIdx.x * blockDim.x + threadIdx.x;
if (i < n) atomicOp(out, x[i]);
```

`Correct S K`: for every 1-D launch with `G·B ≤ 2^32`, any `n`, an input
array of `n` elements and an output word of the algebra's size that fit,
are aligned and do not overlap, under every initial memory and register
content and every execution, the clauses of the phase theorem hold and when
all threads are done `*out = op(*out₀, x[0], …, x[min(n, G·B) − 1])`, whatever
order the threads combined in, and no other byte has changed.

The class theorem `correct_of` is proved once from `phase_sound`; the one
phase obligation (each thread's code) is the generated part.
-/
import Ptx.Auto.Block

set_option linter.unusedSimpArgs false

namespace Ptx.Auto.Accum
open Ptx Ptx.Auto

/-- The spec: the three parameters and the atomic's algebra. -/
structure Spec where
  input : String
  output : String
  length : String
  alg : CellAlg

/-- 4-byte words per element. -/
def Spec.k (S : Spec) : Nat := S.alg.sz.bytes / 4

structure Args (S : Spec) where
  G : BitVec 32
  B : BitVec 32
  n : BitVec 32
  x : Addr
  out : Addr

namespace Args
variable {S : Spec} (A : Args S)

def params : String → Val := fun p =>
  if p = S.input then A.x else if p = S.output then A.out
  else if p = S.length then ext32 A.n else 0

def launch : Launch :=
  { grid := ⟨A.G, 1, 1⟩, block := ⟨A.B, 1, 1⟩, params := A.params,
    alloc := [⟨A.x, 4 * (S.k * A.n.toNat)⟩, ⟨A.out, 4 * S.k⟩] }

/-- Element `i` of the input. -/
def elt (m : Mem) (i : Nat) : Val := rd m (elem A.x (S.k * i)) S.alg.sz

def Pre : Prop :=
  A.G.toNat * A.B.toNat ≤ 2 ^ 32 ∧ Fits A.x (S.k * A.n.toNat) ∧ A.x.toNat % (4 * S.k) = 0 ∧
  Fits A.out S.k ∧ A.out.toNat % (4 * S.k) = 0 ∧
  (A.x.toNat + 4 * (S.k * A.n.toNat) ≤ A.out.toNat ∨ A.out.toNat + 4 * S.k ≤ A.x.toNat)

theorem launch_oneD : A.launch.OneD A.G A.B := ⟨rfl, rfl⟩

end Args

/-- What `accum` claims about kernel `K`. -/
def Correct (S : Spec) (K : Kernel) : Prop :=
  ∀ A : Args S, A.Pre → ∀ (m₀ : Mem) (sh₀ : Dim3 → Mem) (r₀ : Tid → String → Val)
    (p₀ : Tid → String → Bool),
    let L := A.launch
    let c₀ := Cfg.init r₀ p₀ m₀ sh₀
    (∀ c, Reach K L c₀ c → ¬ Faults K L c) ∧
    (∀ c, Reach K L c₀ c → Done K L c ∨ ∃ c', Step K L c c') ∧
    (∃ bound, ∀ j c, Steps K L j c₀ c → j ≤ bound) ∧
    RaceFree K L c₀ ∧
    (∃ c, Reach K L c₀ c ∧ Done K L c) ∧
    (∀ c, Reach K L c₀ c → Done K L c →
      rd c.mem A.out S.alg.sz = S.alg.op (rd m₀ A.out S.alg.sz)
        (afold S.alg (fun i => if i < A.n.toNat then A.elt m₀ i else S.alg.e) (A.G.toNat * A.B.toNat)) ∧
      (∀ y, ¬ covers A.out S.alg.sz.bytes y → c.mem y = m₀ y))

section
variable {S : Spec} (A : Args S)

def gid (t : Tid) : Nat := t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat

/-- A thread reads its element when `gid < n` and writes nothing. -/
def foot (t : Tid) (_ : Nat) : Foot :=
  { r := fun l => l.1 = .global ∧ gid A t < A.n.toNat ∧
      covers (elem A.x (S.k * gid A t)) S.alg.sz.bytes l.2
    w := fun _ => False }

def phased (N : Nat) (m₀ : Mem) (sh₀ : Dim3 → Mem) : Phased where
  P := fun _ => 1
  F := foot A
  T := fun _ _ s => s.pc = 0
  N := fun _ _ => N
  M := fun b _ => ⟨m₀, sh₀ b⟩
  bpc := fun _ _ => 0
  Cell := fun a => a = A.out
  Alg := S.alg
  Δ := fun t _ a => if gid A t < A.n.toNat ∧ a = A.out then A.elt m₀ (gid A t) else S.alg.e

end

/-- The phase obligation: each thread's code, from pc 0, for every launch in
`Pre`. -/
def Obligation (S : Spec) (K : Kernel) (N : Nat) : Prop :=
  ∀ A : Args S, A.Pre → ∀ m₀ sh₀, ∀ t ∈ A.launch.threads, ∀ s : TState, s.pc = 0 →
    Run K (A.launch.allocs K) (A.launch.ctx t) (foot A t 0) (fun a => a = A.out) S.alg
      ((phased A N m₀ sh₀).J K A.launch t 0) N s ⟨m₀, sh₀ t.ctaid⟩ (fun _ => S.alg.e)

/-! ### Folds over a 1-D launch -/

theorem tfold_append (A : CellAlg) (l l' : List Tid) (f : Tid → Val) :
    tfold A (l ++ l') f = A.op (tfold A l f) (tfold A l' f) := by
  induction l with
  | nil =>
    show tfold A l' f = A.op A.e (tfold A l' f)
    rw [A.comm, A.unit _ (tfold_trunc A l' f)]
  | cons a l ih =>
    simp only [List.cons_append, tfold, List.map_cons, List.foldr_cons] at ih ⊢
    rw [ih, A.assoc]

theorem afold_succ' (A : CellAlg) (v : Nat → Val) (hv : ∀ i, A.sz.trunc (v i) = v i) :
    ∀ N, afold A v (N + 1) = A.op (v 0) (afold A (fun i => v (i + 1)) N)
  | 0 => by
    show A.op A.e (v 0) = A.op (v 0) A.e
    exact A.comm _ _
  | N + 1 => by
    rw [show afold A v (N + 1 + 1) = A.op (afold A v (N + 1)) (v (N + 1)) from rfl,
      afold_succ' A v hv N, A.assoc]
    rfl

theorem afold_congr (A : CellAlg) {v w : Nat → Val} : ∀ {N}, (∀ i < N, v i = w i) →
    afold A v N = afold A w N
  | 0, _ => rfl
  | N + 1, h => by
    show A.op (afold A v N) (v N) = A.op (afold A w N) (w N)
    rw [afold_congr A fun i hi => h i (by omega), h N (by omega)]

theorem foldr_range_map (A : CellAlg) :
    ∀ (N : Nat) (v : Nat → Val), (∀ i, A.sz.trunc (v i) = v i) → ∀ (f : Nat → Val),
      (∀ i < N, f i = v i) → ((List.range N).map f).foldr A.op A.e = afold A v N := by
  intro N
  induction N with
  | zero => intro _ _ _ _; rfl
  | succ N ih =>
    intro v hv f hf
    rw [List.range_succ_eq_map, List.map_cons, List.foldr_cons, List.map_map,
      afold_succ' A v hv N, hf 0 (by omega)]
    congr 1
    exact ih (fun i => v (i + 1)) (fun i => hv _) (f ∘ Nat.succ) (fun i hi => hf _ (by omega))

theorem afold_blocks (A : CellAlg) (v : Nat → Val) (hv : ∀ i, A.sz.trunc (v i) = v i) (B : Nat) :
    ∀ G, afold A (fun c => afold A (fun i => v (c * B + i)) B) G = afold A v (G * B) := by
  have add : ∀ a b, afold A v (a + b) = A.op (afold A v a) (afold A (fun i => v (a + i)) b) := by
    intro a b
    induction b with
    | zero => simp only [Nat.add_zero, afold]; rw [A.unit _ (afold_trunc _ _ _)]
    | succ b ih => rw [← Nat.add_assoc]; simp only [afold]; rw [ih, A.assoc]
  intro G
  induction G with
  | zero => simp [afold]
  | succ G ih => rw [Nat.succ_mul, add, ← ih]; rfl

theorem tfold_oneD_gid {L : Launch} {G B : BitVec 32} (h1 : L.OneD G B) (A : CellAlg) (v : Nat → Val)
    (hv : ∀ i, A.sz.trunc (v i) = v i) :
    tfold A L.threads (fun t => v (t.ctaid.x.toNat * B.toNat + t.tid.x.toNat)) =
      afold A v (G.toNat * B.toNat) := by
  rw [Launch.threads, h1.1, h1.2]
  have flat : ∀ (l : List Dim3) (g : Dim3 → List Tid) (f : Tid → Val),
      tfold A (l.flatMap g) f = (l.map fun c => tfold A (g c) f).foldr A.op A.e := by
    intro l g f
    induction l with
    | nil => rfl
    | cons a l ih => rw [List.flatMap_cons, tfold_append A _ _ f, ih]; rfl
  rw [flat]
  have inner : ∀ c : Dim3, c.x.toNat < 2 ^ 32 → tfold A ((dims ⟨B, 1, 1⟩).map fun d => (⟨c, d⟩ : Tid))
      (fun t => v (t.ctaid.x.toNat * B.toNat + t.tid.x.toNat)) =
        afold A (fun i => v (c.x.toNat * B.toNat + i)) B.toNat := by
    intro c _
    rw [show (⟨B, 1, 1⟩ : Dim3) = ⟨B, 1#32, 1#32⟩ from rfl, dims_oneD, range32, List.map_map,
      List.map_map]
    unfold tfold
    rw [List.map_map]
    refine foldr_range_map A B.toNat _ (fun i => hv _) _ fun i hi => ?_
    have := B.isLt
    show v (c.x.toNat * B.toNat + (BitVec.ofNat 32 i).toNat) = _
    simp; rw [Nat.mod_eq_of_lt (by omega)]
  rw [show (⟨G, 1, 1⟩ : Dim3) = ⟨G, 1#32, 1#32⟩ from rfl, dims_oneD, range32, List.map_map,
    List.map_map, ← afold_blocks A v hv B.toNat G.toNat]
  refine foldr_range_map A G.toNat _ (fun i => afold_trunc _ _ _) _ fun i hi => ?_
  have := G.isLt
  show tfold A _ _ = _
  rw [inner _ (BitVec.isLt _)]
  show afold A (fun j => v ((BitVec.ofNat 32 i).toNat * B.toNat + j)) B.toNat = _
  have h : (BitVec.ofNat 32 i).toNat = i := by simp; omega
  rw [h]

theorem Spec.sz_bytes (S : Spec) : S.alg.sz.bytes = 4 * S.k := by
  unfold Spec.k; cases S.alg.sz <;> rfl

/-- An aligned 64-bit element of an array of 64-bit elements that is one
allocation of the list. -/
theorem accessOk_elem2_b8 {al : List Region} {base : Addr} {N i : Nat}
    (hm : ⟨base, 4 * (2 * N)⟩ ∈ al) (hf : Fits base (2 * N)) (hal : base.toNat % (4 * 2) = 0)
    (hi : i < N) : accessOk al (elem base (2 * i)) .b8 = true := by
  have h1 := toNat_elem hf (show 2 * i < 2 * N by omega)
  simp only [accessOk, Size.bytes_b8, Bool.and_eq_true, beq_iff_eq, List.any_eq_true]
  refine ⟨by rw [h1]; omega, _, hm, ?_⟩
  simp only [Region.holds, decide_eq_true_eq, h1]
  unfold Fits at hf; omega

/-- Combining `δ` into a cell whose ghost is still the unit. -/
theorem acc_e (A : CellAlg) (a : Addr) {δ : Val} (hδ : A.sz.trunc δ = δ) :
    Ghost.acc A (fun _ => A.e) a δ = fun x => if x = a then δ else A.e := by
  funext x
  simp only [Ghost.acc]
  split
  · rw [A.comm, A.unit _ hδ]
  · rfl

theorem trunc_ite (A : CellAlg) (p : Prop) [Decidable p] (x : Val) (hx : A.sz.trunc x = x) :
    A.sz.trunc (if p then x else A.e) = if p then x else A.e := by
  split
  · exact hx
  · exact A.e_ok

section
variable {S : Spec} {K : Kernel} {N : Nat} (A : Args S)

theorem ok (hO : Obligation S K N) (hpre : A.Pre) (m₀ : Mem) (sh₀ : Dim3 → Mem)
    (r₀ : Tid → String → Val) (p₀ : Tid → String → Bool) :
    (phased A N m₀ sh₀).Ok K A.launch r₀ p₀ m₀ sh₀ := by
  obtain ⟨hGB, fx, xal, fout, oal, hsep⟩ := hpre
  have hb := S.sz_bytes
  refine ⟨fun _ _ => by simp [phased], fun _ _ => rfl, fun _ _ _ => rfl, ?_, fun _ _ _ _ _ _ => rfl,
    fun _ _ _ _ _ _ _ _ _ hw _ => hw, fun _ _ _ _ _ _ _ _ _ _ hw _ => hw, ?_, ?_⟩
  · intro t ht k hk s hs
    simp only [phased] at hk hs ⊢
    obtain rfl : k = 0 := by omega
    exact hO A ⟨hGB, fx, xal, fout, oal, hsep⟩ m₀ sh₀ t ht s hs
  · -- `*out` is in nobody's footprint
    intro t ht k a ha y hy htc
    simp only [phased] at ha htc hy
    subst ha
    rcases htc with ⟨-, hlt, hcv⟩ | h
    · have hk : S.k * gid A t < S.k * A.n.toNat := Nat.mul_lt_mul_of_pos_left hlt (by
        unfold Spec.k; cases S.alg.sz <;> decide)
      have h1 := toNat_elem fx hk
      have hle : S.k * gid A t + S.k ≤ S.k * A.n.toNat := by
        have := Nat.mul_le_mul_left S.k (show gid A t + 1 ≤ A.n.toNat by omega)
        rw [Nat.mul_add, Nat.mul_one] at this; exact this
      unfold Fits at fx fout
      rw [hb, covers_iff (by omega), h1] at hcv
      rw [hb, covers_iff (by omega)] at hy
      simp only at hcv
      omega
    · exact h
  · intro a b ha hb' hab
    simp only [phased] at ha hb'
    exact absurd (ha.trans hb'.symm) hab

end

/-- The class theorem: the phase obligation gives `Correct`. -/
theorem correct_of {S : Spec} {K : Kernel} {N : Nat} (hO : Obligation S K N) : Correct S K := by
  intro A hpre m₀ sh₀ r₀ p₀ L c₀
  have R := Phased.phase_sound (ok A hO hpre m₀ sh₀ r₀ p₀)
  refine ⟨R.noFault, R.progress, R.bounded, R.raceFree,
    Phased.exists_done_of R.progress R.bounded, fun c hc hd => ?_⟩
  obtain ⟨-, hun, hcell⟩ := R.final c hc hd
  refine ⟨?_, fun y hy => hun y (fun t _ k _ h => h) ?_⟩
  · have hc := hcell A.out rfl
    simp only [phased] at hc
    rw [hc]
    congr 1
    have hv : ∀ i, S.alg.sz.trunc (if i < A.n.toNat then A.elt m₀ i else S.alg.e) =
        if i < A.n.toNat then A.elt m₀ i else S.alg.e := fun i => trunc_ite _ _ _ (trunc_rd _ _ _)
    refine (tfold_congr fun t _ => ?_).trans (tfold_oneD_gid (A.launch_oneD) S.alg _ hv)
    show S.alg.op S.alg.e _ = _
    rw [S.alg.comm, S.alg.unit _ (by simp only [and_true]; exact hv _)]
    simp only [and_true]; rfl
  · intro b hb; simp only [phased] at hb; subst hb; exact hy

end Ptx.Auto.Accum
