/-
M4 check class `reduce32`: block tree reductions with sequential addressing.

```c
s[tid] = i < n ? x[i] : 0;            // phase 0, then bar.sync
for (k = blockDim.x / 2; k > 0; k >>= 1) {
  if (tid < k) s[tid] += s[tid + k];  // phases 1 .. j, each ending at bar.sync
  __syncthreads();
}
if (tid == 0) out[blockIdx.x] = s[0]; // phase j + 1 (`per_block`)
if (tid == 0) atomicAdd(out, s[0]);   // phase j + 1 (`atomic`)
```

The class theorems (`correct_of`, `correct_atomic_of`) are proved once here
from `phase_sound`: the footprints, the per-phase memory, the tree sum and
the side conditions do not depend on the instructions. What does is left as
hypotheses, the phase obligations: for each phase, from the registers the
`Code` claims at its start, the thread's instructions do what the phase's
footprint and memory say and stop at the next barrier with the registers the
`Code` claims there. `e5r-verify ptx check` writes a `Code` from the spec's
register roles and proves the obligations with the M4 tactics; a `Code`
that is wrong only makes them unprovable, it cannot make the theorem false.
-/
import Ptx.Auto.Block

set_option linter.unusedSimpArgs false

namespace Ptx.Auto.Reduce32
open Ptx Ptx.Auto.Block

variable {S : Spec}

/-- The launches the class theorems are about: blocks of `B = 2^j ≤ 2^maxJ`
threads, `G·B ≤ 2^32`, an input of `n` words and an output of `len` words
that fit, are aligned and do not overlap, and any placement of the shared
array ptxas could choose. -/
def Pre (K : Kernel) (len : Nat) (A : Block.Args S) : Prop :=
  A.B.toNat = 2 ^ A.j ∧ A.j ≤ S.maxJ ∧ A.G.toNat * A.B.toNat ≤ 2 ^ 32 ∧
  Fits A.x A.n.toNat ∧ A.x.toNat % 4 = 0 ∧ Fits A.out len ∧ A.out.toNat % 4 = 0 ∧
  (A.x.toNat + 4 * A.n.toNat ≤ A.out.toNat ∨ A.out.toNat + 4 * len ≤ A.x.toNat) ∧
  LayoutOk K A.sh

/-- The stride of phase `k`. -/
def stride (A : Block.Args S) (k : Nat) : Nat := A.B.toNat / 2 ^ k

/-- What `s[i]` holds after phase `k` (`k ≤ j`). -/
def V (A : Block.Args S) (m₀ : Mem) (b : Nat) : Nat → Nat → BitVec 32
  | 0, i => A.seg m₀ b i
  | k + 1, i => if i < stride A (k + 1) then V A m₀ b k i + V A m₀ b k (i + stride A (k + 1))
      else V A m₀ b k i

/-! ### The tree computes the sum -/

theorem accUpTo_congr {f g : Nat → BitVec 32} {N : Nat} (h : ∀ m < N, f m = g m) :
    accUpTo f N = accUpTo g N := by
  induction N with
  | zero => rfl
  | succ N ih => simp only [accUpTo]; rw [ih fun m hm => h m (by omega), h N (by omega)]

theorem accUpTo_even_odd (f : Nat → BitVec 32) (N : Nat) :
    accUpTo f (2 * N) = accUpTo (fun m => f (2 * m)) N + accUpTo (fun m => f (2 * m + 1)) N := by
  induction N with
  | zero => simp [accUpTo]
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by omega]
    simp only [accUpTo]
    rw [ih]
    ac_rfl

section
variable (A : Block.Args S)

theorem stride_eq (hB : A.B.toNat = 2 ^ A.j) {k : Nat} (hk : k ≤ A.j) :
    stride A k = 2 ^ (A.j - k) := by
  unfold stride; rw [hB]; exact Nat.pow_div hk (by decide)

theorem stride_succ (hB : A.B.toNat = 2 ^ A.j) {k : Nat} (hk : k + 1 ≤ A.j) :
    stride A k = 2 * stride A (k + 1) := by
  rw [stride_eq A hB (by omega), stride_eq A hB hk, show A.j - k = (A.j - (k + 1)) + 1 by omega,
    Nat.pow_succ, Nat.mul_comm]

theorem V_tree (hB : A.B.toNat = 2 ^ A.j) (m₀ : Mem) (b : Nat) : ∀ k ≤ A.j, ∀ i < stride A k,
    V A m₀ b k i = accUpTo (fun m => V A m₀ b 0 (i + m * stride A k)) (2 ^ k) := by
  intro k
  induction k with
  | zero =>
    intro _ i _
    simp [accUpTo]
  | succ k ih =>
    intro hk i hi
    have h2 := stride_succ A hB hk
    have hik : i < stride A k := by omega
    have hik' : i + stride A (k + 1) < stride A k := by omega
    rw [show V A m₀ b (k + 1) i = V A m₀ b k i + V A m₀ b k (i + stride A (k + 1)) by
      simp only [V, hi, ↓reduceIte]]
    rw [ih (by omega) i hik, ih (by omega) _ hik', Nat.pow_succ, Nat.mul_comm (2 ^ k) 2,
      accUpTo_even_odd]
    congr 1
    · exact accUpTo_congr fun m _ => by
        rw [h2]; congr 1
        simp only [Nat.mul_assoc, Nat.mul_comm]
    · exact accUpTo_congr fun m _ => by
        rw [h2]; congr 1
        simp only [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.one_mul, Nat.add_assoc, Nat.add_comm]

/-- After phase `j`, `s[0]` holds the sum of the segment. -/
theorem V_final (hB : A.B.toNat = 2 ^ A.j) (m₀ : Mem) (b : Nat) :
    V A m₀ b A.j 0 = accUpTo (fun m => A.seg m₀ b m) A.B.toNat := by
  have h1 : stride A A.j = 1 := by rw [stride_eq A hB (Nat.le_refl _)]; simp
  rw [V_tree A hB m₀ b A.j (Nat.le_refl _) 0 (by omega), h1, ← hB]
  exact accUpTo_congr fun m _ => by simp [V]

theorem stride_facts (hB : A.B.toNat = 2 ^ A.j) {m : Nat} (hm : m + 1 ≤ A.j) :
    1 ≤ stride A (m + 1) ∧ stride A m = 2 * stride A (m + 1) ∧ stride A m ≤ A.B.toNat ∧
      A.B.toNat / 2 ^ 1 = stride A 1 := by
  have h1 := stride_eq A hB hm
  have h2 := stride_succ A hB hm
  refine ⟨by rw [h1]; exact Nat.one_le_two_pow, h2, Nat.div_le_self _ _, rfl⟩

theorem stride_last (hB : A.B.toNat = 2 ^ A.j) : stride A A.j = 1 := by
  rw [stride_eq A hB (Nat.le_refl _)]; simp

/-- Before the last tree phase the stride is at least 2. -/
theorem stride_two (hB : A.B.toNat = 2 ^ A.j) {k : Nat} (hk : k < A.j) : 2 ≤ stride A k := by
  rw [stride_eq A hB (by omega), show A.j - k = (A.j - k - 1) + 1 by omega, Nat.pow_succ]
  have := Nat.one_le_two_pow (n := A.j - k - 1)
  omega

end

/-! ### What the generated proof supplies -/

/-- The kernel-specific part of a phase decomposition: the state each thread
is in when phase `k ≥ 1` starts (`T A t k`, the barrier's continuation pc and
the registers there), the pc of the barrier that ends phase `k`, and a step
bound per phase. Phase 0 starts at pc 0 with arbitrary registers. -/
structure Code (S : Spec) where
  T : Block.Args S → Mem → Tid → Nat → TState → Prop
  bpc : Block.Args S → Nat → Nat
  N : Nat

/-- The entry states, with phase 0 at the start of the kernel. -/
def Code.Tc (C : Code S) (A : Block.Args S) (m₀ : Mem) (t : Tid) : Nat → TState → Prop
  | 0, s => s.pc = 0
  | k + 1, s => C.T A m₀ t (k + 1) s

/-! ### `per_block`: thread 0 of block `b` stores the sum in `out[b]` -/

section
variable (A : Block.Args S)

/-- What thread `t` touches in phase `k`: in phase 0 it reads its input
element and writes `s[tid]`; in the tree phases, if `tid < stride`, it reads
`s[tid + stride]` and updates `s[tid]`; in the last phase thread 0 reads
`s[0]` and writes `out[ctaid]`. -/
def foot (t : Tid) (k : Nat) : Foot :=
  if k = 0 then
    { r := fun l => l.1 = .global ∧ t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat < A.n.toNat ∧
        covers (elem A.x (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)) 4 l.2
      w := fun l => l.1 = .shared ∧ covers (elem A.sb (t.tid.x.toNat)) 4 l.2 }
  else if k ≤ A.j then
    { r := fun l => l.1 = .shared ∧ t.tid.x.toNat < stride A k ∧
        covers (elem A.sb (t.tid.x.toNat + stride A k)) 4 l.2
      w := fun l => l.1 = .shared ∧ t.tid.x.toNat < stride A k ∧ covers (elem A.sb (t.tid.x.toNat)) 4 l.2 }
  else
    { r := fun l => l.1 = .shared ∧ t.tid.x.toNat = 0 ∧ covers (elem A.sb 0) 4 l.2
      w := fun l => l.1 = .global ∧ t.tid.x.toNat = 0 ∧ covers (elem A.out (t.ctaid.x.toNat)) 4 l.2 }

/-- CTA `b`'s view when phase `k` starts. -/
def mem (m₀ : Mem) (sh₀ : Dim3 → Mem) (b : Dim3) : Nat → Heap
  | 0 => ⟨m₀, sh₀ b⟩
  | k + 1 =>
    ⟨if k = A.j + 1 then wr m₀ (elem A.out b.x.toNat) .b4 (ext32 (V A m₀ b.x.toNat A.j 0)) else m₀,
     cells A.sb A.B.toNat (V A m₀ b.x.toNat (min k A.j)) (sh₀ b)⟩

def phased (C : Code S) (m₀ : Mem) (sh₀ : Dim3 → Mem) : Phased where
  P := fun _ => A.j + 2
  F := foot A
  T := C.Tc A m₀
  N := fun _ _ => C.N
  M := mem A m₀ sh₀
  bpc := fun _ k => C.bpc A k
  Cell := fun _ => False
  Δ := fun _ _ _ => 0

theorem foot_zero (t : Tid) : foot A t 0 =
    { r := fun l => l.1 = .global ∧ t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat < A.n.toNat ∧
        covers (elem A.x (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)) 4 l.2
      w := fun l => l.1 = .shared ∧ covers (elem A.sb t.tid.x.toNat) 4 l.2 } := rfl

theorem foot_tree (t : Tid) {k : Nat} (h1 : 1 ≤ k) (hk : k ≤ A.j) : foot A t k =
    { r := fun l => l.1 = .shared ∧ t.tid.x.toNat < stride A k ∧
        covers (elem A.sb (t.tid.x.toNat + stride A k)) 4 l.2
      w := fun l => l.1 = .shared ∧ t.tid.x.toNat < stride A k ∧ covers (elem A.sb t.tid.x.toNat) 4 l.2 } := by
  simp only [foot, show k ≠ 0 by omega, ↓reduceIte, hk]

theorem foot_after (t : Tid) {k : Nat} (hk : A.j < k) : foot A t k =
    { r := fun l => l.1 = .shared ∧ t.tid.x.toNat = 0 ∧ covers (elem A.sb 0) 4 l.2
      w := fun l => l.1 = .global ∧ t.tid.x.toNat = 0 ∧ covers (elem A.out t.ctaid.x.toNat) 4 l.2 } := by
  simp only [foot, show k ≠ 0 by omega, show ¬ k ≤ A.j by omega, ↓reduceIte]

theorem foot_last (t : Tid) : foot A t (A.j + 1) =
    { r := fun l => l.1 = .shared ∧ t.tid.x.toNat = 0 ∧ covers (elem A.sb 0) 4 l.2
      w := fun l => l.1 = .global ∧ t.tid.x.toNat = 0 ∧ covers (elem A.out t.ctaid.x.toNat) 4 l.2 } :=
  foot_after A t (by omega)

end

/-- The three phase obligations, for every launch in `Pre`. -/
structure Obligations (K : Kernel) (C : Code S) : Prop where
  load : ∀ A : Block.Args S, Pre K A.G.toNat A → ∀ m₀ sh₀, ∀ t ∈ (A.launch A.G.toNat).threads, ∀ s,
    C.Tc A m₀ t 0 s →
    Run K ((A.launch A.G.toNat).allocs K) ((A.launch A.G.toNat).ctx t) (foot A t 0) (fun _ => False) add32
      ((phased A C m₀ sh₀).J K (A.launch A.G.toNat) t 0) C.N s (mem A m₀ sh₀ t.ctaid 0) (fun _ => 0)
  tree : ∀ A : Block.Args S, Pre K A.G.toNat A → ∀ m₀ sh₀, ∀ t ∈ (A.launch A.G.toNat).threads, ∀ m,
    m + 1 ≤ A.j → ∀ s, C.Tc A m₀ t (m + 1) s →
    Run K ((A.launch A.G.toNat).allocs K) ((A.launch A.G.toNat).ctx t) (foot A t (m + 1))
      (fun _ => False) add32 ((phased A C m₀ sh₀).J K (A.launch A.G.toNat) t (m + 1)) C.N s
      (mem A m₀ sh₀ t.ctaid (m + 1)) (fun _ => 0)
  last : ∀ A : Block.Args S, Pre K A.G.toNat A → ∀ m₀ sh₀, ∀ t ∈ (A.launch A.G.toNat).threads, ∀ s,
    C.Tc A m₀ t (A.j + 1) s →
    Run K ((A.launch A.G.toNat).allocs K) ((A.launch A.G.toNat).ctx t) (foot A t (A.j + 1))
      (fun _ => False) add32 ((phased A C m₀ sh₀).J K (A.launch A.G.toNat) t (A.j + 1)) C.N s
      (mem A m₀ sh₀ t.ctaid (A.j + 1)) (fun _ => 0)

/-- What `per_block` claims about kernel `K`: for every launch in `Pre`,
under every initial memory, shared memory and register content, and every
execution: no fault and no diverged barrier, progress, bounded executions,
phase-relative race freedom, a finished execution exists, and when all
threads are done every `out[b]` (`b < G`) is the sum of block `b`'s
segment (elements at or past `n` count as zero) and no other byte has
changed. -/
def Correct (S : Spec) (K : Kernel) : Prop :=
  ∀ A : Block.Args S, Pre K A.G.toNat A → ∀ (m₀ : Mem) (sh₀ : Dim3 → Mem) (r₀ : Tid → String → Val)
    (p₀ : Tid → String → Bool),
    let L := A.launch A.G.toNat
    let c₀ := Cfg.init r₀ p₀ m₀ sh₀
    (∀ c, Reach K L c₀ c → ¬ Faults K L c) ∧
    (∀ c, Reach K L c₀ c → Done K L c ∨ ∃ c', Step K L c c') ∧
    (∃ bound, ∀ j c, Steps K L j c₀ c → j ≤ bound) ∧
    RaceFree K L c₀ ∧
    (∃ c, Reach K L c₀ c ∧ Done K L c) ∧
    (∀ c, Reach K L c₀ c → Done K L c →
      (∀ b < A.G.toNat, rd32 c.mem (elem A.out b) = accUpTo (fun i => A.seg m₀ b i) A.B.toNat) ∧
      (∀ y, (∀ b < A.G.toNat, ¬ covers (elem A.out b) 4 y) → c.mem y = m₀ y))

section
variable {K : Kernel} {W : Nat} (hfit : Fit S K W) (C : Code S) (A : Block.Args S)

include hfit in
theorem fits_sb {len : Nat} (hpre : Pre K len A) :
    A.sb.toNat % 4 = 0 ∧ Fits A.sb A.B.toNat ∧ A.B.toNat ≤ W ∧ 1 ≤ A.B.toNat := by
  obtain ⟨sal, sbb, hW⟩ := A.sb_facts hfit hpre.2.2.2.2.2.2.2.2
  have hj := Nat.pow_le_pow_right (show 0 < 2 by decide) hpre.2.1
  have hB1 : 1 ≤ A.B.toNat := by rw [hpre.1]; exact Nat.one_le_two_pow
  have hB := hpre.1
  refine ⟨sal, ?_, by omega, hB1⟩
  unfold Fits; omega

include hfit in
theorem ok (hO : Obligations K C) (hpre : Pre K A.G.toNat A) (m₀ : Mem) (sh₀ : Dim3 → Mem)
    (r₀ : Tid → String → Val) (p₀ : Tid → String → Bool) :
    (phased A C m₀ sh₀).Ok K (A.launch A.G.toNat) r₀ p₀ m₀ sh₀ := by
  obtain ⟨sal, fsbB, -, hB1⟩ := fits_sb hfit A hpre
  have fx := hpre.2.2.2.1
  have fout := hpre.2.2.2.2.2.1
  have hGB := hpre.2.2.1
  refine ⟨fun _ _ => by simp [phased], fun _ _ => rfl, fun _ _ _ => rfl, ?_, ?_, ?_, ?_,
    fun _ _ _ _ h => h.elim, fun _ _ h => h.elim⟩
  · -- the phase obligations
    intro t ht k hk s hs
    simp only [phased] at hk ⊢
    rcases Nat.lt_or_ge k 1 with h0 | h1
    · obtain rfl : k = 0 := by omega
      exact hO.load A hpre m₀ sh₀ t ht s hs
    · rcases Nat.lt_or_ge A.j k with hj | hj
      · obtain rfl : k = A.j + 1 := by omega
        exact hO.last A hpre m₀ sh₀ t ht s hs
      · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
        exact hO.tree A hpre m₀ sh₀ t ht m hj s hs
  · -- what nobody wrote in a phase is unchanged by it
    intro b k x hb hk hno
    simp only [phased] at hk hno ⊢
    have hb' := hb
    obtain ⟨t₀, ht₀, rfl⟩ := hb'
    obtain ⟨sp, y⟩ := x
    have cellOf : ∀ (h : (y - A.sb).toNat < 4 * A.B.toNat),
        th t₀.ctaid ((y - A.sb).toNat / 4) ∈ (A.launch A.G.toNat).threads ∧
          (th t₀.ctaid ((y - A.sb).toNat / 4)).tid.x.toNat = (y - A.sb).toNat / 4 ∧
          covers (elem A.sb ((y - A.sb).toNat / 4)) 4 y :=
      fun h => ⟨(A.th_mem hb (i := (y - A.sb).toNat / 4) (by omega)).1,
        (A.th_mem hb (i := (y - A.sb).toNat / 4) (by omega)).2, covers_of_lt fsbB h⟩
    rcases Nat.lt_or_ge k 1 with h0 | h1
    · obtain rfl : k = 0 := by omega
      cases sp with
      | global =>
        simp only [mem, Heap.get, Heap.at]
        repeat' split
        all_goals first | rfl | (exfalso; omega)
      | shared =>
        show cells A.sb A.B.toNat _ (sh₀ t₀.ctaid) y = sh₀ t₀.ctaid y
        unfold cells; split
        · next h =>
          obtain ⟨hm, hti, hcv⟩ := cellOf h
          have hnw := hno _ hm rfl
          rw [foot_zero] at hnw
          exact absurd ⟨rfl, by rw [hti]; exact hcv⟩ hnw
        · rfl
    · rcases Nat.lt_or_ge A.j k with hj | hj
      · obtain rfl : k = A.j + 1 := by omega
        cases sp with
        | shared =>
          show cells _ _ (V A m₀ _ (min (A.j + 1) A.j)) _ y = cells _ _ (V A m₀ _ (min A.j A.j)) _ y
          rw [show min (A.j + 1) A.j = A.j by omega, Nat.min_self]
        | global =>
          show (if A.j + 1 = A.j + 1 then _ else m₀) y = (if A.j = A.j + 1 then _ else m₀) y
          simp only [↓reduceIte, show A.j ≠ A.j + 1 by omega]
          apply wr_outside
          intro hcv
          have hm := (A.th_mem hb (i := 0) (by omega))
          have := hno _ hm.1 rfl
          rw [foot_last] at this
          exact this ⟨rfl, hm.2, hcv⟩
      · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
        cases sp with
        | global =>
          simp only [mem, Heap.get, Heap.at]
          repeat' split
          all_goals first | rfl | (exfalso; omega)
        | shared =>
          show cells _ _ (V A m₀ _ (min (m + 1) A.j)) _ y = cells _ _ (V A m₀ _ (min m A.j)) _ y
          rw [show min (m + 1) A.j = m + 1 by omega, show min m A.j = m by omega]
          apply cells_congr
          · intro h
            obtain ⟨hm, hti, hcv⟩ := cellOf h
            have hnw := hno _ hm rfl
            rw [foot_tree _ _ (by omega) hj] at hnw
            show (if _ < stride A (m + 1) then _ else _) = _
            split
            · next hl => exact absurd ⟨rfl, by rw [hti]; exact hl, by rw [hti]; exact hcv⟩ hnw
            · rfl
          · intro _; rfl
  · -- in one phase of one CTA, no thread writes what another touches
    intro t ht u hu htu hc k _ x hw htc
    simp only [phased] at hw htc
    have hne := A.tid_ne ht hu hc htu
    obtain ⟨-, hti, -⟩ := A.thread_facts hGB ht
    obtain ⟨-, hui, -⟩ := A.thread_facts hGB hu
    obtain ⟨sp, y⟩ := x
    rcases Nat.lt_or_ge k 1 with h0 | h1
    · obtain rfl : k = 0 := by omega
      rw [foot_zero] at hw htc
      obtain ⟨hsp, hcv⟩ := hw
      rcases htc with ⟨hsp', -⟩ | ⟨-, hcv'⟩
      · simp only at hsp hsp'; rw [hsp] at hsp'; cases hsp'
      · exact elem_disjoint fsbB hti hui hne hcv hcv'
    · rcases Nat.lt_or_ge A.j k with hj | hj
      · rw [foot_after _ _ hj] at hw htc
        obtain ⟨hsp, h0, hcv⟩ := hw
        rcases htc with ⟨hsp', -⟩ | ⟨-, h0', -⟩
        · simp only at hsp hsp'; rw [hsp] at hsp'; cases hsp'
        · exact hne (h0.trans h0'.symm)
      · rw [foot_tree _ _ h1 hj] at hw htc
        obtain ⟨-, hlt, hcv⟩ := hw
        have hsf := stride_facts A hpre.1 (m := k - 1) (by omega)
        rw [show k - 1 + 1 = k by omega] at hsf
        rcases htc with ⟨-, hlt', hcv'⟩ | ⟨-, hlt', hcv'⟩
        · exact elem_disjoint fsbB hti (by omega) (by omega) hcv hcv'
        · exact elem_disjoint fsbB hti hui hne hcv hcv'
  · -- across CTAs, no global byte one writes is touched by another
    intro t ht u hu hc k _ j' _ a hw htc
    simp only [phased] at hw htc
    have hcne := A.cta_ne ht hu hc
    obtain ⟨htc', -⟩ := A.thread_facts hGB ht
    obtain ⟨huc', hui, -⟩ := A.thread_facts hGB hu
    have hwk : A.j < k := by
      refine Classical.byContradiction fun h => ?_
      rcases Nat.lt_or_ge k 1 with h0 | h1
      · obtain rfl : k = 0 := by omega
        rw [foot_zero] at hw; exact absurd hw.1 nofun
      · rw [foot_tree _ _ h1 (by omega)] at hw; exact absurd hw.1 nofun
    rw [foot_after _ _ hwk] at hw
    obtain ⟨-, -, hcv⟩ := hw
    rcases Nat.lt_or_ge j' 1 with h0 | h1
    · obtain rfl : j' = 0 := by omega
      rw [foot_zero] at htc
      rcases htc with ⟨-, hlt, hcv'⟩ | ⟨h, -⟩
      · exact elem_disjoint₂ fout fx hpre.2.2.2.2.2.2.2.1.symm htc' hlt hcv hcv'
      · exact absurd h nofun
    · rcases Nat.lt_or_ge A.j j' with hj | hj
      · rw [foot_after _ _ hj] at htc
        rcases htc with ⟨h, -⟩ | ⟨-, -, hcv'⟩
        · exact absurd h nofun
        · exact elem_disjoint fout htc' huc' hcne hcv hcv'
      · rw [foot_tree _ _ h1 hj] at htc
        rcases htc with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h nofun

end

/-- The class theorem for `per_block`: the obligations give `Correct`. -/
theorem correct_of {K : Kernel} {W : Nat} (hfit : Fit S K W) (C : Code S) (hO : Obligations K C) :
    Correct S K := by
  intro A hpre m₀ sh₀ r₀ p₀ L c₀
  have R := Phased.phase_sound (ok hfit C A hO hpre m₀ sh₀ r₀ p₀)
  have hB1 : 1 ≤ A.B.toNat := by rw [hpre.1]; exact Nat.one_le_two_pow
  refine ⟨R.noFault, R.progress, R.bounded, R.raceFree,
    Phased.exists_done_of R.progress R.bounded, fun c hc hd => ?_⟩
  obtain ⟨hw, hun, -⟩ := R.final c hc hd
  refine ⟨fun b hb => ?_, fun y hy => hun y ?_ (fun _ h => h.elim)⟩
  · -- thread 0 of CTA `b` wrote `out[b]` in the last phase
    obtain ⟨ht, hbt, -⟩ := A.th_of (len := A.G.toNat) (q := b) (r := 0) hb hB1
    have hmem : ∀ a, covers (elem A.out b) 4 a → c.mem a = _ := fun a hcv => by
      refine hw _ ht (A.j + 1) (by simp [phased]) a ?_
      show (foot A _ (A.j + 1)).w (.global, a)
      rw [foot_last]
      refine ⟨rfl, rfl, ?_⟩
      show covers (elem A.out (BitVec.ofNat 32 b).toNat) 4 a
      rw [hbt]; exact hcv
    rw [rd32_congr hmem]
    simp only [phased, mem, ↓reduceIte, hbt]
    rw [rd32_wr_same, lo32_ext32, V_final A hpre.1]
  · -- nobody writes outside `out`
    intro t ht k hk hwk
    simp only [phased] at hk hwk
    rcases Nat.lt_or_ge k 1 with h0 | h1
    · obtain rfl : k = 0 := by omega
      rw [foot_zero] at hwk; exact absurd hwk.1 nofun
    · rcases Nat.lt_or_ge A.j k with hj | hj
      · rw [foot_after _ _ hj] at hwk
        exact hy _ (A.thread_facts hpre.2.2.1 ht).1 hwk.2.2
      · rw [foot_tree _ _ h1 hj] at hwk; exact absurd hwk.1 nofun


/-! ### `atomic`: thread 0 of every block adds the block's sum to `*out` -/

namespace Atomic
open Ptx.Auto.Reduce32

section
variable (A : Block.Args S)

/-- As `foot`, but the last phase writes nothing: its atomic addition to
`*out` is the accumulator cell of the phase theorem, not a footprint. -/
def foot (t : Tid) (k : Nat) : Foot :=
  if k = 0 then
    { r := fun l => l.1 = .global ∧ t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat < A.n.toNat ∧
        covers (elem A.x (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)) 4 l.2
      w := fun l => l.1 = .shared ∧ covers (elem A.sb (t.tid.x.toNat)) 4 l.2 }
  else if k ≤ A.j then
    { r := fun l => l.1 = .shared ∧ t.tid.x.toNat < stride A k ∧
        covers (elem A.sb (t.tid.x.toNat + stride A k)) 4 l.2
      w := fun l => l.1 = .shared ∧ t.tid.x.toNat < stride A k ∧ covers (elem A.sb (t.tid.x.toNat)) 4 l.2 }
  else
    { r := fun l => l.1 = .shared ∧ t.tid.x.toNat = 0 ∧ covers (elem A.sb 0) 4 l.2
      w := fun _ => False }

def mem (m₀ : Mem) (sh₀ : Dim3 → Mem) (b : Dim3) : Nat → Heap
  | 0 => ⟨m₀, sh₀ b⟩
  | k + 1 => ⟨m₀, cells A.sb A.B.toNat (V A m₀ b.x.toNat (min k A.j)) (sh₀ b)⟩

def phased (C : Code S) (m₀ : Mem) (sh₀ : Dim3 → Mem) : Phased where
  P := fun _ => A.j + 2
  F := foot A
  T := C.Tc A m₀
  N := fun _ _ => C.N
  M := mem A m₀ sh₀
  bpc := fun _ k => C.bpc A k
  Cell := fun a => a = A.out
  Δ := fun t k a => if k = A.j + 1 ∧ t.tid.x.toNat = 0 ∧ a = A.out then ext32 (V A m₀ t.ctaid.x.toNat A.j 0) else 0

theorem foot_zero (t : Tid) : foot A t 0 =
    { r := fun l => l.1 = .global ∧ t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat < A.n.toNat ∧
        covers (elem A.x (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)) 4 l.2
      w := fun l => l.1 = .shared ∧ covers (elem A.sb t.tid.x.toNat) 4 l.2 } := rfl

theorem foot_tree (t : Tid) {k : Nat} (h1 : 1 ≤ k) (hk : k ≤ A.j) : foot A t k =
    { r := fun l => l.1 = .shared ∧ t.tid.x.toNat < stride A k ∧
        covers (elem A.sb (t.tid.x.toNat + stride A k)) 4 l.2
      w := fun l => l.1 = .shared ∧ t.tid.x.toNat < stride A k ∧ covers (elem A.sb t.tid.x.toNat) 4 l.2 } := by
  simp only [foot, show k ≠ 0 by omega, ↓reduceIte, hk]

theorem foot_after (t : Tid) {k : Nat} (hk : A.j < k) : foot A t k =
    { r := fun l => l.1 = .shared ∧ t.tid.x.toNat = 0 ∧ covers (elem A.sb 0) 4 l.2
      w := fun _ => False } := by
  simp only [foot, show k ≠ 0 by omega, show ¬ k ≤ A.j by omega, ↓reduceIte]

theorem foot_last (t : Tid) : foot A t (A.j + 1) =
    { r := fun l => l.1 = .shared ∧ t.tid.x.toNat = 0 ∧ covers (elem A.sb 0) 4 l.2
      w := fun _ => False } :=
  foot_after A t (by omega)

end

/-- The three phase obligations, for every launch in `Pre` (output: one word). -/
structure Obligations (K : Kernel) (C : Code S) : Prop where
  load : ∀ A : Block.Args S, Pre K 1 A → ∀ m₀ sh₀, ∀ t ∈ (A.launch 1).threads, ∀ s,
    C.Tc A m₀ t 0 s →
    Run K ((A.launch 1).allocs K) ((A.launch 1).ctx t) (foot A t 0) (fun a => a = A.out) add32
      ((phased A C m₀ sh₀).J K (A.launch 1) t 0) C.N s (mem A m₀ sh₀ t.ctaid 0) (fun _ => 0)
  tree : ∀ A : Block.Args S, Pre K 1 A → ∀ m₀ sh₀, ∀ t ∈ (A.launch 1).threads, ∀ m,
    m + 1 ≤ A.j → ∀ s, C.Tc A m₀ t (m + 1) s →
    Run K ((A.launch 1).allocs K) ((A.launch 1).ctx t) (foot A t (m + 1))
      (fun a => a = A.out) add32 ((phased A C m₀ sh₀).J K (A.launch 1) t (m + 1)) C.N s
      (mem A m₀ sh₀ t.ctaid (m + 1)) (fun _ => 0)
  last : ∀ A : Block.Args S, Pre K 1 A → ∀ m₀ sh₀, ∀ t ∈ (A.launch 1).threads, ∀ s,
    C.Tc A m₀ t (A.j + 1) s →
    Run K ((A.launch 1).allocs K) ((A.launch 1).ctx t) (foot A t (A.j + 1))
      (fun a => a = A.out) add32 ((phased A C m₀ sh₀).J K (A.launch 1) t (A.j + 1)) C.N s
      (mem A m₀ sh₀ t.ctaid (A.j + 1)) (fun _ => 0)

/-- What `atomic` claims about kernel `K`: for every launch in `Pre` (with a
one-word output), under every initial memory, shared memory and register
content, and every execution: no fault and no diverged barrier, progress,
bounded executions, phase-relative race freedom (the blocks' atomic
additions to `*out` are the only conflicting accesses), a finished execution
exists, and when all threads are done `*out` holds its initial value plus
`x[0] + … + x[min(n, G·B) - 1]` (mod 2^32), whatever order the blocks added
in, and no other byte has changed. -/
def Correct (S : Spec) (K : Kernel) : Prop :=
  ∀ A : Block.Args S, Pre K 1 A → ∀ (m₀ : Mem) (sh₀ : Dim3 → Mem) (r₀ : Tid → String → Val)
    (p₀ : Tid → String → Bool),
    let L := A.launch 1
    let c₀ := Cfg.init r₀ p₀ m₀ sh₀
    (∀ c, Reach K L c₀ c → ¬ Faults K L c) ∧
    (∀ c, Reach K L c₀ c → Done K L c ∨ ∃ c', Step K L c c') ∧
    (∃ bound, ∀ j c, Steps K L j c₀ c → j ≤ bound) ∧
    RaceFree K L c₀ ∧
    (∃ c, Reach K L c₀ c ∧ Done K L c) ∧
    (∀ c, Reach K L c₀ c → Done K L c →
      rd32 c.mem A.out = rd32 m₀ A.out +
        accUpTo (fun i => if i < A.n.toNat then rd32 m₀ (elem A.x i) else 0) (A.G.toNat * A.B.toNat) ∧
      (∀ y, ¬ covers A.out 4 y → c.mem y = m₀ y))

section
variable {K : Kernel} {W : Nat} (hfit : Fit S K W) (C : Code S) (A : Block.Args S)

include hfit in
theorem ok (hO : Obligations K C) (hpre : Pre K 1 A) (m₀ : Mem) (sh₀ : Dim3 → Mem)
    (r₀ : Tid → String → Val) (p₀ : Tid → String → Bool) :
    (phased A C m₀ sh₀).Ok K (A.launch 1) r₀ p₀ m₀ sh₀ := by
  obtain ⟨sal, fsbB, -, hB1⟩ := fits_sb hfit A hpre
  have fx := hpre.2.2.2.1
  have fout := hpre.2.2.2.2.2.1
  have hGB := hpre.2.2.1
  have hsep := hpre.2.2.2.2.2.2.2.1
  refine ⟨fun _ _ => by simp [phased], fun _ _ => rfl, fun _ _ _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht k hk s hs
    simp only [phased] at hk ⊢
    rcases Nat.lt_or_ge k 1 with h0 | h1
    · obtain rfl : k = 0 := by omega
      exact hO.load A hpre m₀ sh₀ t ht s hs
    · rcases Nat.lt_or_ge A.j k with hj | hj
      · obtain rfl : k = A.j + 1 := by omega
        exact hO.last A hpre m₀ sh₀ t ht s hs
      · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
        exact hO.tree A hpre m₀ sh₀ t ht m hj s hs
  · intro b k x hb hk hno
    simp only [phased] at hk hno ⊢
    have hb' := hb
    obtain ⟨t₀, ht₀, rfl⟩ := hb'
    obtain ⟨sp, y⟩ := x
    have cellOf : ∀ (h : (y - A.sb).toNat < 4 * A.B.toNat),
        th t₀.ctaid ((y - A.sb).toNat / 4) ∈ (A.launch 1).threads ∧
          (th t₀.ctaid ((y - A.sb).toNat / 4)).tid.x.toNat = (y - A.sb).toNat / 4 ∧
          covers (elem A.sb ((y - A.sb).toNat / 4)) 4 y :=
      fun h => ⟨(A.th_mem hb (i := (y - A.sb).toNat / 4) (by omega)).1,
        (A.th_mem hb (i := (y - A.sb).toNat / 4) (by omega)).2, covers_of_lt fsbB h⟩
    cases sp with
    | global => simp only [mem, Heap.get, Heap.at]; split <;> rfl
    | shared =>
      rcases Nat.lt_or_ge k 1 with h0 | h1
      · obtain rfl : k = 0 := by omega
        show cells A.sb A.B.toNat _ (sh₀ t₀.ctaid) y = sh₀ t₀.ctaid y
        unfold cells; split
        · next h =>
          obtain ⟨hm, hti, hcv⟩ := cellOf h
          have hnw := hno _ hm rfl
          rw [foot_zero] at hnw
          exact absurd ⟨rfl, by rw [hti]; exact hcv⟩ hnw
        · rfl
      · rcases Nat.lt_or_ge A.j k with hj | hj
        · obtain rfl : k = A.j + 1 := by omega
          show cells _ _ (V A m₀ _ (min (A.j + 1) A.j)) _ y = cells _ _ (V A m₀ _ (min A.j A.j)) _ y
          rw [show min (A.j + 1) A.j = A.j by omega, Nat.min_self]
        · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
          show cells _ _ (V A m₀ _ (min (m + 1) A.j)) _ y = cells _ _ (V A m₀ _ (min m A.j)) _ y
          rw [show min (m + 1) A.j = m + 1 by omega, show min m A.j = m by omega]
          apply cells_congr
          · intro h
            obtain ⟨hm, hti, hcv⟩ := cellOf h
            have hnw := hno _ hm rfl
            rw [foot_tree _ _ (by omega) hj] at hnw
            show (if _ < stride A (m + 1) then _ else _) = _
            split
            · next hl => exact absurd ⟨rfl, by rw [hti]; exact hl, by rw [hti]; exact hcv⟩ hnw
            · rfl
          · intro _; rfl
  · intro t ht u hu htu hc k _ x hw htc
    simp only [phased] at hw htc
    have hne := A.tid_ne ht hu hc htu
    obtain ⟨-, hti, -⟩ := A.thread_facts hGB ht
    obtain ⟨-, hui, -⟩ := A.thread_facts hGB hu
    obtain ⟨sp, y⟩ := x
    rcases Nat.lt_or_ge k 1 with h0 | h1
    · obtain rfl : k = 0 := by omega
      rw [foot_zero] at hw htc
      obtain ⟨hsp, hcv⟩ := hw
      rcases htc with ⟨hsp', -⟩ | ⟨-, hcv'⟩
      · simp only at hsp hsp'; rw [hsp] at hsp'; cases hsp'
      · exact elem_disjoint fsbB hti hui hne hcv hcv'
    · rcases Nat.lt_or_ge A.j k with hj | hj
      · rw [foot_after _ _ hj] at hw; exact hw
      · rw [foot_tree _ _ h1 hj] at hw htc
        obtain ⟨-, hlt, hcv⟩ := hw
        have hsf := stride_facts A hpre.1 (m := k - 1) (by omega)
        rw [show k - 1 + 1 = k by omega] at hsf
        rcases htc with ⟨-, hlt', hcv'⟩ | ⟨-, hlt', hcv'⟩
        · exact elem_disjoint fsbB hti (by omega) (by omega) hcv hcv'
        · exact elem_disjoint fsbB hti hui hne hcv hcv'
  · -- no thread writes global memory except through the cell
    intro t _ u _ _ k _ j' _ a hw _
    simp only [phased] at hw
    rcases Nat.lt_or_ge k 1 with h0 | h1
    · obtain rfl : k = 0 := by omega
      rw [foot_zero] at hw; exact absurd hw.1 nofun
    · rcases Nat.lt_or_ge A.j k with hj | hj
      · rw [foot_after _ _ hj] at hw; exact hw
      · rw [foot_tree _ _ h1 hj] at hw; exact absurd hw.1 nofun
  · -- the cell `*out` is in nobody's footprint
    intro t ht k a ha y hy htc
    simp only [phased] at ha htc
    subst ha
    have hc0 : covers (elem A.out 0) 4 y := by rw [elem_zero]; exact hy
    rcases Nat.lt_or_ge k 1 with h0 | h1
    · obtain rfl : k = 0 := by omega
      rw [foot_zero] at htc
      rcases htc with ⟨-, hlt, hcv⟩ | ⟨h, -⟩
      · exact elem_disjoint₂ fout fx (by omega) (by omega : 0 < 1) hlt hc0 hcv
      · exact absurd h nofun
    · rcases Nat.lt_or_ge A.j k with hj | hj
      · rw [foot_after _ _ hj] at htc
        rcases htc with ⟨h, -⟩ | h
        · exact absurd h nofun
        · exact h
      · rw [foot_tree _ _ h1 hj] at htc
        rcases htc with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h nofun
  · intro a b ha hb hab
    simp only [phased] at ha hb
    exact absurd (ha.trans hb.symm) hab

end

/-- The class theorem for `atomic`: the obligations give `Correct`. -/
theorem correct_of {K : Kernel} {W : Nat} (hfit : Fit S K W) (C : Code S) (hO : Obligations K C) :
    Correct S K := by
  intro A hpre m₀ sh₀ r₀ p₀ L c₀
  have R := Phased.phase_sound (ok hfit C A hO hpre m₀ sh₀ r₀ p₀)
  have hB1 : 1 ≤ A.B.toNat := by rw [hpre.1]; exact Nat.one_le_two_pow
  refine ⟨R.noFault, R.progress, R.bounded, R.raceFree,
    Phased.exists_done_of R.progress R.bounded, fun c hc hd => ?_⟩
  obtain ⟨-, hun, hcell⟩ := R.final c hc hd
  refine ⟨?_, fun y hy => hun y ?_ ?_⟩
  · rw [cell_add32 (hcell A.out rfl)]
    congr 1
    simp only [phased, lo32_tfold_add32]
    -- only phase `j + 1` of thread 0 of each block contributes
    rw [tsum_congr (g := fun t => if t.tid.x.toNat = 0 then V A m₀ t.ctaid.x.toNat A.j 0 else 0)
      fun t _ => ?_]
    · rw [tsum_oneD_first (v := fun c => V A m₀ c A.j 0) (A.launch_oneD 1) (by omega),
        ← accUpTo_blocks _ A.B.toNat]
      refine accUpTo_congr' fun b _ => ?_
      rw [V_final A hpre.1]
      rfl
    · by_cases h0 : t.tid.x.toNat = 0
      · simp only [h0, true_and, and_true, ↓reduceIte, lo32_afold_add32, lo32_ite_ext]
        exact accUpTo_single _ _ _ (by omega)
      · simp only [h0, false_and, and_false, ↓reduceIte, lo32_afold_add32, lo32_zero]
        exact accUpTo_zero _
  · intro t ht k hk hwk
    simp only [phased] at hk hwk
    rcases Nat.lt_or_ge k 1 with h0 | h1
    · obtain rfl : k = 0 := by omega
      rw [foot_zero] at hwk; exact absurd hwk.1 nofun
    · rcases Nat.lt_or_ge A.j k with hj | hj
      · rw [foot_after _ _ hj] at hwk; exact hwk
      · rw [foot_tree _ _ h1 hj] at hwk; exact absurd hwk.1 nofun
  · intro b hb; simp only [phased] at hb; subst hb; exact hy

end Atomic

end Ptx.Auto.Reduce32
