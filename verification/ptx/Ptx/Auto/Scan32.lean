/-
M4 check class `scan32`: Hillis-Steele inclusive block scans.

```c
s[tid] = i < n ? x[i] : 0;                    // phase 0, then bar.sync
for (off = 1; off < blockDim.x; off <<= 1) {
  unsigned t = tid >= off ? s[tid - off] : 0; // phase 2k + 1, then bar.sync
  s[tid] += t;                                // phase 2k + 2, then bar.sync
}
if (i < n) out[i] = s[tid];                   // phase 2R + 1
```

As in `reduce32` (Ptx/Auto/Reduce32.lean), the class theorem `correct_of`
is proved once from `phase_sound`, with the phase obligations, the only
part that depends on the instructions, as hypotheses.
-/
import Ptx.Auto.Block
import Ptx.Auto.Reduce32

set_option linter.unusedSimpArgs false

namespace Ptx.Auto.Scan32
open Ptx Ptx.Auto.Block
open Ptx.Auto.Reduce32 (Code accUpTo_congr)

variable {S : Spec}

/-- The launches the class theorem is about: blocks of `1 ≤ B ≤ 2^maxJ`
threads with `R = j` rounds (`B ≤ 2^R`, and `2^(R-1) < B` unless `R = 0`),
`G·B ≤ 2^32` threads covering `n`, input and output arrays of `n` words that
fit, are aligned and do not overlap, and any placement of the shared array
ptxas could choose. -/
def Pre (K : Kernel) (A : Block.Args S) : Prop :=
  1 ≤ A.B.toNat ∧ A.B.toNat ≤ 2 ^ S.maxJ ∧ A.B.toNat ≤ 2 ^ A.j ∧ (A.j = 0 ∨ 2 ^ (A.j - 1) < A.B.toNat) ∧
  A.G.toNat * A.B.toNat ≤ 2 ^ 32 ∧ A.n.toNat ≤ A.G.toNat * A.B.toNat ∧
  Fits A.x A.n.toNat ∧ A.x.toNat % 4 = 0 ∧ Fits A.out A.n.toNat ∧ A.out.toNat % 4 = 0 ∧
  (A.x.toNat + 4 * A.n.toNat ≤ A.out.toNat ∨ A.out.toNat + 4 * A.n.toNat ≤ A.x.toNat) ∧
  LayoutOk K A.sh

/-- What `s[i]` holds after round `k`. -/
def V (A : Block.Args S) (m₀ : Mem) (b : Nat) : Nat → Nat → BitVec 32
  | 0, i => A.seg m₀ b i
  | k + 1, i => if 2 ^ k ≤ i then V A m₀ b k i + V A m₀ b k (i - 2 ^ k) else V A m₀ b k i

/-- What thread `i` reads in round `k`. -/
def rv (A : Block.Args S) (m₀ : Mem) (b k i : Nat) : BitVec 32 :=
  if 2 ^ k ≤ i then V A m₀ b k (i - 2 ^ k) else 0

/-! ### The rounds compute window sums, and the last one the prefix sum -/

theorem accUpTo_add (f : Nat → BitVec 32) (a b : Nat) :
    accUpTo f (a + b) = accUpTo f a + accUpTo (fun m => f (a + m)) b := by
  induction b with
  | zero => simp [accUpTo]
  | succ b ih => rw [← Nat.add_assoc]; simp only [accUpTo]; rw [ih, BitVec.add_assoc]

theorem accUpTo_succ' (f : Nat → BitVec 32) (N : Nat) :
    accUpTo f (N + 1) = f 0 + accUpTo (fun m => f (m + 1)) N := by
  rw [Nat.add_comm, accUpTo_add]; simp [accUpTo, Nat.add_comm 1]

theorem accUpTo_rev (f : Nat → BitVec 32) : ∀ N, accUpTo f N = accUpTo (fun m => f (N - 1 - m)) N := by
  intro N
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [accUpTo_succ' (fun m => f (N + 1 - 1 - m)), show accUpTo f (N + 1) = accUpTo f N + f N from rfl, ih]
    rw [BitVec.add_comm]
    congr 1
    exact accUpTo_congr fun m hm => by congr 1; omega

section
variable (A : Block.Args S)

theorem V_window (m₀ : Mem) (b : Nat) : ∀ k i,
    V A m₀ b k i = accUpTo (fun m => A.seg m₀ b (i - m)) (min (2 ^ k) (i + 1)) := by
  intro k
  induction k with
  | zero => intro i; simp [V, accUpTo, show min 1 (i + 1) = 1 by omega]
  | succ k ih =>
    intro i
    have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    by_cases hi : 2 ^ k ≤ i
    · rw [show V A m₀ b (k + 1) i = V A m₀ b k i + V A m₀ b k (i - 2 ^ k) by simp [V, hi], ih, ih,
        show min (2 ^ (k + 1)) (i + 1) = 2 ^ k + min (2 ^ k) (i - 2 ^ k + 1) by omega,
        show min (2 ^ k) (i + 1) = 2 ^ k by omega, accUpTo_add]
      congr 1
      exact accUpTo_congr fun m _ => by congr 1; omega
    · rw [show V A m₀ b (k + 1) i = V A m₀ b k i by simp [V, hi], ih,
        show min (2 ^ (k + 1)) (i + 1) = i + 1 by omega, show min (2 ^ k) (i + 1) = i + 1 by omega]

/-- After the last round, `s[i]` is the prefix sum of the segment up to `i`. -/
theorem V_final (m₀ : Mem) (b : Nat) {i : Nat} (hi : i < 2 ^ A.j) :
    V A m₀ b A.j i = accUpTo (fun j => A.seg m₀ b j) (i + 1) := by
  rw [V_window, show min (2 ^ A.j) (i + 1) = i + 1 by omega, accUpTo_rev (fun j => A.seg m₀ b j)]
  exact accUpTo_congr fun m hm => by congr 1

/-! ### The phases: 0 loads; `2i+1` reads `s[tid - 2^i]`; `2i+2` adds it; `2R+1` stores -/

/-- What thread `t` touches in phase `p`. -/
def foot (t : Tid) (p : Nat) : Foot :=
  if p = 0 then
    { r := fun l => l.1 = .global ∧ t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat < A.n.toNat ∧
        covers (elem A.x (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)) 4 l.2
      w := fun l => l.1 = .shared ∧ covers (elem A.sb t.tid.x.toNat) 4 l.2 }
  else if p = 2 * A.j + 1 then
    { r := fun l => l.1 = .shared ∧ t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat < A.n.toNat ∧
        covers (elem A.sb t.tid.x.toNat) 4 l.2
      w := fun l => l.1 = .global ∧ t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat < A.n.toNat ∧
        covers (elem A.out (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)) 4 l.2 }
  else if p % 2 = 1 then
    { r := fun l => l.1 = .shared ∧ 2 ^ (p / 2) ≤ t.tid.x.toNat ∧
        covers (elem A.sb (t.tid.x.toNat - 2 ^ (p / 2))) 4 l.2
      w := fun _ => False }
  else
    { r := fun _ => False
      w := fun l => l.1 = .shared ∧ covers (elem A.sb t.tid.x.toNat) 4 l.2 }

/-- The outputs of CTA `b` after the last round. -/
def outs (m₀ : Mem) (b : Nat) : Mem :=
  cells (elem A.out (b * A.B.toNat)) (min A.B.toNat (A.n.toNat - b * A.B.toNat)) (V A m₀ b A.j) m₀

/-- CTA `b`'s view when phase `p` starts. -/
def mem (m₀ : Mem) (sh₀ : Dim3 → Mem) (b : Dim3) : Nat → Heap
  | 0 => ⟨m₀, sh₀ b⟩
  | p + 1 =>
    ⟨if p = 2 * A.j + 1 then outs A m₀ b.x.toNat else m₀,
     cells A.sb A.B.toNat (V A m₀ b.x.toNat (p / 2)) (sh₀ b)⟩

def phased (C : Code S) (m₀ : Mem) (sh₀ : Dim3 → Mem) : Phased where
  P := fun _ => 2 * A.j + 2
  F := foot A
  T := C.Tc A m₀
  N := fun _ _ => C.N
  M := mem A m₀ sh₀
  bpc := fun _ p => C.bpc A p
  Cell := fun _ => False
  Δ := fun _ _ _ => 0

theorem foot_load (t : Tid) : foot A t 0 =
    { r := fun l => l.1 = .global ∧ t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat < A.n.toNat ∧
        covers (elem A.x (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)) 4 l.2
      w := fun l => l.1 = .shared ∧ covers (elem A.sb t.tid.x.toNat) 4 l.2 } := rfl

theorem foot_read (t : Tid) {i : Nat} (hi : i < A.j) : foot A t (2 * i + 1) =
    { r := fun l => l.1 = .shared ∧ 2 ^ i ≤ t.tid.x.toNat ∧ covers (elem A.sb (t.tid.x.toNat - 2 ^ i)) 4 l.2
      w := fun _ => False } := by
  simp only [foot, show 2 * i + 1 ≠ 0 by omega, show 2 * i + 1 ≠ 2 * A.j + 1 by omega, ↓reduceIte,
    show (2 * i + 1) % 2 = 1 by omega, show (2 * i + 1) / 2 = i by omega]

theorem foot_add (t : Tid) {i : Nat} (_hi : i < A.j) : foot A t (2 * i + 2) =
    { r := fun _ => False, w := fun l => l.1 = .shared ∧ covers (elem A.sb t.tid.x.toNat) 4 l.2 } := by
  simp only [foot, show 2 * i + 2 ≠ 0 by omega, show 2 * i + 2 ≠ 2 * A.j + 1 by omega, ↓reduceIte,
    show (2 * i + 2) % 2 = 0 by omega, show ¬ (0 = 1) by decide]

theorem foot_store (t : Tid) : foot A t (2 * A.j + 1) =
    { r := fun l => l.1 = .shared ∧ t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat < A.n.toNat ∧
        covers (elem A.sb t.tid.x.toNat) 4 l.2
      w := fun l => l.1 = .global ∧ t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat < A.n.toNat ∧
        covers (elem A.out (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)) 4 l.2 } := by
  simp only [foot, show 2 * A.j + 1 ≠ 0 by omega, ↓reduceIte]

/-- Phase `p < 2R + 2` is the load, a read, an add, or the store. -/
theorem phase_cases {p : Nat} (hp : p < 2 * A.j + 2) :
    p = 0 ∨ (∃ i < A.j, p = 2 * i + 1) ∨ (∃ i < A.j, p = 2 * i + 2) ∨ p = 2 * A.j + 1 := by
  rcases Nat.mod_two_eq_zero_or_one p with h | h
  · by_cases h0 : p = 0
    · exact .inl h0
    · exact .inr (.inr (.inl ⟨p / 2 - 1, by omega, by omega⟩))
  · by_cases hR : p = 2 * A.j + 1
    · exact .inr (.inr (.inr hR))
    · exact .inr (.inl ⟨p / 2, by omega, by omega⟩)

end

/-- The four phase obligations, for every launch in `Pre`. -/
structure Obligations (K : Kernel) (C : Code S) : Prop where
  load : ∀ A : Block.Args S, Pre K A → ∀ m₀ sh₀, ∀ t ∈ (A.launch A.n.toNat).threads, ∀ s,
    C.Tc A m₀ t 0 s →
    Run K ((A.launch A.n.toNat).allocs K) ((A.launch A.n.toNat).ctx t) (foot A t 0) (fun _ => False)
      ((phased A C m₀ sh₀).J K (A.launch A.n.toNat) t 0) C.N s (mem A m₀ sh₀ t.ctaid 0) (fun _ => 0)
  read : ∀ A : Block.Args S, Pre K A → ∀ m₀ sh₀, ∀ t ∈ (A.launch A.n.toNat).threads, ∀ i < A.j, ∀ s,
    C.Tc A m₀ t (2 * i + 1) s →
    Run K ((A.launch A.n.toNat).allocs K) ((A.launch A.n.toNat).ctx t) (foot A t (2 * i + 1))
      (fun _ => False) ((phased A C m₀ sh₀).J K (A.launch A.n.toNat) t (2 * i + 1)) C.N s
      (mem A m₀ sh₀ t.ctaid (2 * i + 1)) (fun _ => 0)
  add : ∀ A : Block.Args S, Pre K A → ∀ m₀ sh₀, ∀ t ∈ (A.launch A.n.toNat).threads, ∀ i < A.j, ∀ s,
    C.Tc A m₀ t (2 * i + 2) s →
    Run K ((A.launch A.n.toNat).allocs K) ((A.launch A.n.toNat).ctx t) (foot A t (2 * i + 2))
      (fun _ => False) ((phased A C m₀ sh₀).J K (A.launch A.n.toNat) t (2 * i + 2)) C.N s
      (mem A m₀ sh₀ t.ctaid (2 * i + 2)) (fun _ => 0)
  store : ∀ A : Block.Args S, Pre K A → ∀ m₀ sh₀, ∀ t ∈ (A.launch A.n.toNat).threads, ∀ s,
    C.Tc A m₀ t (2 * A.j + 1) s →
    Run K ((A.launch A.n.toNat).allocs K) ((A.launch A.n.toNat).ctx t) (foot A t (2 * A.j + 1))
      (fun _ => False) ((phased A C m₀ sh₀).J K (A.launch A.n.toNat) t (2 * A.j + 1)) C.N s
      (mem A m₀ sh₀ t.ctaid (2 * A.j + 1)) (fun _ => 0)

/-- What `scan32` claims about kernel `K`: for every launch in `Pre`, under
every initial memory, shared memory and register content, and every
execution: no fault or diverged barrier, progress, bounded executions,
phase-relative race freedom, a finished execution exists, and when all
threads are done every `out[i]` (`i < n`) is the sum of `x[j]` from the
start of `i`'s block to `i`, and no other byte has changed. -/
def Correct (S : Spec) (K : Kernel) : Prop :=
  ∀ A : Block.Args S, Pre K A → ∀ (m₀ : Mem) (sh₀ : Dim3 → Mem) (r₀ : Tid → String → Val)
    (p₀ : Tid → String → Bool),
    let L := A.launch A.n.toNat
    let c₀ := Cfg.init r₀ p₀ m₀ sh₀
    (∀ c, Reach K L c₀ c → ¬ Faults K L c) ∧
    (∀ c, Reach K L c₀ c → Done K L c ∨ ∃ c', Step K L c c') ∧
    (∃ bound, ∀ j c, Steps K L j c₀ c → j ≤ bound) ∧
    RaceFree K L c₀ ∧
    (∃ c, Reach K L c₀ c ∧ Done K L c) ∧
    (∀ c, Reach K L c₀ c → Done K L c →
      (∀ i < A.n.toNat, rd32 c.mem (elem A.out i) =
        accUpTo (fun j => rd32 m₀ (elem A.x (i / A.B.toNat * A.B.toNat + j))) (i % A.B.toNat + 1)) ∧
      (∀ y, (∀ i < A.n.toNat, ¬ covers (elem A.out i) 4 y) → c.mem y = m₀ y))

section
variable {K : Kernel} {W : Nat} (hfit : Fit S K W) (C : Code S) (A : Block.Args S)

include hfit in
theorem fits_sb (hpre : Pre K A) :
    A.sb.toNat % 4 = 0 ∧ Fits A.sb A.B.toNat ∧ A.B.toNat ≤ W := by
  obtain ⟨sal, sbb, hW⟩ := A.sb_facts hfit hpre.2.2.2.2.2.2.2.2.2.2.2
  have hB := hpre.2.1
  refine ⟨sal, ?_, by omega⟩
  unfold Fits; omega

omit hfit in
/-- Every round's offset is below the block size. -/
theorem pow_lt (hpre : Pre K A) {i : Nat} (hi : i < A.j) : 2 ^ i < A.B.toNat := by
  rcases hpre.2.2.2.1 with h | h
  · omega
  · exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (by omega)) h

include hfit in
theorem ok (hO : Obligations K C) (hpre : Pre K A) (m₀ : Mem) (sh₀ : Dim3 → Mem)
    (r₀ : Tid → String → Val) (p₀ : Tid → String → Bool) :
    (phased A C m₀ sh₀).Ok K (A.launch A.n.toNat) r₀ p₀ m₀ sh₀ := by
  obtain ⟨sal, fsbB, -⟩ := fits_sb hfit A hpre
  have hB1 := hpre.1
  have hGB := hpre.2.2.2.2.1
  have fx := hpre.2.2.2.2.2.2.1
  have fout := hpre.2.2.2.2.2.2.2.2.1
  have hsep := hpre.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨fun _ _ => by simp [phased], fun _ _ => rfl, fun _ _ _ => rfl, ?_, ?_, ?_, ?_,
    fun _ _ _ _ h => h.elim, fun _ _ h => h.elim⟩
  · intro t ht k hk s hs
    simp only [phased] at hk ⊢
    rcases phase_cases A hk with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | rfl
    · exact hO.load A hpre m₀ sh₀ t ht s hs
    · exact hO.read A hpre m₀ sh₀ t ht i hi s hs
    · exact hO.add A hpre m₀ sh₀ t ht i hi s hs
    · exact hO.store A hpre m₀ sh₀ t ht s hs
  · intro b k x hb hk hno
    simp only [phased] at hk hno ⊢
    have hb' := hb
    obtain ⟨t₀, ht₀, rfl⟩ := hb'
    obtain ⟨sp, y⟩ := x
    have cellOf : ∀ (h : (y - A.sb).toNat < 4 * A.B.toNat),
        th t₀.ctaid ((y - A.sb).toNat / 4) ∈ (A.launch A.n.toNat).threads ∧
          (th t₀.ctaid ((y - A.sb).toNat / 4)).tid.x.toNat = (y - A.sb).toNat / 4 ∧
          covers (elem A.sb ((y - A.sb).toNat / 4)) 4 y :=
      fun h => ⟨(A.th_mem hb (i := (y - A.sb).toNat / 4) (by omega)).1,
        (A.th_mem hb (i := (y - A.sb).toNat / 4) (by omega)).2, covers_of_lt fsbB h⟩
    rcases phase_cases A hk with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | rfl
    · cases sp with
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
          rw [foot_load] at hnw
          exact absurd ⟨rfl, by rw [hti]; exact hcv⟩ hnw
        · rfl
    · cases sp with
      | global =>
        simp only [mem, Heap.get, Heap.at]
        repeat' split
        all_goals first | rfl | (exfalso; omega)
      | shared =>
        show cells _ _ (V A m₀ _ ((2 * i + 1) / 2)) _ y = cells _ _ (V A m₀ _ (2 * i / 2)) _ y
        rw [show (2 * i + 1) / 2 = i by omega, show 2 * i / 2 = i by omega]
    · cases sp with
      | global =>
        simp only [mem, Heap.get, Heap.at]
        repeat' split
        all_goals first | rfl | (exfalso; omega)
      | shared =>
        show cells _ _ (V A m₀ _ ((2 * i + 2) / 2)) _ y = cells _ _ (V A m₀ _ ((2 * i + 1) / 2)) _ y
        unfold cells; split
        · next h =>
          obtain ⟨hm, hti, hcv⟩ := cellOf h
          have hnw := hno _ hm rfl
          rw [foot_add _ _ hi] at hnw
          exact absurd ⟨rfl, by rw [hti]; exact hcv⟩ hnw
        · rfl
    · cases sp with
      | shared =>
        show cells _ _ (V A m₀ _ ((2 * A.j + 1) / 2)) _ y = cells _ _ (V A m₀ _ (2 * A.j / 2)) _ y
        rw [show (2 * A.j + 1) / 2 = A.j by omega, show 2 * A.j / 2 = A.j by omega]
      | global =>
        show (if 2 * A.j + 1 = 2 * A.j + 1 then _ else m₀) y = (if 2 * A.j = 2 * A.j + 1 then _ else m₀) y
        simp only [↓reduceIte, show 2 * A.j ≠ 2 * A.j + 1 by omega]
        show cells _ _ _ m₀ y = m₀ y
        unfold cells; split
        · next h =>
          exfalso
          have hcnt : (y - elem A.out (t₀.ctaid.x.toNat * A.B.toNat)).toNat / 4 <
              min A.B.toNat (A.n.toNat - t₀.ctaid.x.toNat * A.B.toNat) := by omega
          have hm := A.th_mem hb (i := (y - elem A.out (t₀.ctaid.x.toNat * A.B.toNat)).toNat / 4)
            (by omega)
          have hnw := hno _ hm.1 rfl
          rw [foot_store] at hnw
          have hf := fits_tail fout (c := t₀.ctaid.x.toNat * A.B.toNat)
            (M := min A.B.toNat (A.n.toNat - t₀.ctaid.x.toNat * A.B.toNat)) (by omega)
          have hlt : t₀.ctaid.x.toNat * A.B.toNat +
              (y - elem A.out (t₀.ctaid.x.toNat * A.B.toNat)).toNat / 4 < A.n.toNat := by omega
          refine hnw ⟨rfl, ?_, ?_⟩
          · show t₀.ctaid.x.toNat * A.B.toNat + (th t₀.ctaid _).tid.x.toNat < _
            rw [hm.2]; exact hlt
          show covers (elem A.out ((th t₀.ctaid _).ctaid.x.toNat * A.B.toNat +
            (th t₀.ctaid _).tid.x.toNat)) 4 y
          rw [hm.2, show (th t₀.ctaid _).ctaid = t₀.ctaid from rfl, ← elem_elem]
          exact covers_of_lt hf h
        · rfl
  · intro t ht u hu htu hc k hk x hw htc
    simp only [phased] at hk hw htc
    have hne := A.tid_ne ht hu hc htu
    obtain ⟨htc', hti, -⟩ := A.thread_facts hGB ht
    obtain ⟨huc', hui, -⟩ := A.thread_facts hGB hu
    have hcx : t.ctaid.x.toNat = u.ctaid.x.toNat := by rw [hc]
    obtain ⟨sp, y⟩ := x
    rcases phase_cases A hk with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | rfl
    · rw [foot_load] at hw htc
      obtain ⟨hsp, hcv⟩ := hw
      rcases htc with ⟨hsp', -⟩ | ⟨-, hcv'⟩
      · simp only at hsp hsp'; rw [hsp] at hsp'; cases hsp'
      · exact elem_disjoint fsbB hti hui hne hcv hcv'
    · rw [foot_read _ _ hi] at hw; exact hw
    · rw [foot_add _ _ hi] at hw htc
      rcases htc with h | ⟨-, hcv'⟩
      · exact h
      · exact elem_disjoint fsbB hti hui hne hw.2 hcv'
    · rw [foot_store] at hw htc
      obtain ⟨hsp, hlt, hcv⟩ := hw
      rcases htc with ⟨hsp', -⟩ | ⟨-, hlt', hcv'⟩
      · simp only at hsp hsp'; rw [hsp] at hsp'; cases hsp'
      · exact elem_disjoint fout hlt hlt' (by rw [hcx]; omega) hcv hcv'
  · intro t ht u hu hc k hk j' hj a hw htc
    simp only [phased] at hk hj hw htc
    obtain ⟨htc', hti, -⟩ := A.thread_facts hGB ht
    obtain ⟨huc', hui, -⟩ := A.thread_facts hGB hu
    have hkS : k = 2 * A.j + 1 := by
      rcases phase_cases A hk with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | rfl
      · rw [foot_load] at hw; exact absurd hw.1 nofun
      · rw [foot_read _ _ hi] at hw; exact hw.elim
      · rw [foot_add _ _ hi] at hw; exact absurd hw.1 nofun
      · rfl
    subst hkS
    rw [foot_store] at hw
    obtain ⟨-, hlt, hcv⟩ := hw
    have hgid := A.gid_ne ht hu hc
    rcases phase_cases A hj with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | rfl
    · rw [foot_load] at htc
      rcases htc with ⟨-, hlt', hcv'⟩ | ⟨h, -⟩
      · exact elem_disjoint₂ fout fx (by omega) hlt hlt' hcv hcv'
      · exact absurd h nofun
    · rw [foot_read _ _ hi] at htc
      rcases htc with ⟨h, -⟩ | h
      · exact absurd h nofun
      · exact h
    · rw [foot_add _ _ hi] at htc
      rcases htc with h | ⟨h, -⟩
      · exact h
      · exact absurd h nofun
    · rw [foot_store] at htc
      rcases htc with ⟨h, -⟩ | ⟨-, hlt', hcv'⟩
      · exact absurd h nofun
      · exact elem_disjoint fout hlt hlt' hgid hcv hcv'

end

/-- The class theorem: the obligations give `Correct`. -/
theorem correct_of {K : Kernel} {W : Nat} (hfit : Fit S K W) (C : Code S) (hO : Obligations K C) :
    Correct S K := by
  intro A hpre m₀ sh₀ r₀ p₀ L c₀
  have R := Phased.phase_sound (ok hfit C A hO hpre m₀ sh₀ r₀ p₀)
  have hB1 := hpre.1
  have hBR := hpre.2.2.1
  have hnGB := hpre.2.2.2.2.2.1
  have fout := hpre.2.2.2.2.2.2.2.2.1
  refine ⟨R.noFault, R.progress, R.bounded, R.raceFree,
    Phased.exists_done_of R.progress R.bounded, fun c hc hd => ?_⟩
  obtain ⟨hw, hun, -⟩ := R.final c hc hd
  refine ⟨fun i hi => ?_, fun y hy => hun y ?_ (fun _ h => h.elim)⟩
  · -- thread `i % B` of CTA `i / B` wrote `out[i]` in the last phase
    have hq : i / A.B.toNat < A.G.toNat := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
    have hr : i % A.B.toNat < A.B.toNat := Nat.mod_lt _ (by omega)
    have hgi : i / A.B.toNat * A.B.toNat + i % A.B.toNat = i := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod i A.B.toNat
    generalize i / A.B.toNat = q at hq hgi ⊢
    generalize i % A.B.toNat = r at hr hgi ⊢
    subst hgi
    obtain ⟨ht, hc', ht'⟩ := A.th_of (len := A.n.toNat) hq hr
    have hmem : ∀ a, covers (elem A.out (q * A.B.toNat + r)) 4 a → c.mem a = _ := fun a hcv => by
      refine hw _ ht (2 * A.j + 1) (by simp [phased]) a ?_
      show (foot A _ (2 * A.j + 1)).w (.global, a)
      rw [foot_store]
      refine ⟨rfl, ?_, ?_⟩
      · show (BitVec.ofNat 32 q).toNat * A.B.toNat + (BitVec.ofNat 32 r).toNat < _
        rw [hc', ht']; exact hi
      · show covers (elem A.out ((BitVec.ofNat 32 q).toNat * A.B.toNat + (BitVec.ofNat 32 r).toNat)) 4 a
        rw [hc', ht']; exact hcv
    rw [rd32_congr hmem]
    simp only [phased, mem, ↓reduceIte, hc', outs]
    rw [← elem_elem,
      rd32_cells (fits_tail fout (c := q * A.B.toNat) (M := _) (by omega)) (by omega),
      V_final A m₀ _ (by omega)]
    refine accUpTo_congr fun j hj => ?_
    simp only [Block.Args.seg]
    split <;> first | rfl | (exfalso; omega)
  · intro t ht k hk hwk
    simp only [phased] at hk hwk
    rcases phase_cases A hk with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | rfl
    · rw [foot_load] at hwk; exact absurd hwk.1 nofun
    · rw [foot_read _ _ hi] at hwk; exact hwk
    · rw [foot_add _ _ hi] at hwk; exact absurd hwk.1 nofun
    · rw [foot_store] at hwk
      exact hy _ hwk.2.1 hwk.2.2

end Ptx.Auto.Scan32
