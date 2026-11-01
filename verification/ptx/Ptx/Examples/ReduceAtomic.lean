/-
M4: the block tree reduction finished with one `atomicAdd` per block, as nvcc
13.2 emits it (benchmarks/correct/reduce_atomic_nvcc.{cu,ptx}), verified on its
PTX for every power-of-two block size up to 1024, every grid size and every
input length. The tree phases are those of Ptx/Examples/Reduce.lean (other
registers); the last phase adds `s[0]` to `*out` with `atom.global.add.u32`,
an accumulator cell of the phase theorem, so `*out` ends as its initial value
plus the sum of every block's contribution, whatever order the blocks add
in.

```c
__shared__ unsigned s[1024];
s[tid] = i < n ? x[i] : 0;            // phase 0, then bar.sync
for (k = blockDim.x / 2; k > 0; k >>= 1) {
  if (tid < k) s[tid] += s[tid + k];  // phases 1 .. j, each ending at bar.sync
  __syncthreads();
}
if (tid == 0) atomicAdd(out, s[0]);   // phase j + 1
```
-/
import Ptx.Logic.PhaseSound
import Ptx.Logic.PhaseWp
import Ptx.Logic.Cells
import Ptx.Tactics.EvalR
import Ptx.Auto.Tactic4
import Ptx.Kernels.ReduceAtomicNvcc
import Ptx.Logic.Sums
import Ptx.Examples.Reduce

set_option linter.unusedSimpArgs false

namespace Ptx.Examples.ReduceAtomic
open Ptx

abbrev K := Ptx.Kernels.ReduceAtomicNvcc.«reduce_atomic»

/-- The launch-time values the theorem quantifies over. The block has
`B = 2^j` threads. -/
structure Args where
  G : BitVec 32
  B : BitVec 32
  j : Nat
  n : BitVec 32
  x : Addr
  out : Addr
  sh : String → Addr

namespace Args
variable (A : Args)

def sb : Addr := A.sh "_ZZ13reduce_atomicE1s"

def params : String → Val := fun p =>
  if p = "reduce_atomic_param_0" then A.x else if p = "reduce_atomic_param_1" then A.out
  else if p = "reduce_atomic_param_2" then ext32 A.n else 0

def launch : Launch :=
  { grid := ⟨A.G, 1, 1⟩, block := ⟨A.B, 1, 1⟩, params := A.params,
    alloc := [⟨A.x, 4 * A.n.toNat⟩, ⟨A.out, 4⟩], shared := A.sh }

def Pre : Prop :=
  A.B.toNat = 2 ^ A.j ∧ A.j ≤ 10 ∧ A.G.toNat * A.B.toNat ≤ 2 ^ 32 ∧
  Fits A.x A.n.toNat ∧ A.x.toNat % 4 = 0 ∧ Fits A.out 1 ∧ A.out.toNat % 4 = 0 ∧
  (A.x.toNat + 4 * A.n.toNat ≤ A.out.toNat ∨ A.out.toNat + 4 ≤ A.x.toNat) ∧
  LayoutOk K A.sh

/-- Element `i` of CTA `b`'s segment, `0` past the end of the input. -/
def seg (m₀ : Mem) (b i : Nat) : BitVec 32 :=
  if b * A.B.toNat + i < A.n.toNat then rd32 m₀ (elem A.x (b * A.B.toNat + i)) else 0

/-- The stride of phase `k`. -/
def stride (k : Nat) : Nat := A.B.toNat / 2 ^ k

/-- What `s[i]` holds after phase `k` (`k ≤ j`). -/
def V (m₀ : Mem) (b : Nat) : Nat → Nat → BitVec 32
  | 0, i => A.seg m₀ b i
  | k + 1, i => if i < A.stride (k + 1) then V m₀ b k i + V m₀ b k (i + A.stride (k + 1)) else V m₀ b k i

end Args

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

namespace Args
variable (A : Args)

theorem stride_eq (hB : A.B.toNat = 2 ^ A.j) {k : Nat} (hk : k ≤ A.j) :
    A.stride k = 2 ^ (A.j - k) := by
  unfold stride; rw [hB]; exact Nat.pow_div hk (by decide)

theorem stride_succ (hB : A.B.toNat = 2 ^ A.j) {k : Nat} (hk : k + 1 ≤ A.j) :
    A.stride k = 2 * A.stride (k + 1) := by
  rw [A.stride_eq hB (by omega), A.stride_eq hB hk, show A.j - k = (A.j - (k + 1)) + 1 by omega,
    Nat.pow_succ, Nat.mul_comm]

theorem V_tree (hB : A.B.toNat = 2 ^ A.j) (m₀ : Mem) (b : Nat) : ∀ k ≤ A.j, ∀ i < A.stride k,
    A.V m₀ b k i = accUpTo (fun m => A.V m₀ b 0 (i + m * A.stride k)) (2 ^ k) := by
  intro k
  induction k with
  | zero =>
    intro _ i _
    simp [accUpTo]
  | succ k ih =>
    intro hk i hi
    have h2 := A.stride_succ hB hk
    have hik : i < A.stride k := by omega
    have hik' : i + A.stride (k + 1) < A.stride k := by omega
    rw [show A.V m₀ b (k + 1) i = A.V m₀ b k i + A.V m₀ b k (i + A.stride (k + 1)) by
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

/-! ### The phases -/

/-- What thread `t` touches in phase `k`: in phase 0 it reads its input
element and writes `s[tid]`; in the tree phases, if `tid < stride`, it reads
`s[tid + stride]` and updates `s[tid]`; in the last phase thread 0 reads
`s[0]` (its atomic addition to `*out` is the accumulator cell, not a
footprint). -/
def foot (t : Tid) (k : Nat) : Foot :=
  if k = 0 then
    { r := fun l => l.1 = .global ∧ t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat < A.n.toNat ∧
        covers (elem A.x (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)) 4 l.2
      w := fun l => l.1 = .shared ∧ covers (elem A.sb (t.tid.x.toNat)) 4 l.2 }
  else if k ≤ A.j then
    { r := fun l => l.1 = .shared ∧ t.tid.x.toNat < A.stride k ∧ covers (elem A.sb (t.tid.x.toNat + A.stride k)) 4 l.2
      w := fun l => l.1 = .shared ∧ t.tid.x.toNat < A.stride k ∧ covers (elem A.sb (t.tid.x.toNat)) 4 l.2 }
  else
    { r := fun l => l.1 = .shared ∧ t.tid.x.toNat = 0 ∧ covers (elem A.sb 0) 4 l.2
      w := fun _ => False }

/-- CTA `b`'s view when phase `k` starts. -/
def mem (m₀ : Mem) (sh₀ : Dim3 → Mem) (b : Dim3) : Nat → Heap
  | 0 => ⟨m₀, sh₀ b⟩
  | k + 1 => ⟨m₀, cells A.sb A.B.toNat (A.V m₀ b.x.toNat (min k A.j)) (sh₀ b)⟩

def regsOk (t : Tid) (s : TState) : Prop :=
  s.r "%r12" = ext32 t.ctaid.x ∧ s.r "%r2" = ext32 t.tid.x ∧
  s.r "%r6" = ext32 (BitVec.ofNat 32 (A.sb.toNat + 4 * t.tid.x.toNat)) ∧ s.r "%rd2" = A.out

/-- The registers at the start of each phase. -/
def T (t : Tid) : Nat → TState → Prop
  | 0, s => s.pc = 0
  | 1, s => s.pc = 19 ∧ s.r "%r1" = ext32 A.B ∧ A.regsOk t s
  | k + 2, s => s.pc = 31 ∧ s.r "%r23" = ext32 (BitVec.ofNat 32 (A.stride (k + 1))) ∧ A.regsOk t s

def phased (m₀ : Mem) (sh₀ : Dim3 → Mem) : Phased where
  P := fun _ => A.j + 2
  F := A.foot
  T := A.T
  N := fun _ _ => 40
  M := A.mem m₀ sh₀
  bpc := fun _ k => if k = 0 then 18 else 30
  Cell := fun a => a = A.out
  Δ := fun t k a => if k = A.j + 1 ∧ t.tid.x.toNat = 0 ∧ a = A.out then A.V m₀ t.ctaid.x.toNat A.j 0 else 0

/-- After phase `j`, `s[0]` holds the sum of the segment. -/
theorem V_final (hB : A.B.toNat = 2 ^ A.j) (m₀ : Mem) (b : Nat) :
    A.V m₀ b A.j 0 = accUpTo (fun m => A.seg m₀ b m) A.B.toNat := by
  have h1 : A.stride A.j = 1 := by rw [A.stride_eq hB (Nat.le_refl _)]; simp
  rw [A.V_tree hB m₀ b A.j (Nat.le_refl _) 0 (by omega), h1, ← hB]
  exact accUpTo_congr fun m _ => by simp [V]


theorem launch_oneD : A.launch.OneD A.G A.B := ⟨rfl, rfl⟩

omit A in
theorem lo32_ofInt_zero : lo32 (BitVec.ofInt 64 0) = 0 := by decide

theorem sb_facts (hpre : A.Pre) : A.sb.toNat % 4 = 0 ∧ A.sb.toNat + 4096 ≤ 2 ^ 32 :=
  hpre.2.2.2.2.2.2.2.2.1 ⟨"_ZZ13reduce_atomicE1s", 4, 4096⟩ (by simp [K, Ptx.Kernels.ReduceAtomicNvcc.reduce_atomic])

theorem B_le (hpre : A.Pre) : A.B.toNat ≤ 1024 := by
  have := Nat.pow_le_pow_right (show 0 < 2 by decide) hpre.2.1
  rw [hpre.1]; simpa using this

/-- The index facts of one thread. -/
theorem thread_facts (hpre : A.Pre) {t : Tid} (ht : t ∈ A.launch.threads) :
    t.ctaid.x.toNat < A.G.toNat ∧ t.tid.x.toNat < A.B.toNat ∧ A.B.toNat ≤ 1024 ∧
      t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat < A.G.toNat * A.B.toNat ∧ A.G.toNat * A.B.toNat ≤ 2 ^ 32 ∧
      t.ctaid.y = 0 ∧ t.ctaid.z = 0 ∧ t.tid.y = 0 ∧ t.tid.z = 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := A.launch_oneD.thread ht
  exact ⟨h1, h2, A.B_le hpre, gid_lt_of h1 h2, hpre.2.2.1, h3, h4, h5, h6⟩

set_option maxHeartbeats 2000000 in
theorem phase0 (hpre : A.Pre) (m₀ : Mem) (sh₀ : Dim3 → Mem) {t : Tid} (ht : t ∈ A.launch.threads)
    (s : TState) (hs : A.T t 0 s) :
    Run K (A.launch.allocs K) (A.launch.ctx t) (A.foot t 0) (fun a => a = A.out)
      ((A.phased m₀ sh₀).J K A.launch t 0) 40 s (A.mem m₀ sh₀ t.ctaid 0) (fun _ => 0) := by
  obtain ⟨pc, r, p⟩ := s
  simp only [T] at hs; subst hs
  obtain ⟨hc, hi, hB, hcB, hGB, -, -, -, -⟩ := A.thread_facts hpre ht
  obtain ⟨sal, sbb⟩ := A.sb_facts hpre
  have fx := hpre.2.2.2.1
  have fsb : Fits A.sb 1024 := by unfold Fits; omega
  refine (wpR_sound (cut := fun _ => false) ?_).weaken fun s h d hq => hq.1
  simp only [ptx_eval, K, Ptx.Kernels.ReduceAtomicNvcc.reduce_atomic, launch, params, mem, Phased.J, phased,
    List.map_cons, List.map_nil]
  simp only [show A.sh "_ZZ13reduce_atomicE1s" = A.sb from rfl]
  ptx_addrs [A.sb, A.x] [t.tid.x.toNat, t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat]
  have fsbB : Fits A.sb A.B.toNat := by unfold Fits at fsb ⊢; omega
  have xal := hpre.2.2.2.2.1
  have hcB' : t.ctaid.x.toNat * A.B.toNat < 2 ^ 32 := by omega
  ptx_branches
  all_goals (try and_intros)
  all_goals first
    | trivial
    | (intro _ h; exact h.elim)
    | (funext a; split
       · next h => first | exact absurd h.1 (by omega) | exact absurd h.2.1 (by omega)
       · rfl)
    | (exfalso; omega)
    | exact accessOk_elem_mem (N := 1024) (by simp) fsb sal (by omega)
    | exact accessOk_elem_mem (N := A.n.toNat) (by simp) fx xal (by omega)
    | exact fun y hy => ⟨rfl, hy⟩
    | exact fun y hy => .inl ⟨rfl, by omega, hy⟩
    | (rintro ⟨sp, y⟩ ⟨hsp, hy⟩
       try simp only at hsp
       subst hsp
       refine wr_cells fsbB hi hy ?_
       simp only [V, seg, Nat.zero_min, lo32_ext32, lo32_rd_b4, lo32_ofInt_zero]
       split <;> first | rfl | (exfalso; omega))
    | (simp only [T, regsOk, upd, String.reduceEq, ↓reduceIte, true_and, and_true]
       all_goals (try and_intros)
       all_goals ptx_reg)
    | skip

theorem foot_zero (t : Tid) : A.foot t 0 =
    { r := fun l => l.1 = .global ∧ t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat < A.n.toNat ∧
        covers (elem A.x (t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat)) 4 l.2
      w := fun l => l.1 = .shared ∧ covers (elem A.sb t.tid.x.toNat) 4 l.2 } := rfl

theorem foot_tree (t : Tid) {k : Nat} (h1 : 1 ≤ k) (hk : k ≤ A.j) : A.foot t k =
    { r := fun l => l.1 = .shared ∧ t.tid.x.toNat < A.stride k ∧
        covers (elem A.sb (t.tid.x.toNat + A.stride k)) 4 l.2
      w := fun l => l.1 = .shared ∧ t.tid.x.toNat < A.stride k ∧ covers (elem A.sb t.tid.x.toNat) 4 l.2 } := by
  simp only [foot, show k ≠ 0 by omega, ↓reduceIte, hk]

theorem foot_after (t : Tid) {k : Nat} (hk : A.j < k) : A.foot t k =
    { r := fun l => l.1 = .shared ∧ t.tid.x.toNat = 0 ∧ covers (elem A.sb 0) 4 l.2
      w := fun _ => False } := by
  simp only [foot, show k ≠ 0 by omega, show ¬ k ≤ A.j by omega, ↓reduceIte]

theorem foot_last (t : Tid) : A.foot t (A.j + 1) =
    { r := fun l => l.1 = .shared ∧ t.tid.x.toNat = 0 ∧ covers (elem A.sb 0) 4 l.2
      w := fun _ => False } :=
  A.foot_after t (by omega)

theorem stride_facts (hpre : A.Pre) {m : Nat} (hm : m + 1 ≤ A.j) :
    1 ≤ A.stride (m + 1) ∧ A.stride m = 2 * A.stride (m + 1) ∧ A.stride m ≤ A.B.toNat ∧
      A.B.toNat / 2 ^ 1 = A.stride 1 := by
  have h1 := A.stride_eq hpre.1 hm
  have h2 := A.stride_succ hpre.1 hm
  refine ⟨by rw [h1]; exact Nat.one_le_two_pow, h2, Nat.div_le_self _ _, rfl⟩

set_option maxHeartbeats 4000000 in
theorem phase_tree (hpre : A.Pre) (m₀ : Mem) (sh₀ : Dim3 → Mem) {t : Tid} (ht : t ∈ A.launch.threads)
    {m : Nat} (hm : m + 1 ≤ A.j) (s : TState) (hs : A.T t (m + 1) s) :
    Run K (A.launch.allocs K) (A.launch.ctx t) (A.foot t (m + 1)) (fun a => a = A.out)
      ((A.phased m₀ sh₀).J K A.launch t (m + 1)) 40 s (A.mem m₀ sh₀ t.ctaid (m + 1)) (fun _ => 0) := by
  obtain ⟨hc, hi, hB, hcB, hGB, -, -, -, -⟩ := A.thread_facts hpre ht
  obtain ⟨sal, sbb⟩ := A.sb_facts hpre
  have fsb : Fits A.sb 1024 := by unfold Fits; omega
  have fsbB : Fits A.sb A.B.toNat := by unfold Fits at fsb ⊢; omega
  obtain ⟨hh1, hh2, hh3, hh4⟩ := A.stride_facts hpre hm
  have hmin : min m A.j = m := Nat.min_eq_left (by omega)
  have hne : m ≠ A.j + 1 := by omega
  have hmin1 : min (m + 1) A.j = m + 1 := Nat.min_eq_left hm
  have xal := hpre.2.2.2.2.1
  obtain ⟨pc, r, p⟩ := s
  rcases m with _ | m'
  · simp only [Nat.zero_add] at hh1 hh2 hh3 hmin1 hm ⊢
    simp only [T, regsOk] at hs
    obtain ⟨rfl, hr1, hr2, hr3, hr6, hrd2⟩ := hs
    refine (wpR_sound (cut := fun _ => false) ?_).weaken fun s h d hq => hq.1
    have hh4' : A.B.toNat / 2 = A.stride 1 := by simpa using hh4
    simp only [ptx_eval, K, Ptx.Kernels.ReduceAtomicNvcc.reduce_atomic, launch, params, mem, Phased.J, phased,
      List.map_cons, List.map_nil, hr1, hr2, hr3, hr6, hrd2, A.foot_tree t (k := 1) (by omega) hm]
    simp only [show A.sh "_ZZ13reduce_atomicE1s" = A.sb from rfl]
    ptx_branches4
    all_goals ptx_addrs4 [A.sb] [t.tid.x.toNat, t.tid.x.toNat + A.stride 1]
    all_goals (try and_intros)
    all_goals first
      | trivial
      | (intro _ h; exact h.elim)
      | (funext a; split
         · next h => first | exact absurd h.1 (by omega) | exact absurd h.2.1 (by omega)
         · rfl)
      | (exfalso; omega)
      | exact accessOk_elem_mem (N := 1024) (by simp) fsb sal (by omega)
      | exact fun y hy => ⟨trivial, by omega, hy⟩
      | exact fun y hy => .inl ⟨trivial, by omega, hy⟩
      | exact fun y hy => .inr ⟨trivial, by omega, hy⟩
      | exact fun y hy => ⟨rfl, by omega, hy⟩
      | exact fun y hy => .inl ⟨rfl, by omega, hy⟩
      | exact fun y hy => .inr ⟨rfl, by omega, hy⟩
      | (rintro ⟨sp, y⟩ ⟨-, hlt, -⟩; exfalso; omega)
      | (rintro ⟨sp, y⟩ ⟨hsp, hlt, hy⟩
         try simp only at hsp
         subst hsp
         refine wr_cells fsbB hi hy ?_
         simp only [lo32_ext32, lo32_rd_b4, hmin, hmin1]
         rw [rd32_cells fsbB hi, rd32_cells fsbB (by omega)]
         simp only [V, hlt, ↓reduceIte])
      | (simp only [T, regsOk, upd, String.reduceEq, ↓reduceIte, true_and, and_true]
         all_goals (try and_intros)
         all_goals ptx_reg4)
      | skip
    done
  · simp only [T, regsOk] at hs
    obtain ⟨rfl, hr22, hr2, hr3, hr6, hrd2⟩ := hs
    have hst : A.stride (m' + 1) ≤ 1024 := by omega
    refine (wpR_sound (cut := fun _ => false) ?_).weaken fun s h d hq => hq.1
    simp only [ptx_eval, K, Ptx.Kernels.ReduceAtomicNvcc.reduce_atomic, launch, params, mem, Phased.J, phased,
      List.map_cons, List.map_nil, hr22, hr2, hr3, hr6, hrd2, A.foot_tree t (k := m' + 1 + 1) (by omega) hm]
    simp only [show A.sh "_ZZ13reduce_atomicE1s" = A.sb from rfl]
    ptx_branches4
    all_goals ptx_addrs4 [A.sb] [t.tid.x.toNat, t.tid.x.toNat + A.stride (m' + 1 + 1)]
    all_goals (try and_intros)
    all_goals first
      | trivial
      | (intro _ h; exact h.elim)
      | (funext a; split
         · next h => first | exact absurd h.1 (by omega) | exact absurd h.2.1 (by omega)
         · rfl)
      | (exfalso; omega)
      | exact accessOk_elem_mem (N := 1024) (by simp) fsb sal (by omega)
      | exact fun y hy => ⟨trivial, by omega, hy⟩
      | exact fun y hy => .inl ⟨trivial, by omega, hy⟩
      | exact fun y hy => .inr ⟨trivial, by omega, hy⟩
      | exact fun y hy => ⟨rfl, by omega, hy⟩
      | exact fun y hy => .inl ⟨rfl, by omega, hy⟩
      | exact fun y hy => .inr ⟨rfl, by omega, hy⟩
      | (rintro ⟨sp, y⟩ ⟨-, hlt, -⟩; exfalso; omega)
      | (rintro ⟨sp, y⟩ ⟨hsp, hlt, hy⟩
         try simp only at hsp
         subst hsp
         refine wr_cells fsbB hi hy ?_
         simp only [lo32_ext32, lo32_rd_b4, hmin, hmin1]
         rw [rd32_cells fsbB hi, rd32_cells fsbB (by omega)]
         simp only [V, hlt, ↓reduceIte])
      | (simp only [T, regsOk, upd, String.reduceEq, ↓reduceIte, true_and, and_true]
         all_goals (try and_intros)
         all_goals ptx_reg4)
      | skip
    done

theorem T_last {t : Tid} {pc : Nat} {r : String → Val} {p : String → Bool}
    (hs : A.T t (A.j + 1) ⟨pc, r, p⟩) :
    (pc = 19 ∧ A.j = 0 ∧ r "%r1" = ext32 A.B ∧ r "%r12" = ext32 t.ctaid.x ∧ r "%r2" = ext32 t.tid.x ∧
      r "%r6" = ext32 (BitVec.ofNat 32 (A.sb.toNat + 4 * t.tid.x.toNat)) ∧ r "%rd2" = A.out) ∨
    (pc = 31 ∧ 1 ≤ A.j ∧ r "%r23" = ext32 (BitVec.ofNat 32 (A.stride A.j)) ∧
      r "%r12" = ext32 t.ctaid.x ∧ r "%r2" = ext32 t.tid.x ∧
      r "%r6" = ext32 (BitVec.ofNat 32 (A.sb.toNat + 4 * t.tid.x.toNat)) ∧ r "%rd2" = A.out) := by
  rcases hj : A.j with _ | j' <;> rw [hj] at hs <;> simp only [T, regsOk] at hs
  · exact .inl ⟨hs.1, rfl, hs.2⟩
  · exact .inr ⟨hs.1, by omega, hs.2⟩

set_option maxHeartbeats 4000000 in
theorem phase_last (hpre : A.Pre) (m₀ : Mem) (sh₀ : Dim3 → Mem) {t : Tid} (ht : t ∈ A.launch.threads)
    (s : TState) (hs : A.T t (A.j + 1) s) :
    Run K (A.launch.allocs K) (A.launch.ctx t) (A.foot t (A.j + 1)) (fun a => a = A.out)
      ((A.phased m₀ sh₀).J K A.launch t (A.j + 1)) 40 s (A.mem m₀ sh₀ t.ctaid (A.j + 1))
      (fun _ => 0) := by
  obtain ⟨hc, hi, hB, hcB, hGB, -, -, -, -⟩ := A.thread_facts hpre ht
  obtain ⟨sal, sbb⟩ := A.sb_facts hpre
  have fsb : Fits A.sb 1024 := by unfold Fits; omega
  have fsbB : Fits A.sb A.B.toNat := by unfold Fits at fsb ⊢; omega
  have fout := hpre.2.2.2.2.2.1
  have oal := hpre.2.2.2.2.2.2.1
  have hB1 : 1 ≤ A.B.toNat := by rw [hpre.1]; exact Nat.one_le_two_pow
  have hlast : A.stride A.j = 1 := by rw [A.stride_eq hpre.1 (Nat.le_refl _)]; simp
  have hne : A.j ≠ A.j + 1 := by omega
  have hmin : min A.j A.j = A.j := Nat.min_self _
  have hmin' : min (A.j + 1) A.j = A.j := by omega
  obtain ⟨pc, r, p⟩ := s
  rw [A.foot_last t]
  refine (wpR_sound (cut := fun _ => false) ?_).weaken fun s h d hq => hq.1
  have hB2 : A.j = 0 → A.B.toNat = 1 := fun h => by rw [hpre.1, h]
  rcases A.T_last hs with ⟨rfl, hj0, hr1, hr2, hr3, hr6, hrd2⟩ | ⟨rfl, hj1, hr22, hr2, hr3, hr6, hrd2⟩
  all_goals simp only [ptx_eval, K, Ptx.Kernels.ReduceAtomicNvcc.reduce_atomic, launch, params, mem, Phased.J,
    phased, List.map_cons, List.map_nil, hr2, hr3, hr6, hrd2, hne, hmin, hmin', ↓reduceIte,
    A.foot_last t]
  all_goals try simp only [hr1]
  all_goals try simp only [hr22, hlast]
  all_goals simp only [show A.sh "_ZZ13reduce_atomicE1s" = A.sb from rfl]
  all_goals ptx_branches4
  all_goals ptx_addrs4 [A.sb, A.out] [0, t.ctaid.x.toNat]
  all_goals (try and_intros)
  all_goals first
    | trivial
    | (intro _ h; exact h.elim)
    | (funext a; split
       · next h => first | exact absurd h.1 (by omega) | exact absurd h.2.1 (by omega)
       · rfl)
    | (exfalso; omega)
    | exact accessOk_elem_mem (N := 1024) (by simp) fsb sal (by omega)
    | exact accessOk_elem_mem (N := 1) (by simp) fout oal (by omega)
    | exact elem_zero _
    | (refine ⟨_, addsTo_add _, fun v => ⟨?_, fun _ h => h.elim, trivial⟩⟩
       funext a
       simp only [Ghost.add, lo32_rd_b4, elem_zero A.out]
       rw [rd32_cells fsbB (by omega)]
       by_cases ha : a = A.out
       · subst ha; simp [show t.tid.x.toNat = 0 by omega]
       · simp [ha])
    | exact fun y hy => ⟨trivial, by omega, hy⟩
    | exact fun y hy => .inl ⟨trivial, by omega, hy⟩
    | exact fun y hy => .inl ⟨rfl, by omega, hy⟩
    | (rintro ⟨sp, y⟩ ⟨-, h0, -⟩; exfalso; omega)
    | (rintro ⟨sp, y⟩ ⟨hsp, h0, hy⟩
       try simp only at hsp
       subst hsp
       refine wr_lo32 ?_ hy
       simp only [lo32_ext32, lo32_rd_b4]
       rw [rd32_cells fsbB (by omega)])
  done

/-! ### The side conditions of the phase theorem -/

theorem tid_ne (hpre : A.Pre) {t u : Tid} (ht : t ∈ A.launch.threads) (hu : u ∈ A.launch.threads)
    (hc : t.ctaid = u.ctaid) (htu : t ≠ u) : t.tid.x.toNat ≠ u.tid.x.toNat := by
  intro h
  obtain ⟨-, -, -, -, -, -, -, ht5, ht6⟩ := A.thread_facts hpre ht
  obtain ⟨-, -, -, -, -, -, -, hu5, hu6⟩ := A.thread_facts hpre hu
  apply htu
  rcases t with ⟨tc, ⟨tx, ty, tz⟩⟩; rcases u with ⟨uc, ⟨ux, uy, uz⟩⟩
  simp only at hc h ht5 ht6 hu5 hu6
  subst hc ht5 ht6 hu5 hu6
  rw [BitVec.eq_of_toNat_eq h]

theorem cta_ne (hpre : A.Pre) {t u : Tid} (ht : t ∈ A.launch.threads) (hu : u ∈ A.launch.threads)
    (hc : t.ctaid ≠ u.ctaid) : t.ctaid.x.toNat ≠ u.ctaid.x.toNat := by
  intro h
  obtain ⟨-, -, -, -, -, ht3, ht4, -, -⟩ := A.thread_facts hpre ht
  obtain ⟨-, -, -, -, -, hu3, hu4, -, -⟩ := A.thread_facts hpre hu
  apply hc
  rcases t with ⟨⟨tx, ty, tz⟩, _⟩; rcases u with ⟨⟨ux, uy, uz⟩, _⟩
  simp only at h ht3 ht4 hu3 hu4
  subst ht3 ht4 hu3 hu4
  rw [BitVec.eq_of_toNat_eq h]

/-- The thread with index `i` in CTA `b`. -/
def th (b : Dim3) (i : Nat) : Tid := ⟨b, ⟨BitVec.ofNat 32 i, 0, 0⟩⟩

theorem th_mem (hpre : A.Pre) {b : Dim3} (hb : ∃ t ∈ A.launch.threads, t.ctaid = b) {i : Nat}
    (hi : i < A.B.toNat) : th b i ∈ A.launch.threads ∧ (th b i).tid.x.toNat = i := by
  obtain ⟨t, ht, rfl⟩ := hb
  have hB := A.B_le hpre
  have hti : (BitVec.ofNat 32 i).toNat = i := by simp; omega
  refine ⟨?_, hti⟩
  have := ht
  rw [mem_threads] at this ⊢
  obtain ⟨h1, h2, h3, _, _, _⟩ := this
  refine ⟨h1, h2, h3, ?_, ?_, ?_⟩
  · show (BitVec.ofNat 32 i).toNat < A.B.toNat; rw [hti]; exact hi
  · show (0 : BitVec 32).toNat < (1 : BitVec 32).toNat; decide
  · show (0 : BitVec 32).toNat < (1 : BitVec 32).toNat; decide

theorem ok (hpre : A.Pre) (m₀ : Mem) (sh₀ : Dim3 → Mem) (r₀ : Tid → String → Val)
    (p₀ : Tid → String → Bool) : (A.phased m₀ sh₀).Ok K A.launch r₀ p₀ m₀ sh₀ := by
  obtain ⟨sal, sbb⟩ := A.sb_facts hpre
  have fsb : Fits A.sb 1024 := by unfold Fits; omega
  have hBle := A.B_le hpre
  have fsbB : Fits A.sb A.B.toNat := by unfold Fits at fsb ⊢; omega
  have fx := hpre.2.2.2.1
  have fout := hpre.2.2.2.2.2.1
  have hsep := hpre.2.2.2.2.2.2.2.1
  have hB1 : 1 ≤ A.B.toNat := by rw [hpre.1]; exact Nat.one_le_two_pow
  refine ⟨fun _ _ => by simp [phased], fun _ _ => rfl, fun _ _ _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht k hk s hs
    simp only [phased] at hk ⊢
    rcases Nat.lt_or_ge k 1 with h0 | h1
    · obtain rfl : k = 0 := by omega
      exact A.phase0 hpre m₀ sh₀ ht s hs
    · rcases Nat.lt_or_ge A.j k with hj | hj
      · obtain rfl : k = A.j + 1 := by omega
        exact A.phase_last hpre m₀ sh₀ ht s hs
      · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
        exact A.phase_tree hpre m₀ sh₀ ht hj s hs
  · intro b k x hb hk hno
    simp only [phased] at hk hno ⊢
    have hb' := hb
    obtain ⟨t₀, ht₀, rfl⟩ := hb'
    obtain ⟨sp, y⟩ := x
    have cellOf : ∀ (h : (y - A.sb).toNat < 4 * A.B.toNat),
        th t₀.ctaid ((y - A.sb).toNat / 4) ∈ A.launch.threads ∧
          (th t₀.ctaid ((y - A.sb).toNat / 4)).tid.x.toNat = (y - A.sb).toNat / 4 ∧
          covers (elem A.sb ((y - A.sb).toNat / 4)) 4 y :=
      fun h => ⟨(A.th_mem hpre hb (i := (y - A.sb).toNat / 4) (by omega)).1,
        (A.th_mem hpre hb (i := (y - A.sb).toNat / 4) (by omega)).2, covers_of_lt fsbB h⟩
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
          rw [A.foot_zero] at hnw
          exact absurd ⟨rfl, by rw [hti]; exact hcv⟩ hnw
        · rfl
      · rcases Nat.lt_or_ge A.j k with hj | hj
        · obtain rfl : k = A.j + 1 := by omega
          show cells _ _ (A.V m₀ _ (min (A.j + 1) A.j)) _ y = cells _ _ (A.V m₀ _ (min A.j A.j)) _ y
          rw [show min (A.j + 1) A.j = A.j by omega, Nat.min_self]
        · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
          show cells _ _ (A.V m₀ _ (min (m + 1) A.j)) _ y = cells _ _ (A.V m₀ _ (min m A.j)) _ y
          rw [show min (m + 1) A.j = m + 1 by omega, show min m A.j = m by omega]
          apply cells_congr
          · intro h
            obtain ⟨hm, hti, hcv⟩ := cellOf h
            have hnw := hno _ hm rfl
            rw [A.foot_tree _ (by omega) hj] at hnw
            show (if _ < A.stride (m + 1) then _ else _) = _
            split
            · next hl => exact absurd ⟨rfl, by rw [hti]; exact hl, by rw [hti]; exact hcv⟩ hnw
            · rfl
          · intro _; rfl
  · intro t ht u hu htu hc k _ x hw htc
    simp only [phased] at hw htc
    have hne := A.tid_ne hpre ht hu hc htu
    obtain ⟨-, hti, -⟩ := A.thread_facts hpre ht
    obtain ⟨-, hui, -⟩ := A.thread_facts hpre hu
    obtain ⟨sp, y⟩ := x
    rcases Nat.lt_or_ge k 1 with h0 | h1
    · obtain rfl : k = 0 := by omega
      rw [A.foot_zero] at hw htc
      obtain ⟨hsp, hcv⟩ := hw
      rcases htc with ⟨hsp', -⟩ | ⟨-, hcv'⟩
      · simp only at hsp hsp'; rw [hsp] at hsp'; cases hsp'
      · exact elem_disjoint fsbB hti hui hne hcv hcv'
    · rcases Nat.lt_or_ge A.j k with hj | hj
      · rw [A.foot_after _ hj] at hw; exact hw
      · rw [A.foot_tree _ h1 hj] at hw htc
        obtain ⟨-, hlt, hcv⟩ := hw
        have hsf := A.stride_facts hpre (m := k - 1) (by omega)
        rw [show k - 1 + 1 = k by omega] at hsf
        rcases htc with ⟨-, hlt', hcv'⟩ | ⟨-, hlt', hcv'⟩
        · exact elem_disjoint fsbB hti (by omega) (by omega) hcv hcv'
        · exact elem_disjoint fsbB hti hui hne hcv hcv'
  · -- no thread writes global memory except through the cell
    intro t _ u _ _ k _ j' _ a hw _
    simp only [phased] at hw
    rcases Nat.lt_or_ge k 1 with h0 | h1
    · obtain rfl : k = 0 := by omega
      rw [A.foot_zero] at hw; exact absurd hw.1 nofun
    · rcases Nat.lt_or_ge A.j k with hj | hj
      · rw [A.foot_after _ hj] at hw; exact hw
      · rw [A.foot_tree _ h1 hj] at hw; exact absurd hw.1 nofun
  · -- the cell `*out` is in nobody's footprint
    intro t ht k a ha y hy htc
    simp only [phased] at ha htc
    subst ha
    have hc0 : covers (elem A.out 0) 4 y := by rw [elem_zero]; exact hy
    rcases Nat.lt_or_ge k 1 with h0 | h1
    · obtain rfl : k = 0 := by omega
      rw [A.foot_zero] at htc
      rcases htc with ⟨-, hlt, hcv⟩ | ⟨h, -⟩
      · exact elem_disjoint₂ fout fx (by omega) (by omega : 0 < 1) hlt hc0 hcv
      · exact absurd h nofun
    · rcases Nat.lt_or_ge A.j k with hj | hj
      · rw [A.foot_after _ hj] at htc
        rcases htc with ⟨h, -⟩ | h
        · exact absurd h nofun
        · exact h
      · rw [A.foot_tree _ h1 hj] at htc
        rcases htc with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h nofun
  · intro a b ha hb hab
    simp only [phased] at ha hb
    exact absurd (ha.trans hb.symm) hab

end Args

/-- The atomic reduction is correct for every launch in `Pre`: blocks of
`B = 2^j ≤ 1024` threads, any number of blocks with `G·B ≤ 2^32`, any length
`n`, an input array and an output word that fit, are aligned and do not
overlap, and any placement of the shared array. Under every initial memory,
shared memory and register content, and every execution: no fault and no
diverged barrier, progress, bounded executions, phase-relative race freedom
(the blocks' atomic additions to `*out` are the only conflicting accesses,
and they are atomics on one location), a finished execution exists, and when
all threads are done `*out` holds its initial value plus
`x[0] + … + x[min(n, G·B) - 1]` (mod 2^32), whatever order the blocks added
in, and no other byte has changed. -/
theorem reduce_atomic_correct (A : Args) (hpre : A.Pre) (m₀ : Mem) (sh₀ : Dim3 → Mem)
    (r₀ : Tid → String → Val) (p₀ : Tid → String → Bool) :
    let L := A.launch
    let c₀ := Cfg.init r₀ p₀ m₀ sh₀
    (∀ c, Reach K L c₀ c → ¬ Faults K L c) ∧
    (∀ c, Reach K L c₀ c → Done K L c ∨ ∃ c', Step K L c c') ∧
    (∃ bound, ∀ j c, Steps K L j c₀ c → j ≤ bound) ∧
    RaceFree K L c₀ ∧
    (∃ c, Reach K L c₀ c ∧ Done K L c) ∧
    (∀ c, Reach K L c₀ c → Done K L c →
      rd32 c.mem A.out = rd32 m₀ A.out +
        accUpTo (fun i => if i < A.n.toNat then rd32 m₀ (elem A.x i) else 0) (A.G.toNat * A.B.toNat) ∧
      (∀ y, ¬ covers A.out 4 y → c.mem y = m₀ y)) := by
  intro L c₀
  have R := Phased.phase_sound (A.ok hpre m₀ sh₀ r₀ p₀)
  have hB1 : 1 ≤ A.B.toNat := by rw [hpre.1]; exact Nat.one_le_two_pow
  refine ⟨R.noFault, R.progress, R.bounded, R.raceFree,
    Phased.exists_done_of R.progress R.bounded, fun c hc hd => ?_⟩
  obtain ⟨-, hun, hcell⟩ := R.final c hc hd
  refine ⟨?_, fun y hy => hun y ?_ ?_⟩
  · rw [hcell A.out rfl]
    congr 1
    simp only [Args.phased]
    -- only phase `j + 1` of thread 0 of each block contributes
    rw [tsum_congr (g := fun t => if t.tid.x.toNat = 0 then A.V m₀ t.ctaid.x.toNat A.j 0 else 0)
      fun t _ => ?_]
    · rw [tsum_oneD_first (v := fun c => A.V m₀ c A.j 0) A.launch_oneD (by omega),
        ← accUpTo_blocks _ A.B.toNat]
      refine accUpTo_congr' fun b _ => ?_
      rw [A.V_final hpre.1]
      rfl
    · by_cases h0 : t.tid.x.toNat = 0
      · simp only [h0, true_and, and_true, ↓reduceIte]
        exact accUpTo_single _ _ _ (by omega)
      · simp only [h0, false_and, and_false, ↓reduceIte]
        exact accUpTo_zero _
  · intro t ht k hk hwk
    simp only [Args.phased] at hk hwk
    rcases Nat.lt_or_ge k 1 with h0 | h1
    · obtain rfl : k = 0 := by omega
      rw [A.foot_zero] at hwk; exact absurd hwk.1 nofun
    · rcases Nat.lt_or_ge A.j k with hj | hj
      · rw [A.foot_after _ hj] at hwk; exact hwk
      · rw [A.foot_tree _ h1 hj] at hwk; exact absurd hwk.1 nofun
  · intro b hb; simp only [Args.phased] at hb; subst hb; exact hy

/-- The precondition is satisfiable: 3 blocks of 8 threads over 20 elements,
the shared array at offset 0. -/
example : (Args.mk 3 8 3 20 0x1000 0x2000 (fun _ => 0)).Pre := by
  refine ⟨by decide, by decide, by decide, by simp [Fits], by decide, by simp [Fits], by decide,
    by decide, ?_, ?_⟩
  · intro v hv
    simp [K, Ptx.Kernels.ReduceAtomicNvcc.reduce_atomic] at hv; subst hv; decide
  · simp [K, Ptx.Kernels.ReduceAtomicNvcc.reduce_atomic]

end Ptx.Examples.ReduceAtomic
