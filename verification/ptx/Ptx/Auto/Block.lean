/-
M4 check classes: what the block classes (`reduce32`, `scan32`) share.

A block-class kernel is launched one-dimensionally (`G` blocks of `B`
threads), reads `n` 32-bit words from an input array, uses one `.shared`
array of 32-bit words, and writes an output pointer. The spec names the
three parameters and the shared array, and bounds the block size by
`2 ^ maxJ`. Everything here is about the launch, not the kernel's code:
which thread is which, and where the shared array may be.
-/
import Ptx.Logic.PhaseSound
import Ptx.Logic.PhaseWp
import Ptx.Logic.Cells
import Ptx.Logic.Sums
import Ptx.Logic.Launch1D
import Ptx.Tactics.EvalR
import Ptx.Auto.Tactic4

set_option linter.unusedSimpArgs false

namespace Ptx.Auto.Block
open Ptx

/-- What a block-class spec names: the input array, the output pointer and
the length (kernel parameters), the shared array, and the largest block,
`2 ^ maxJ` threads. -/
structure Spec where
  input : String
  output : String
  length : String
  shared : String
  maxJ : Nat

/-- The shared array is declared with an alignment that is a multiple of 4
and room for `W ≥ 2 ^ maxJ` words. Only proofs use this; no theorem
statement does. -/
def Fit (S : Spec) (K : Kernel) (W : Nat) : Prop :=
  ∃ al, ⟨S.shared, al, 4 * W⟩ ∈ K.shared ∧ 0 < al ∧ al % 4 = 0 ∧ 2 ^ S.maxJ ≤ W

/-- The launch-time values a class theorem quantifies over. `j` is the
class's logarithm of the block size (`B = 2^j` for `reduce32`, the number
of rounds for `scan32`). -/
structure Args (S : Spec) where
  G : BitVec 32
  B : BitVec 32
  j : Nat
  n : BitVec 32
  x : Addr
  out : Addr
  sh : String → Addr

namespace Args
variable {S : Spec} (A : Args S)

/-- Where the shared array is. -/
def sb : Addr := A.sh S.shared

def params : String → Val := fun p =>
  if p = S.input then A.x else if p = S.output then A.out
  else if p = S.length then ext32 A.n else 0

/-- The launch, with an output region of `outLen` words. -/
def launch (outLen : Nat) : Launch :=
  { grid := ⟨A.G, 1, 1⟩, block := ⟨A.B, 1, 1⟩, params := A.params,
    alloc := [⟨A.x, 4 * A.n.toNat⟩, ⟨A.out, 4 * outLen⟩], shared := A.sh }

/-- Element `i` of CTA `b`'s segment, `0` past the end of the input. -/
def seg (m₀ : Mem) (b i : Nat) : BitVec 32 :=
  if b * A.B.toNat + i < A.n.toNat then rd32 m₀ (elem A.x (b * A.B.toNat + i)) else 0

theorem launch_oneD (len : Nat) : (A.launch len).OneD A.G A.B := ⟨rfl, rfl⟩

/-- The index facts of one thread. -/
theorem thread_facts {len : Nat} (hGB : A.G.toNat * A.B.toNat ≤ 2 ^ 32) {t : Tid}
    (ht : t ∈ (A.launch len).threads) :
    t.ctaid.x.toNat < A.G.toNat ∧ t.tid.x.toNat < A.B.toNat ∧
      t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat < A.G.toNat * A.B.toNat ∧
      A.G.toNat * A.B.toNat ≤ 2 ^ 32 ∧
      t.ctaid.y = 0 ∧ t.ctaid.z = 0 ∧ t.tid.y = 0 ∧ t.tid.z = 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (A.launch_oneD len).thread ht
  exact ⟨h1, h2, gid_lt_of h1 h2, hGB, h3, h4, h5, h6⟩

theorem gid_toNat {t : Tid} (hcB : t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat < A.G.toNat * A.B.toNat)
    (hGB : A.G.toNat * A.B.toNat ≤ 2 ^ 32) :
    (t.ctaid.x * A.B + t.tid.x).toNat = t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_mul, Nat.mod_eq_of_lt (a := t.ctaid.x.toNat * A.B.toNat) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem tid_ne {len : Nat} {t u : Tid} (ht : t ∈ (A.launch len).threads) (hu : u ∈ (A.launch len).threads)
    (hc : t.ctaid = u.ctaid) (htu : t ≠ u) : t.tid.x.toNat ≠ u.tid.x.toNat := by
  intro h
  obtain ⟨-, -, -, -, ht5, ht6⟩ := (A.launch_oneD len).thread ht
  obtain ⟨-, -, -, -, hu5, hu6⟩ := (A.launch_oneD len).thread hu
  apply htu
  rcases t with ⟨tc, ⟨tx, ty, tz⟩⟩; rcases u with ⟨uc, ⟨ux, uy, uz⟩⟩
  simp only at hc h ht5 ht6 hu5 hu6
  subst hc ht5 ht6 hu5 hu6
  rw [BitVec.eq_of_toNat_eq h]

theorem cta_ne {len : Nat} {t u : Tid} (ht : t ∈ (A.launch len).threads) (hu : u ∈ (A.launch len).threads)
    (hc : t.ctaid ≠ u.ctaid) : t.ctaid.x.toNat ≠ u.ctaid.x.toNat := by
  intro h
  obtain ⟨-, -, ht3, ht4, -, -⟩ := (A.launch_oneD len).thread ht
  obtain ⟨-, -, hu3, hu4, -, -⟩ := (A.launch_oneD len).thread hu
  apply hc
  rcases t with ⟨⟨tx, ty, tz⟩, _⟩; rcases u with ⟨⟨ux, uy, uz⟩, _⟩
  simp only at h ht3 ht4 hu3 hu4
  subst ht3 ht4 hu3 hu4
  rw [BitVec.eq_of_toNat_eq h]

/-- Two global indices of different CTAs differ. -/
theorem gid_ne {len : Nat} {t u : Tid} (ht : t ∈ (A.launch len).threads) (hu : u ∈ (A.launch len).threads)
    (hc : t.ctaid ≠ u.ctaid) :
    t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat ≠ u.ctaid.x.toNat * A.B.toNat + u.tid.x.toNat := by
  have hcne := A.cta_ne ht hu hc
  obtain ⟨-, hti, -⟩ := (A.launch_oneD len).thread ht
  obtain ⟨-, hui, -⟩ := (A.launch_oneD len).thread hu
  intro h
  apply hcne
  have e1 := Nat.mul_add_div (show 0 < A.B.toNat by omega) t.ctaid.x.toNat t.tid.x.toNat
  have e2 := Nat.mul_add_div (show 0 < A.B.toNat by omega) u.ctaid.x.toNat u.tid.x.toNat
  rw [Nat.div_eq_of_lt hti, Nat.add_zero] at e1
  rw [Nat.div_eq_of_lt hui, Nat.add_zero] at e2
  rw [Nat.mul_comm] at e1 e2
  rw [← e1, ← e2, h]

end Args

/-- The thread with index `i` in CTA `b`. -/
def th (b : Dim3) (i : Nat) : Tid := ⟨b, ⟨BitVec.ofNat 32 i, 0, 0⟩⟩

namespace Args
variable {S : Spec} (A : Args S)

theorem th_mem {len : Nat} {b : Dim3} (hb : ∃ t ∈ (A.launch len).threads, t.ctaid = b) {i : Nat}
    (hi : i < A.B.toNat) : th b i ∈ (A.launch len).threads ∧ (th b i).tid.x.toNat = i := by
  obtain ⟨t, ht, rfl⟩ := hb
  have hB := A.B.isLt
  have hti : (BitVec.ofNat 32 i).toNat = i := by simp; omega
  refine ⟨?_, hti⟩
  have := ht
  rw [mem_threads] at this ⊢
  obtain ⟨h1, h2, h3, _, _, _⟩ := this
  refine ⟨h1, h2, h3, ?_, ?_, ?_⟩
  · show (BitVec.ofNat 32 i).toNat < A.B.toNat; rw [hti]; exact hi
  · show (0 : BitVec 32).toNat < (1 : BitVec 32).toNat; decide
  · show (0 : BitVec 32).toNat < (1 : BitVec 32).toNat; decide

/-- The thread of CTA `q` with index `r` is in a launch of `G > q` blocks of
`B > r` threads. -/
theorem th_of {len q r : Nat} (hq : q < A.G.toNat) (hr : r < A.B.toNat) :
    (⟨⟨BitVec.ofNat 32 q, 0, 0⟩, ⟨BitVec.ofNat 32 r, 0, 0⟩⟩ : Tid) ∈ (A.launch len).threads ∧
      (BitVec.ofNat 32 q).toNat = q ∧ (BitVec.ofNat 32 r).toNat = r := by
  have hq' : (BitVec.ofNat 32 q).toNat = q := by have := A.G.isLt; simp; omega
  have hr' : (BitVec.ofNat 32 r).toNat = r := by have := A.B.isLt; simp; omega
  refine ⟨?_, hq', hr'⟩
  rw [mem_threads]
  simp only [Launch.Thread, launch]
  refine ⟨by rw [hq']; exact hq, by decide, by decide, by rw [hr']; exact hr, by decide, by decide⟩

/-- Where the shared array is, from the layout ptxas may choose. -/
theorem sb_facts {K : Kernel} {W : Nat} (hfit : Fit S K W) (hl : LayoutOk K A.sh) :
    A.sb.toNat % 4 = 0 ∧ A.sb.toNat + 4 * W ≤ 2 ^ 32 ∧ 2 ^ S.maxJ ≤ W := by
  obtain ⟨al, hm, hal, h4, hW⟩ := hfit
  obtain ⟨h1, h2⟩ := hl.1 _ hm
  refine ⟨?_, h2, hW⟩
  have : A.sb.toNat % al = 0 := h1
  obtain ⟨c, rfl⟩ := Nat.dvd_of_mod_eq_zero h4
  have h := Nat.mod_mod_of_dvd A.sb.toNat (⟨c, rfl⟩ : 4 ∣ 4 * c)
  rw [this] at h
  exact h.symm

/-- The shared array as one of the shared allocations of the launch. -/
theorem sb_alloc {K : Kernel} {W len : Nat} {al : Nat} (hm : ⟨S.shared, al, 4 * W⟩ ∈ K.shared) :
    ⟨A.sb, 4 * W⟩ ∈ (A.launch len).allocs K .shared := by
  simp only [Launch.allocs_shared, Launch.sregions, List.mem_map]
  exact ⟨_, hm, rfl⟩

end Args

end Ptx.Auto.Block
