/-
@HEADER@
-/
import Ptx.Auto.Reduce32

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace E5rCheck
open Ptx Ptx.Auto Ptx.Auto.Block Ptx.Auto.Reduce32

@KERNEL_DEF@
@SPEC_DEF@
/-- The registers each phase starts with, from the spec's roles at each
barrier. Not trusted: a wrong claim only makes the obligations unprovable. -/
def phaseT (A : Block.Args spec) (m₀ : Mem) (t : Tid) : Nat → TState → Prop
  | 0, _ => False
  | 1, s => s.pc = @PC1@ ∧ @T1@
  | k + 2, s => s.pc = @PCL@ ∧ @TL@

def code : Code spec where
  T := phaseT
  bpc := fun _ k => if k = 0 then @BPC0@ else @BPCL@
  N := @N@

theorem fit : Fit spec @K@ @W@ :=
  ⟨@ALIGN@, by simp [@K@], by decide, by decide, by decide⟩

theorem lo32_ofInt_zero : lo32 (BitVec.ofInt 64 0) = 0 := by decide

theorem T_last {A : Block.Args spec} {m₀ : Mem} {t : Tid} {pc : Nat} {r : String → Val} {p : String → Bool}
    (hs : code.Tc A m₀ t (A.j + 1) ⟨pc, r, p⟩) :
    (pc = @PC1@ ∧ A.j = 0 ∧ @LAST1@) ∨ (pc = @PCL@ ∧ 1 ≤ A.j ∧ @LASTL@) := by
  rcases hj : A.j with _ | j' <;> rw [hj] at hs <;> simp only [Code.Tc, code, phaseT] at hs
  · exact .inl ⟨hs.1, rfl, hs.2⟩
  · exact .inr ⟨hs.1, by omega, hs.2⟩

theorem obligations : @NS@Obligations @K@ code := by
  refine ⟨?_, ?_, ?_⟩
  · -- phase 0: load, then the first barrier
    intro A hpre m₀ sh₀ t ht s hs
    obtain ⟨pc, r, p⟩ := s
    simp only [Code.Tc] at hs; subst hs
    obtain ⟨hc, hi, hcB, hGB, -, -, -, -⟩ := A.thread_facts hpre.2.2.1 ht
    obtain ⟨sal, fsbB, hBW, hB1⟩ := fits_sb fit A hpre
    obtain ⟨-, sbb, -⟩ := A.sb_facts fit hpre.2.2.2.2.2.2.2.2
    have fsb : Fits A.sb @W@ := by unfold Fits; omega
    have fx := hpre.2.2.2.1
    have xal := hpre.2.2.2.2.1
    have hcB' : t.ctaid.x.toNat * A.B.toNat < 2 ^ 32 := by omega
    refine (wpR_sound (cut := fun _ => false) ?_).weaken fun s h d hq => hq.1
    simp only [@EVAL@]
    try simp only [show A.sh @SHNAME@ = A.sb from rfl]
    ptx_branches4
    all_goals ptx_addrs4 [A.sb, A.x] [t.tid.x.toNat, t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat]
    all_goals (try and_intros)
    all_goals first
      | trivial@EXTRA_ALTS@
      | (exfalso; omega)
      | exact accessOk_elem_mem (N := @W@) (by simp) fsb sal (by omega)
      | exact accessOk_elem_mem (N := A.n.toNat) (by simp) fx xal (by omega)
      | exact fun y hy => ⟨rfl, hy⟩
      | exact fun y hy => ⟨trivial, hy⟩
      | exact fun y hy => .inl ⟨rfl, by omega, hy⟩
      | exact fun y hy => .inl ⟨trivial, by omega, hy⟩
      | (rintro ⟨sp, y⟩ ⟨hsp, hy⟩
         try simp only at hsp
         subst hsp
         refine wr_cells fsbB hi hy ?_
         simp only [Reduce32.V, Block.Args.seg, Nat.zero_min, lo32_ext32, lo32_rd_b4, lo32_ofInt_zero]
         split <;> first | rfl | (exfalso; omega))
      | (simp (config := { failIfUnchanged := false }) only [code, phaseT, upd, String.reduceEq,
           ↓reduceIte, true_and, and_true]
         all_goals (try and_intros)
         all_goals ptx_reg4)
    done
  · -- phases 1 .. j: one tree step each, then the loop's barrier
    intro A hpre m₀ sh₀ t ht m hm s hs
    obtain ⟨hc, hi, hcB, hGB, -, -, -, -⟩ := A.thread_facts hpre.2.2.1 ht
    obtain ⟨sal, fsbB, hBW, hB1⟩ := fits_sb fit A hpre
    obtain ⟨-, sbb, -⟩ := A.sb_facts fit hpre.2.2.2.2.2.2.2.2
    have fsb : Fits A.sb @W@ := by unfold Fits; omega
    obtain ⟨hh1, hh2, hh3, hh4⟩ := stride_facts A hpre.1 hm
    have hmin : min m A.j = m := Nat.min_eq_left (by omega)
    have hne : m ≠ A.j + 1 := by omega
    have hmin1 : min (m + 1) A.j = m + 1 := Nat.min_eq_left hm
    obtain ⟨pc, r, p⟩ := s
    rcases m with _ | m'
    · simp only [Nat.zero_add] at hh1 hh2 hh3 hmin1 hm ⊢
      simp only [Code.Tc, code, phaseT] at hs
      obtain ⟨rfl, @PAT1@⟩ := hs
      refine (wpR_sound (cut := fun _ => false) ?_).weaken fun s h d hq => hq.1
      have hh4' : A.B.toNat / 2 = stride A 1 := by simpa using hh4
      simp only [@EVAL@@HYP1@, @NS@foot_tree A t (k := 1) (by omega) hm]
      try simp only [show A.sh @SHNAME@ = A.sb from rfl]
      ptx_branches4
      all_goals ptx_addrs4 [A.sb] [t.tid.x.toNat, t.tid.x.toNat + stride A 1]
@TREE_ALTS@
    · simp only [Code.Tc, code, phaseT] at hs
      obtain ⟨rfl, @PATL@⟩ := hs
      have hst : stride A (m' + 1) ≤ @W@ := by omega
      refine (wpR_sound (cut := fun _ => false) ?_).weaken fun s h d hq => hq.1
      simp only [@EVAL@@HYPL@, @NS@foot_tree A t (k := m' + 1 + 1) (by omega) hm]
      try simp only [show A.sh @SHNAME@ = A.sb from rfl]
      ptx_branches4
      all_goals ptx_addrs4 [A.sb] [t.tid.x.toNat, t.tid.x.toNat + stride A (m' + 1 + 1)]
@TREE_ALTS@
  · -- phase j + 1: thread 0 stores the block's sum
    intro A hpre m₀ sh₀ t ht s hs
    obtain ⟨hc, hi, hcB, hGB, -, -, -, -⟩ := A.thread_facts hpre.2.2.1 ht
    obtain ⟨sal, fsbB, hBW, hB1⟩ := fits_sb fit A hpre
    obtain ⟨-, sbb, -⟩ := A.sb_facts fit hpre.2.2.2.2.2.2.2.2
    have fsb : Fits A.sb @W@ := by unfold Fits; omega
    have fout := hpre.2.2.2.2.2.1
    have oal := hpre.2.2.2.2.2.2.1
    have hlast := stride_last A hpre.1
    have hne : A.j ≠ A.j + 1 := by omega
    have hmin : min A.j A.j = A.j := Nat.min_self _
    have hmin' : min (A.j + 1) A.j = A.j := by omega
    have hB2 : A.j = 0 → A.B.toNat = 1 := fun h => by rw [hpre.1, h]
    obtain ⟨pc, r, p⟩ := s
    rw [@NS@foot_last A t]
    refine (wpR_sound (cut := fun _ => false) ?_).weaken fun s h d hq => hq.1
    rcases T_last hs with ⟨rfl, hj0, @PAT1@⟩ | ⟨rfl, hj1, @PATL@⟩
    · simp only [@EVAL@@HYP1@, hne, hmin, hmin', ↓reduceIte, @NS@foot_last A t]
      try simp only [show A.sh @SHNAME@ = A.sb from rfl]
      ptx_branches4
      all_goals ptx_addrs4 [A.sb, A.out] [0, t.ctaid.x.toNat]
@LAST_ALTS@
    · simp only [@EVAL@@HYPL@, hlast, hne, hmin, hmin', ↓reduceIte, @NS@foot_last A t]
      try simp only [show A.sh @SHNAME@ = A.sb from rfl]
      ptx_branches4
      all_goals ptx_addrs4 [A.sb, A.out] [0, t.ctaid.x.toNat]
@LAST_ALTS@

theorem correct : @NS@Correct spec @K@ := @NS@correct_of fit code obligations

end E5rCheck

#print axioms E5rCheck.correct
