/-
@HEADER@
-/
import Ptx.Auto.Scan32

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace E5rCheck
open Ptx Ptx.Auto Ptx.Auto.Block Ptx.Auto.Scan32
open Ptx.Auto.Reduce32 (Code Code.Tc)

@KERNEL_DEF@
@SPEC_DEF@
/-- The registers each phase starts with, from the spec's roles at each
barrier: after the load (phase 1), after a round's read (even phases) and
after a round's add (odd phases from 3). Not trusted: a wrong claim only
makes the obligations unprovable. -/
def phaseT (A : Block.Args spec) (m₀ : Mem) (t : Tid) (p : Nat) (s : TState) : Prop :=
  if p = 1 then s.pc = @PC1@ ∧ @T1@
  else if p % 2 = 0 then s.pc = @PCR@ ∧ @TR@
  else s.pc = @PCA@ ∧ @TA@

def code : Code spec where
  T := phaseT
  bpc := fun _ p => if p = 0 then @BPC0@ else if p % 2 = 1 then @BPCR@ else @BPCA@
  N := @N@

theorem fit : Fit spec @K@ @W@ :=
  ⟨@ALIGN@, by simp [@K@], by decide, by decide, by decide⟩

theorem lo32_ofInt_zero : lo32 (BitVec.ofInt 64 0) = 0 := by decide

theorem T_odd {A : Block.Args spec} {m₀ : Mem} {t : Tid} {i pc : Nat} {r : String → Val} {p : String → Bool}
    (hs : code.Tc A m₀ t (2 * i + 1) ⟨pc, r, p⟩) :
    (i = 0 ∧ pc = @PC1@ ∧ @LAST1@) ∨ (1 ≤ i ∧ pc = @PCA@ ∧ @LASTA@) := by
  simp only [Code.Tc, code, phaseT, show ¬ ((2 * i + 1) % 2 = 0) by omega,
    show (2 * i + 1) / 2 - 1 = i - 1 by omega] at hs
  by_cases h : i = 0
  · subst h; exact .inl ⟨rfl, by simpa using hs⟩
  · simp only [show 2 * i + 1 ≠ 1 by omega, ↓reduceIte] at hs
    exact .inr ⟨by omega, hs⟩

theorem T_even {A : Block.Args spec} {m₀ : Mem} {t : Tid} {i pc : Nat} {r : String → Val} {p : String → Bool}
    (hs : code.Tc A m₀ t (2 * i + 2) ⟨pc, r, p⟩) : pc = @PCR@ ∧ @LASTR@ := by
  simp only [Code.Tc, code, phaseT, show 2 * i + 2 ≠ 1 by omega, show (2 * i + 2) % 2 = 0 by omega,
    ↓reduceIte, show (2 * i + 2) / 2 - 1 = i by omega] at hs
  exact hs

theorem obligations : Obligations @K@ code := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- phase 0: load, then the first barrier
    intro A hpre m₀ sh₀ t ht s hs
    obtain ⟨pc, r, p⟩ := s
    simp only [Code.Tc] at hs; subst hs
    obtain ⟨hc, hi, hcB, hGB, -, -, -, -⟩ := A.thread_facts hpre.2.2.2.2.1 ht
    obtain ⟨sal, fsbB, hBW⟩ := fits_sb fit A hpre
    obtain ⟨-, sbb, -⟩ := A.sb_facts fit hpre.2.2.2.2.2.2.2.2.2.2.2
    have fsb : Fits A.sb @W@ := by unfold Fits; omega
    have fx := hpre.2.2.2.2.2.2.1
    have xal := hpre.2.2.2.2.2.2.2.1
    have hcB' : t.ctaid.x.toNat * A.B.toNat < 2 ^ 32 := by omega
    have hg := A.gid_toNat hcB hGB
    refine (wpR_sound (cut := fun _ => false) ?_).weaken fun s h d hq => hq.1
    simp only [@EVAL@, Scan32.foot, ↓reduceIte]
    try simp only [show A.sh @SHNAME@ = A.sb from rfl]
    ptx_branches4
    all_goals ptx_addrs4 [A.sb, A.x] [t.tid.x.toNat, t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat]
    all_goals (try and_intros)
    all_goals first
      | trivial
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
         simp only [Scan32.V, Block.Args.seg, Nat.zero_div, lo32_ext32, lo32_rd_b4, lo32_ofInt_zero]
         split <;> first | rfl | (exfalso; omega))
      | (simp (config := { failIfUnchanged := false }) only [code, Code.Tc, phaseT, upd, String.reduceEq,
           ↓reduceIte, true_and, and_true]
         all_goals (try and_intros)
         all_goals first
           | ptx_reg4
           | assumption
           | (rw [Ptx.Auto.ule_toNat, hg])
           | (rw [Ptx.Auto.ult_toNat, hg]))
    done
  · -- phase 2i + 1: read s[tid - 2^i], then a barrier
    intro A hpre m₀ sh₀ t ht i hiR s hs
    obtain ⟨hc, hi, hcB, hGB, -, -, -, -⟩ := A.thread_facts hpre.2.2.2.2.1 ht
    obtain ⟨sal, fsbB, hBW⟩ := fits_sb fit A hpre
    obtain ⟨-, sbb, -⟩ := A.sb_facts fit hpre.2.2.2.2.2.2.2.2.2.2.2
    have fsb : Fits A.sb @W@ := by unfold Fits; omega
    have hpw := pow_lt A hpre hiR
    have hpw2 : i ≥ 1 → 2 ^ (i - 1) * 2 = 2 ^ i := fun h => by
      rw [← Nat.pow_succ]; congr 1; omega
    have hmid : 2 * i / 2 = i := by omega
    have hp0 : i = 0 → 2 ^ i = 1 := fun h => by rw [h]
    have hB2 : 2 ≤ A.B.toNat := by
      have := pow_lt A hpre (i := 0) (by omega); simp at this; omega
    obtain ⟨pc, r, p⟩ := s
    rw [foot_read A t hiR]
    refine (wpR_sound (cut := fun _ => false) ?_).weaken fun s h d hq => hq.1
    rcases T_odd hs with ⟨hi0, rfl, @PAT1@⟩ | ⟨hi1, rfl, @PATA@⟩
    · simp only [@EVAL@@HYP1@, ↓reduceIte, foot_read A t hiR,
        show 2 * i + 1 ≠ 0 by omega, show (2 * i + 1) % 2 = 1 by omega, hmid,
        show 2 * i ≠ 2 * A.j + 1 by omega]
      try simp only [show A.sh @SHNAME@ = A.sb from rfl]
      ptx_branches4
      all_goals ptx_addrs4 [A.sb] [t.tid.x.toNat - 2 ^ i]
@READ_ALTS@
    · simp only [@EVAL@@HYPA@, ↓reduceIte, foot_read A t hiR,
        show 2 * i + 1 ≠ 0 by omega, show (2 * i + 1) % 2 = 1 by omega, hmid,
        show 2 * i ≠ 2 * A.j + 1 by omega]
      try simp only [show A.sh @SHNAME@ = A.sb from rfl]
      ptx_branches4
      all_goals ptx_addrs4 [A.sb] [t.tid.x.toNat - 2 ^ i]
@READ_ALTS@
  · -- phase 2i + 2: add what was read to s[tid], then a barrier
    intro A hpre m₀ sh₀ t ht i hiR s hs
    obtain ⟨hc, hi, hcB, hGB, -, -, -, -⟩ := A.thread_facts hpre.2.2.2.2.1 ht
    obtain ⟨sal, fsbB, hBW⟩ := fits_sb fit A hpre
    obtain ⟨-, sbb, -⟩ := A.sb_facts fit hpre.2.2.2.2.2.2.2.2.2.2.2
    have fsb : Fits A.sb @W@ := by unfold Fits; omega
    have hpw := pow_lt A hpre hiR
    obtain ⟨pc, r, p⟩ := s
    obtain ⟨rfl, @PATR@⟩ := T_even hs
    rw [foot_add A t hiR]
    refine (wpR_sound (cut := fun _ => false) ?_).weaken fun s h d hq => hq.1
    simp only [@EVAL@@HYPR@, ↓reduceIte,
      foot_add A t hiR, show 2 * i + 2 ≠ 0 by omega, show (2 * i + 2) % 2 = 0 by omega,
      show ¬ ((0 : Nat) = 1) by decide, show (2 * i + 1) / 2 = i by omega,
      show (2 * i + 2) / 2 = i + 1 by omega, show 2 * i + 1 ≠ 2 * A.j + 1 by omega,
      show 2 * i + 2 ≠ 2 * A.j + 1 by omega]
    try simp only [show A.sh @SHNAME@ = A.sb from rfl]
    ptx_branches4
    all_goals ptx_addrs4 [A.sb] [t.tid.x.toNat]
    all_goals (try and_intros)
    all_goals first
      | trivial
      | (exfalso; omega)
      | exact accessOk_elem_mem (N := @W@) (by simp) fsb sal (by omega)
      | exact fun y hy => .inr ⟨trivial, hy⟩
      | exact fun y hy => .inr ⟨rfl, hy⟩
      | exact fun y hy => ⟨trivial, hy⟩
      | exact fun y hy => ⟨rfl, hy⟩
      | (rintro ⟨sp, y⟩ ⟨hsp, hy⟩
         try simp only at hsp
         subst hsp
         refine wr_cells fsbB hi hy ?_
         simp only [lo32_ext32, lo32_rd_b4]
         rw [rd32_cells fsbB hi]
         simp only [Scan32.V, Scan32.rv]
         split <;> simp)
      | (simp (config := { failIfUnchanged := false }) only [code, Code.Tc, phaseT, upd, String.reduceEq,
           ↓reduceIte, true_and, and_true, show 2 * i + 2 + 1 ≠ 1 by omega,
           show ¬ ((2 * i + 2 + 1) % 2 = 0) by omega, show (2 * i + 2 + 1) / 2 - 1 = i by omega]
         all_goals (try and_intros)
         all_goals first | ptx_reg4 | rfl | assumption)
    done
  · -- phase 2R + 1: store s[tid] to out[gid] when gid < n
    intro A hpre m₀ sh₀ t ht s hs
    obtain ⟨hc, hi, hcB, hGB, -, -, -, -⟩ := A.thread_facts hpre.2.2.2.2.1 ht
    obtain ⟨sal, fsbB, hBW⟩ := fits_sb fit A hpre
    obtain ⟨-, sbb, -⟩ := A.sb_facts fit hpre.2.2.2.2.2.2.2.2.2.2.2
    have fsb : Fits A.sb @W@ := by unfold Fits; omega
    have fout := hpre.2.2.2.2.2.2.2.2.1
    have oal := hpre.2.2.2.2.2.2.2.2.2.1
    have hBR := hpre.2.2.1
    have hpw2 : A.j ≥ 1 → 2 ^ (A.j - 1) * 2 = 2 ^ A.j := fun h => by
      rw [← Nat.pow_succ]; congr 1; omega
    have hR0 : A.j = 0 → A.B.toNat = 1 := fun h => by
      rw [h] at hBR; have := hpre.1; simp at hBR; omega
    have hmid : 2 * A.j / 2 = A.j := by omega
    have hcB' : t.ctaid.x.toNat * A.B.toNat < 2 ^ 32 := by omega
    have hg := A.gid_toNat hcB hGB
    obtain ⟨pc, r, p⟩ := s
    rw [foot_store A t]
    refine (wpR_sound (cut := fun _ => false) ?_).weaken fun s h d hq => hq.1
    rcases T_odd hs with ⟨hi0, rfl, @PAT1@⟩ | ⟨hi1, rfl, @PATA@⟩
    · have hB1 := hR0 hi0
      simp only [@EVAL@@HYP1@, ↓reduceIte, foot_store A t,
        hmid, show 2 * A.j ≠ 2 * A.j + 1 by omega, show ¬ (2 * A.j + 1 + 1 < 2 * A.j + 2) by omega]
      try simp only [show A.sh @SHNAME@ = A.sb from rfl]
      ptx_branches4
      all_goals ptx_addrs4 [A.sb, A.out] [t.tid.x.toNat, t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat]
@STORE_ALTS@
    · have h1 := hpw2 hi1
      have h2 : 2 ^ (A.j - 1) < A.B.toNat := by rcases hpre.2.2.2.1 with h | h <;> omega
      simp only [@EVAL@@HYPA@, ↓reduceIte, foot_store A t,
        hmid, show 2 * A.j ≠ 2 * A.j + 1 by omega, show ¬ (2 * A.j + 1 + 1 < 2 * A.j + 2) by omega]
      try simp only [show A.sh @SHNAME@ = A.sb from rfl]
      ptx_branches4
      all_goals ptx_addrs4 [A.sb, A.out] [t.tid.x.toNat, t.ctaid.x.toNat * A.B.toNat + t.tid.x.toNat]
@STORE_ALTS@

theorem correct : Scan32.Correct spec @K@ := correct_of fit code obligations

end E5rCheck

#print axioms E5rCheck.correct
