import Theories.Logic

set_option linter.constructorNameAsVariable false
set_option linter.unusedSimpArgs false

namespace E5R.Thermostat.RamRun
open E5R

/-- Deterministic evaluator for pure instructions and checked RAM/ROM accesses.
    MMIO, atomics, exceptions and nondeterministic effects fail closed. -/
def effect (B : Board) (img : List Segment) : Eff → (Word → BitVec 8) → Option Machine
  | .done c, ram => some ⟨c, ram⟩
  | .load w a false k, ram =>
    if a.toNat % w.bytes = 0 then
      if B.inRam a w.bytes then effect B img (k (ramRead ram a w)) ram
      else match romRead? img a.toNat w.bytes false with
        | some v => effect B img (k v) ram
        | none => none
    else none
  | .store w a v false k, ram =>
    if a.toNat % w.bytes = 0 ∧ B.inRam a w.bytes = true then
      effect B img k (ramWrite ram a v w)
    else none
  | _, _ => none

theorem effect_sound {B img e ram m} (h : effect B img e ram = some m) :
    ∀ o i evs, interp B img o e ram i evs = .ok m.core m.ram evs := by
  induction e generalizing ram with
  | done c => simp only [effect, Option.some.injEq] at h; subst m; intros; rfl
  | load w a atomic k ih =>
    cases atomic with
    | true => contradiction
    | false =>
      simp only [effect] at h
      split at h
      · rename_i ha
        split at h
        · rename_i hr
          intro o i evs
          simp only [interp, ha, ne_eq, not_true_eq_false, ↓reduceIte, hr]
          exact ih _ h o i evs
        · rename_i hr
          cases hv : romRead? img a.toNat w.bytes false with
          | none => simp [hv] at h
          | some v =>
            simp only [hv] at h
            intro o i evs
            simp only [interp, ha, ne_eq, not_true_eq_false, ↓reduceIte, hr, hv]
            exact ih _ h o i evs
      · contradiction
  | store w a v atomic k ih =>
    cases atomic with
    | true => contradiction
    | false =>
      simp only [effect] at h
      split at h
      · rename_i ha
        intro o i evs
        simp only [interp, ha.1, ne_eq, not_true_eq_false, ↓reduceIte, ha.2]
        exact ih h o i evs
      · contradiction
  | trap | unsupported | choose | pick => contradiction

def run (B : Board) (img : List Segment) : Nat → Machine → Option Machine
  | 0, m => some m
  | n+1, m => if m.core.pc.getLsbD 0 then none else
    match fetchDecode img m.core.pc with
    | none => none
    | some (i, len) => match effect B img (exec m.core len i) m.ram with
      | none => none
      | some m' => run B img n m'

theorem sound {B img n m m'} (h : run B img n m = some m') : DetSteps B img n m m' := by
  induction n generalizing m with
  | zero => simp only [run, Option.some.injEq] at h; subst m'; exact .refl _
  | succ n ih =>
    simp only [run] at h
    split at h
    · contradiction
    · rename_i ha
      cases hd : fetchDecode img m.core.pc with
      | none => simp [hd] at h
      | some pair =>
        obtain ⟨i, len⟩ := pair
        simp only [hd] at h
        cases he : effect B img (exec m.core len i) m.ram with
        | none => simp [he] at h
        | some m1 =>
          simp only [he] at h
          exact .step (detStep_of (by simpa using ha) hd (fun o => effect_sound he o 0 [])) (ih h)

end E5R.Thermostat.RamRun
