import FP.IEEE.Spec.RoundingModes
import Ptx.Semantics.FloatCore

open FP.IEEE FP.IEEE.Spec

namespace Crosscheck

def mode : Ptx.Fp.RMode → RoundingMode
  | .rn => .nearestEven
  | .rz => .towardZero
  | .rm => .towardNegative
  | .rp => .towardPositive

theorem floor_eq (x : ℚ) : x.floor = ⌊(x : ℝ)⌋ := by rw [Rat.floor_cast]; rfl

theorem ceil_eq (x : ℚ) : x.ceil = ⌈(x : ℝ)⌉ := by
  rw [Rat.ceil_cast, Rat.ceil_eq_neg_floor_neg]
  show -⌊-x⌋ = ⌈x⌉
  rw [Int.floor_neg, neg_neg]

theorem cast_lt_iff (a b : ℚ) : a < b ↔ (a : ℝ) < (b : ℝ) := Rat.cast_lt.symm

theorem pow2_eq (k : ℤ) : ((Ptx.Fp.pow2 k : ℚ) : ℝ) = (2 : ℝ) ^ k := by
  unfold Ptx.Fp.pow2
  split_ifs with h
  · push_cast
    rw [← zpow_natCast]; congr 1; omega
  · push_cast
    rw [one_div, ← zpow_natCast, ← zpow_neg]; congr 1; omega

theorem roundInt_eq (m : Ptx.Fp.RMode) (x : ℚ) :
    Ptx.Fp.roundInt m x = roundInteger (mode m) (x : ℝ) := by
  have hf : ⌊(x : ℝ)⌋ = x.floor := (floor_eq x).symm
  have hc : ⌈(x : ℝ)⌉ = x.ceil := (ceil_eq x).symm
  have e1 : ((x : ℝ) - (x.floor : ℝ)) = ((x - x.floor : ℚ) : ℝ) := by push_cast; ring
  have half : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by push_cast; ring
  cases m <;> simp only [Ptx.Fp.roundInt, roundInteger, mode, roundEven, hf, hc]
  · rw [e1, ← half]; simp only [Rat.cast_lt]
  · rw [show (0 : ℝ) = ((0 : ℚ) : ℝ) by simp]; simp only [Rat.cast_lt]

end Crosscheck
