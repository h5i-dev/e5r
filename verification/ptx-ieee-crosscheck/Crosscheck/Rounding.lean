import FP.IEEE.Spec.RoundingModes
import FP.IEEE.Spec.RealRounding
import Ptx.Semantics.FloatCore

/-!
# The model's rounding core against lean-ieee754

For every format of the model (`fmt_f32`, `fmt_f64`: they are lean-ieee754's
`binary32` and `binary64`), every rounding mode of PTX (`.rn .rz .rm .rp` as
`nearestEven towardZero towardNegative towardPositive`) and every rational:

* `roundInt_eq`: `Ptx.Fp.roundInt` is `roundInteger`;
* `ilog2_eq`: `Ptx.Fp.ilog2` is `Int.log 2`;
* `roundQ_eq`: `Ptx.Fp.roundQ` is `roundWithMode` (gradual underflow);
* `precRoundQ_eq`, `overflows_iff`, `tiny_iff`: the overflow test of IEEE
  754-2019 §7.4 and the tininess-after-rounding test of §7.5 (the one
  `.ftz` flushes on) are `OverflowWithMode` and `TinyWithMode`;
* `roundSqrtQ_eq`: `Ptx.Fp.roundSqrtQ` is `roundWithMode` of `Real.sqrt`.

Not covered here: the bit-pattern layer of `Ptx/Semantics/Float.lean`
(decoding, encoding, special operands, zero signs, NaN, `.sat`), which the
GPU differential test checks.
-/

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

theorem zpow2_mul (x y : ℤ) : (2:ℝ) ^ x * (2:ℝ) ^ y = (2:ℝ) ^ (x + y) :=
  (zpow_add₀ (by norm_num) x y).symm

/-- `ilog2` brackets `q` between consecutive powers of two. -/
theorem ilog2_bracket (q : ℚ) (hq : 0 < q) :
    (2:ℝ) ^ (Ptx.Fp.ilog2 q) ≤ (q:ℝ) ∧ (q:ℝ) < (2:ℝ) ^ (Ptx.Fp.ilog2 q + 1) := by
  have hnum : 0 < q.num := Rat.num_pos.mpr hq
  set n := q.num.natAbs with hn
  set d := q.den with hd
  have hn0 : n ≠ 0 := by omega
  have hd0 : d ≠ 0 := q.den_nz
  have hqr : (q:ℝ) = (n:ℝ) / (d:ℝ) := by
    rw [Rat.cast_def]
    congr 1
    rw [hn, Nat.cast_natAbs]; push_cast [abs_of_pos hnum]; rfl
  have h1 : ((2:ℝ) ^ (Nat.log2 n : ℤ)) ≤ n := by
    rw [zpow_natCast]; exact_mod_cast Nat.log2_self_le hn0
  have h2 : (n:ℝ) < (2:ℝ) ^ ((Nat.log2 n : ℤ) + 1) := by
    rw [show ((Nat.log2 n : ℤ) + 1) = ((Nat.log2 n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    exact_mod_cast Nat.lt_log2_self
  have h3 : ((2:ℝ) ^ (Nat.log2 d : ℤ)) ≤ d := by
    rw [zpow_natCast]; exact_mod_cast Nat.log2_self_le hd0
  have h4 : (d:ℝ) < (2:ℝ) ^ ((Nat.log2 d : ℤ) + 1) := by
    rw [show ((Nat.log2 d : ℤ) + 1) = ((Nat.log2 d + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    exact_mod_cast Nat.lt_log2_self
  have hdpos : (0:ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
  set k : ℤ := (Nat.log2 n : ℤ) - (Nat.log2 d : ℤ) with hk
  have lower : (2:ℝ) ^ (k - 1) < (q:ℝ) := by
    rw [hqr, lt_div_iff₀ hdpos]
    calc (2:ℝ) ^ (k - 1) * d < (2:ℝ) ^ (k - 1) * (2:ℝ) ^ ((Nat.log2 d : ℤ) + 1) :=
          mul_lt_mul_of_pos_left h4 (by positivity)
      _ = (2:ℝ) ^ (Nat.log2 n : ℤ) := by rw [zpow2_mul]; congr 1; omega
      _ ≤ n := h1
  have upper : (q:ℝ) < (2:ℝ) ^ (k + 1) := by
    rw [hqr, div_lt_iff₀ hdpos]
    calc (n:ℝ) < (2:ℝ) ^ ((Nat.log2 n : ℤ) + 1) := h2
      _ = (2:ℝ) ^ (k + 1) * (2:ℝ) ^ (Nat.log2 d : ℤ) := by rw [zpow2_mul]; congr 1; omega
      _ ≤ (2:ℝ) ^ (k + 1) * d := mul_le_mul_of_nonneg_left h3 (by positivity)
  have hdef : Ptx.Fp.ilog2 q = if q < Ptx.Fp.pow2 k then k - 1 else k := rfl
  rw [hdef]
  split_ifs with h
  · have h' : (q:ℝ) < (2:ℝ) ^ k := by rw [← pow2_eq]; exact_mod_cast h
    exact ⟨lower.le, by simpa using h'⟩
  · have h' : (2:ℝ) ^ k ≤ (q:ℝ) := by rw [← pow2_eq]; exact_mod_cast (not_lt.mp h)
    exact ⟨h', upper⟩

/-- `ilog2` is Mathlib's `Int.log 2` (what lean-ieee754's quantum uses). -/
theorem ilog2_eq (q : ℚ) (hq : 0 < q) : Ptx.Fp.ilog2 q = Int.log 2 (q : ℝ) := by
  obtain ⟨h1, h2⟩ := ilog2_bracket q hq
  have hr : (0:ℝ) < q := by exact_mod_cast hq
  have a := (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hr).1 (by exact_mod_cast h1)
  have b := (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hr).1 (by exact_mod_cast h2)
  omega

theorem abs_eq (q : ℚ) : q.abs = |q| := by
  unfold Rat.abs; split_ifs with h
  · exact (abs_of_nonneg h).symm
  · exact (abs_of_neg (lt_of_not_ge h)).symm

/-- A format of the model as a lean-ieee754 `Format`. -/
def fmt (F : Ptx.Fp.Fmt) (h : F.emin ≤ F.emax) : Format := ⟨F.fb, F.emin, F.emax, h⟩

theorem f32_emin : Ptx.Fp.Fmt.f32.emin ≤ Ptx.Fp.Fmt.f32.emax := by decide
theorem f64_emin : Ptx.Fp.Fmt.f64.emin ≤ Ptx.Fp.Fmt.f64.emax := by decide

/-- The model's formats are lean-ieee754's `binary32` and `binary64`. -/
theorem fmt_f32 : fmt Ptx.Fp.Fmt.f32 f32_emin = binary32 := by
  simp only [fmt, binary32, Ptx.Fp.Fmt.f32, Ptx.Fp.Fmt.emin, Ptx.Fp.Fmt.emax, Ptx.Fp.Fmt.bias, Format.mk.injEq]; decide
theorem fmt_f64 : fmt Ptx.Fp.Fmt.f64 f64_emin = binary64 := by
  simp only [fmt, binary64, Ptx.Fp.Fmt.f64, Ptx.Fp.Fmt.emin, Ptx.Fp.Fmt.emax, Ptx.Fp.Fmt.bias, Format.mk.injEq]; decide

theorem log_abs_eq (q : ℚ) (hq : q ≠ 0) : Ptx.Fp.ilog2 q.abs = Int.log 2 |(q : ℝ)| := by
  rw [abs_eq, ilog2_eq _ (abs_pos.mpr hq), Rat.cast_abs]

theorem scaled_cast (q : ℚ) (e : ℤ) : ((q / Ptx.Fp.pow2 e : ℚ) : ℝ) = (q : ℝ) / (2:ℝ) ^ e := by
  push_cast [pow2_eq]; rfl

/-- **Rounding.** `roundQ` (gradual underflow, no upper exponent bound) is
lean-ieee754's `roundWithMode`, for every rational, format and mode. -/
theorem roundQ_eq (F : Ptx.Fp.Fmt) (h : F.emin ≤ F.emax) (m : Ptx.Fp.RMode) (q : ℚ) :
    ((Ptx.Fp.roundQ F m q : ℚ) : ℝ) = roundWithMode (fmt F h) (mode m) (q : ℝ) := by
  unfold Ptx.Fp.roundQ roundWithMode Format.quantum Format.quantumExponent
  split_ifs with hq
  · subst hq; simp
  · simp only [Ptx.Fp.qexp, fmt]
    rw [log_abs_eq q hq]
    push_cast [pow2_eq]
    rw [roundInt_eq, scaled_cast]

/-- `precRoundQ` is lean-ieee754's `precisionRoundWithMode`. -/
theorem precRoundQ_eq (F : Ptx.Fp.Fmt) (h : F.emin ≤ F.emax) (m : Ptx.Fp.RMode) (q : ℚ) :
    ((Ptx.Fp.precRoundQ F m q : ℚ) : ℝ) = precisionRoundWithMode (fmt F h) (mode m) (q : ℝ) := by
  unfold Ptx.Fp.precRoundQ precisionRoundWithMode
  split_ifs with hq
  · subst hq; simp
  · simp only [fmt]
    rw [log_abs_eq q hq]
    push_cast [pow2_eq]
    rw [roundInt_eq, scaled_cast]

theorem maxFinite_eq (F : Ptx.Fp.Fmt) (h : F.emin ≤ F.emax) :
    ((Ptx.Fp.maxFinite F : ℚ) : ℝ) = (fmt F h).maxFinite := by
  unfold Ptx.Fp.maxFinite Format.maxFinite
  have : 1 ≤ 2 ^ (F.fb + 1) := Nat.one_le_two_pow
  push_cast [Nat.cast_sub this, pow2_eq]
  simp [fmt]

/-- **Overflow** (IEEE 754-2019 §7.4) is lean-ieee754's `OverflowWithMode`. -/
theorem overflows_iff (F : Ptx.Fp.Fmt) (h : F.emin ≤ F.emax) (m : Ptx.Fp.RMode) (q : ℚ) :
    Ptx.Fp.overflows F m q = true ↔ OverflowWithMode (fmt F h) (mode m) (q : ℝ) := by
  unfold Ptx.Fp.overflows OverflowWithMode
  rw [decide_eq_true_iff, abs_eq, ← maxFinite_eq F h, ← precRoundQ_eq F h, ← Rat.cast_abs, Rat.cast_lt]

/-- **Tininess after rounding** (§7.5, the `.ftz` flush test) is
lean-ieee754's `TinyWithMode`. -/
theorem tiny_iff (F : Ptx.Fp.Fmt) (h : F.emin ≤ F.emax) (m : Ptx.Fp.RMode) (q : ℚ) :
    Ptx.Fp.tiny F m q = true ↔ TinyWithMode (fmt F h) (mode m) (q : ℝ) := by
  unfold Ptx.Fp.tiny TinyWithMode
  have hmin : ((Ptx.Fp.minNormal F : ℚ) : ℝ) = (fmt F h).minNormal := by
    simp [Ptx.Fp.minNormal, Format.minNormal, pow2_eq, fmt]
  rw [Bool.and_eq_true, bne_iff_ne, decide_eq_true_iff, abs_eq, ← Rat.cast_lt (K := ℝ), Rat.cast_abs,
    precRoundQ_eq F h, hmin]
  constructor
  · rintro ⟨hq, hlt⟩
    refine ⟨?_, hlt⟩
    have hx : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    exact lt_of_lt_of_le (by positivity) (precisionRound_abs_lower (fmt F h) (mode m) (q : ℝ) hx)
  · rintro ⟨hpos, hlt⟩
    refine ⟨?_, hlt⟩
    rintro rfl
    simp [precisionRoundWithMode] at hpos

/-! ### Square root -/

theorem log_sqrt (q : ℚ) (hq : 0 < q) :
    Int.log 2 (Real.sqrt (q : ℝ)) = Int.fdiv (Ptx.Fp.ilog2 q) 2 := by
  obtain ⟨h1, h2⟩ := ilog2_bracket q hq
  set L := Ptx.Fp.ilog2 q
  set E := Int.fdiv L 2
  have hE : 2 * E ≤ L ∧ L < 2 * E + 2 := by
    have : E = L / 2 := by simp only [E, Int.fdiv_eq_ediv]; simp
    omega
  have hr : (0:ℝ) < q := by exact_mod_cast hq
  have sq : ∀ z : ℤ, ((2:ℝ) ^ z) ^ 2 = (2:ℝ) ^ (2 * z) := fun z => by
    rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
  have lo : (2:ℝ) ^ E ≤ Real.sqrt q := by
    apply Real.le_sqrt_of_sq_le
    rw [sq]; exact le_trans (zpow_le_zpow_right₀ (by norm_num) hE.1) h1
  have hi : Real.sqrt q < (2:ℝ) ^ (E + 1) := by
    rw [Real.sqrt_lt' (by positivity), sq]
    exact lt_of_lt_of_le h2 (zpow_le_zpow_right₀ (by norm_num) (by omega))
  have hs : (0:ℝ) < Real.sqrt q := Real.sqrt_pos.mpr hr
  have a := (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hs).1 (by exact_mod_cast lo)
  have b := (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hs).1 (by exact_mod_cast hi)
  omega

/-- `roundIntSqrt m y` rounds `√y` to an integer. -/
theorem roundIntSqrt_eq (m : Ptx.Fp.RMode) (y : ℚ) (hy : 0 ≤ y) :
    Ptx.Fp.roundIntSqrt m y = roundInteger (mode m) (Real.sqrt (y : ℝ)) := by
  set k : ℕ := Nat.sqrt y.floor.toNat with hk
  have hyr : (0:ℝ) ≤ y := by exact_mod_cast hy
  have hfl0 : 0 ≤ y.floor := by rw [floor_eq]; exact Int.floor_nonneg.mpr hyr
  have hfl : ((y.floor.toNat : ℕ) : ℤ) = y.floor := Int.toNat_of_nonneg hfl0
  have k2 : k * k ≤ y.floor.toNat := Nat.sqrt_le y.floor.toNat
  have k3 : y.floor.toNat < (k + 1) * (k + 1) := Nat.lt_succ_sqrt y.floor.toNat
  have hle : ((k * k : ℕ) : ℝ) ≤ (y : ℝ) := by
    have : ((k * k : ℕ) : ℤ) ≤ y.floor := by rw [← hfl]; exact_mod_cast k2
    have h' : ((y.floor : ℤ) : ℝ) ≤ y := by rw [floor_eq]; exact Int.floor_le _
    calc ((k * k : ℕ) : ℝ) = (((k * k : ℕ) : ℤ) : ℝ) := by push_cast; ring
      _ ≤ ((y.floor : ℤ) : ℝ) := by exact_mod_cast this
      _ ≤ y := h'
  have hlt : (y : ℝ) < (((k + 1) * (k + 1) : ℕ) : ℝ) := by
    have : y.floor + 1 ≤ (((k + 1) * (k + 1) : ℕ) : ℤ) := by rw [← hfl]; exact_mod_cast k3
    have h' : (y : ℝ) < ((y.floor : ℤ) : ℝ) + 1 := by rw [floor_eq]; exact Int.lt_floor_add_one _
    calc (y : ℝ) < ((y.floor : ℤ) : ℝ) + 1 := h'
      _ = (((y.floor + 1 : ℤ)) : ℝ) := by push_cast; ring
      _ ≤ (((((k + 1) * (k + 1) : ℕ) : ℤ)) : ℝ) := by exact_mod_cast this
      _ = _ := by push_cast; ring
  have hkr : (0:ℝ) ≤ k := by positivity
  have sk : (k : ℝ) ≤ Real.sqrt y :=
    Real.le_sqrt_of_sq_le (by rw [sq]; exact_mod_cast hle)
  have sk1 : Real.sqrt y < (k : ℝ) + 1 := by
    rw [Real.sqrt_lt' (by positivity), sq]; push_cast at hlt; linarith
  have hfloor : ⌊Real.sqrt (y : ℝ)⌋ = (k : ℤ) := by
    rw [Int.floor_eq_iff]; push_cast; exact ⟨sk, sk1⟩
  have hnn : ¬ Real.sqrt (y : ℝ) < 0 := not_lt.mpr (Real.sqrt_nonneg _)
  have hh : (((2 * k + 1 : ℕ) : ℚ) / 2 : ℝ) = (k : ℝ) + 1 / 2 := by push_cast; ring
  have hhpos : (0:ℝ) ≤ (k : ℝ) + 1 / 2 := by positivity
  cases m
  · -- nearest even: √y against k + ½ is y against (k + ½)²
    simp only [Ptx.Fp.roundIntSqrt, roundInteger, mode, roundEven, hfloor, ← hk]
    have c1 : (y < ((2 * k + 1 : ℕ) : ℚ) / 2 * (((2 * k + 1 : ℕ) : ℚ) / 2)) ↔
        Real.sqrt (y : ℝ) - (k : ℤ) < 1 / 2 := by
      rw [cast_lt_iff]; push_cast
      rw [show (Real.sqrt (y:ℝ) - k < 1 / 2) ↔ Real.sqrt y < k + 1 / 2 by constructor <;> intro <;> linarith,
        Real.sqrt_lt' (by positivity)]
      constructor <;> intro h <;> nlinarith
    have c2 : (((2 * k + 1 : ℕ) : ℚ) / 2 * (((2 * k + 1 : ℕ) : ℚ) / 2) < y) ↔
        1 / 2 < Real.sqrt (y : ℝ) - (k : ℤ) := by
      rw [cast_lt_iff]; push_cast
      rw [show (1 / 2 < Real.sqrt (y:ℝ) - k) ↔ (k : ℝ) + 1 / 2 < Real.sqrt y by constructor <;> intro <;> linarith,
        Real.lt_sqrt hhpos]
      constructor <;> intro h <;> nlinarith
    simp only [c1, c2]
  · simp only [Ptx.Fp.roundIntSqrt, roundInteger, mode, hfloor, hnn, ← hk, if_false]
  · simp only [Ptx.Fp.roundIntSqrt, roundInteger, mode, hfloor, ← hk]
  · simp only [Ptx.Fp.roundIntSqrt, roundInteger, mode, ← hk]
    split_ifs with he
    · have : Real.sqrt (y : ℝ) = k := by
        have hy' : (y : ℝ) = (k : ℝ) ^ 2 := by
          have := congrArg (fun z : ℚ => (z : ℝ)) he; push_cast at this; rw [this]; ring
        rw [hy', Real.sqrt_sq hkr]
      rw [this, Int.ceil_natCast]
    · have hne : (k : ℝ) < Real.sqrt y := by
        rcases lt_or_eq_of_le sk with h | h
        · exact h
        · exfalso; apply he
          have : (y : ℝ) = ((k * k : ℕ) : ℝ) := by
            rw [← Real.sq_sqrt hyr, ← h]; push_cast; ring
          exact_mod_cast this
      symm; rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith

/-- **Square root.** `roundSqrtQ F m q` is lean-ieee754's
`roundWithMode F m (√q)`, the finite result its `Sqrt` contract requires. -/
theorem roundSqrtQ_eq (F : Ptx.Fp.Fmt) (h : F.emin ≤ F.emax) (m : Ptx.Fp.RMode) (q : ℚ) (hq : 0 < q) :
    ((Ptx.Fp.roundSqrtQ F m q : ℚ) : ℝ) = roundWithMode (fmt F h) (mode m) (Real.sqrt (q : ℝ)) := by
  have hr : (0:ℝ) < q := by exact_mod_cast hq
  unfold Ptx.Fp.roundSqrtQ roundWithMode Format.quantum Format.quantumExponent
  simp only [fmt]
  rw [abs_of_nonneg (Real.sqrt_nonneg _), log_sqrt q hq]
  set e := max F.emin (Int.fdiv (Ptx.Fp.ilog2 q) 2) - (F.fb : ℤ)
  have hy : 0 ≤ q / Ptx.Fp.pow2 (2 * e) := by
    apply div_nonneg hq.le; unfold Ptx.Fp.pow2; split_ifs <;> positivity
  push_cast [pow2_eq]
  rw [roundIntSqrt_eq m _ hy, scaled_cast, Real.sqrt_div' _ (by positivity)]
  congr 3
  rw [show (2:ℝ) ^ (2 * e) = ((2:ℝ) ^ e) ^ 2 by rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring,
    Real.sqrt_sq (by positivity)]

end Crosscheck
