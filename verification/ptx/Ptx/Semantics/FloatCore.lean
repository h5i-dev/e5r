/-
The rounding core of the floating-point model (docs/verification-ptx.md,
"Floating point").

IEEE 754-2019 §4.3 defines rounding of an exact real result to a format:
the result is the representable number nearest the exact value in the
direction the attribute names, with gradual underflow (§7.5) and overflow
decided on the result rounded as if the exponent range were unbounded
(§7.4). Every exact result an instruction of the subset produces is
rational except a square root, so the core works on `Rat`:

* `ilog2 q` is `⌊log₂ |q|⌋`;
* `qexp F q` is the exponent of the last place of `q` in format `F`:
  `max(emin, ⌊log₂ |q|⌋) − p + 1`, clamped at the subnormal spacing;
* `roundInt m x` rounds a rational to an integer in direction `m`;
* `roundQ F m q` is `q` rounded to `F` with unbounded exponent above;
* `precRoundQ` is the same with neither exponent bound, the value the
  overflow test (§7.4) and the tininess test of `.ftz` look at;
* `roundSqrtQ` rounds `√q` the same way, deciding each comparison of `√q`
  with a rational `t ≥ 0` as `q` against `t²`.

This file imports nothing but core Lean, so it also compiles in the
project that cross-checks it against `lean-ieee754`'s `roundWithMode`
(docs/verification-ptx.md, "Cross-check").
-/
namespace Ptx.Fp

/-- PTX's rounding modifiers `.rn .rz .rm .rp` (and `.rni .rzi .rmi .rpi`
for rounding to an integer): nearest with ties to even, toward zero,
toward −∞, toward +∞. -/
inductive RMode where
  | rn | rz | rm | rp
  deriving Repr, DecidableEq, Inhabited

/-- A binary interchange format: `fb` fraction bits, `eb` exponent bits. -/
structure Fmt where
  fb : Nat
  eb : Nat
  deriving Repr, DecidableEq, Inhabited

/-- binary32 (`.f32`) and binary64 (`.f64`). -/
def Fmt.f32 : Fmt := ⟨23, 8⟩
def Fmt.f64 : Fmt := ⟨52, 11⟩

def Fmt.bias (F : Fmt) : Nat := 2 ^ (F.eb - 1) - 1
def Fmt.emin (F : Fmt) : Int := 1 - (F.bias : Int)
def Fmt.emax (F : Fmt) : Int := F.bias

/-- `2^k` for any integer `k`. -/
def pow2 (k : Int) : Rat :=
  if 0 ≤ k then ((2 ^ k.toNat : Nat) : Rat) else 1 / ((2 ^ (-k).toNat : Nat) : Rat)

/-- `⌊log₂ q⌋` for `q > 0`: `log₂ num − log₂ den` is that or one more. -/
def ilog2 (q : Rat) : Int :=
  let k : Int := (Nat.log2 q.num.natAbs : Int) - (Nat.log2 q.den : Int)
  if q < pow2 k then k - 1 else k

/-- Round a rational to an integer. -/
def roundInt : RMode → Rat → Int
  | .rn, x =>
    let k := x.floor
    let f := x - k
    if f < 1 / 2 then k else if 1 / 2 < f then k + 1 else k + k % 2
  | .rz, x => if x < 0 then x.ceil else x.floor
  | .rm, x => x.floor
  | .rp, x => x.ceil

/-- The exponent of the last place of `q` in `F`, with gradual underflow. -/
def qexp (F : Fmt) (q : Rat) : Int := max F.emin (ilog2 q.abs) - F.fb

/-- `q` rounded to `F`, gradual underflow, no upper exponent bound. -/
def roundQ (F : Fmt) (m : RMode) (q : Rat) : Rat :=
  if q = 0 then 0 else (roundInt m (q / pow2 (qexp F q)) : Rat) * pow2 (qexp F q)

/-- `q` rounded to `F`'s precision with no exponent bound at all. -/
def precRoundQ (F : Fmt) (m : RMode) (q : Rat) : Rat :=
  if q = 0 then 0 else
    let e := ilog2 q.abs - F.fb
    (roundInt m (q / pow2 e) : Rat) * pow2 e

/-- The largest finite number of `F`. -/
def maxFinite (F : Fmt) : Rat := ((2 ^ (F.fb + 1) - 1 : Nat) : Rat) * pow2 (F.emax - F.fb)

/-- The smallest normal number of `F`. -/
def minNormal (F : Fmt) : Rat := pow2 F.emin

/-- Overflow (§7.4): the result rounded with unbounded exponent range
exceeds the largest finite number. -/
def overflows (F : Fmt) (m : RMode) (q : Rat) : Bool := decide (maxFinite F < (precRoundQ F m q).abs)

/-- Tininess after rounding (§7.5): nonzero and, rounded with unbounded
exponent range, below the smallest normal number. -/
def tiny (F : Fmt) (m : RMode) (q : Rat) : Bool :=
  q != 0 && decide ((precRoundQ F m q).abs < minNormal F)

/-- Round `√y` to an integer, `y ≥ 0`: with `k = ⌊√y⌋ = Nat.sqrt ⌊y⌋`,
`√y` against `k + ½` is `y` against `(k + ½)²`, and `√y = k` is `y = k²`. -/
def roundIntSqrt (m : RMode) (y : Rat) : Int :=
  let k : Nat := Nat.sqrt y.floor.toNat
  let h : Rat := ((2 * k + 1 : Nat) : Rat) / 2
  match m with
  | .rn => if y < h * h then k else if h * h < y then k + 1 else k + k % 2
  | .rz | .rm => k
  | .rp => if y = ((k * k : Nat) : Rat) then k else k + 1

/-- `√q` rounded to `F`, `q > 0`. `⌊log₂ √q⌋ = ⌊⌊log₂ q⌋ / 2⌋`; the square
root of a positive finite number of either format is normal, so the
spacing is `2^(⌊log₂ √q⌋ − fb)` once clamped like `qexp`. -/
def roundSqrtQ (F : Fmt) (m : RMode) (q : Rat) : Rat :=
  let e := max F.emin (Int.fdiv (ilog2 q) 2) - F.fb
  (roundIntSqrt m (q / pow2 (2 * e)) : Rat) * pow2 e

end Ptx.Fp
