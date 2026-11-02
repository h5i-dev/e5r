/-
`.f32` and `.f64` instructions on bit patterns (docs/verification-ptx.md,
"Floating point"), from the PTX ISA (9.7.3 floating-point instructions,
9.3.1.2 comparisons, 9.7.10 `cvt`) and IEEE 754-2019.

A value is its bit pattern, a `Nat` below `2^(1 + eb + fb)`. An operation
returns `some bits`, or `none` where its result is a NaN. PTX does not fix
which NaN: single-precision instructions "return an unspecified NaN", and
double-precision ones support payloads without saying which input's
payload a result carries (on the A10G that depends on the operand order
ptxas chose). The instruction table (`Instruction.lean`) therefore takes
the bits of every NaN result from the launch's NaN oracle, and theorems
quantify over it.

The modifiers, as the ISA states them:

* `.rn .rz .rm .rp` (§4.3 rounding attributes); add, sub and mul without
  one may be fused into an fma by ptxas, so the parser refuses them;
* `.ftz` flushes subnormal inputs and results to sign-preserving zero. A
  result is flushed when it is tiny after rounding (§7.5), the test the A10G
  applies (`fma.rn.ftz` of a value just below the smallest normal that rounds
  up to it is not flushed);
* `.sat` clamps to `[+0.0, 1.0]`, NaN to `+0.0`;
* `min`/`max` return the non-NaN operand when one is NaN, treat `-0 < +0`,
  and with `.NaN` return NaN if either is;
* comparisons are ordered or unordered as in Tables 23 to 25;
* float-to-integer conversions clamp to the destination range, and a NaN
  converts to 0, or to `1 << (w − 1)` when the source is `.f64` or the
  destination is 64-bit.
-/
import Ptx.Semantics.FloatCore

namespace Ptx.Fp

namespace Fmt
variable (F : Fmt)

/-- The sign bit. -/
def signBit : Nat := 2 ^ (F.eb + F.fb)
/-- All-ones exponent field. -/
def expMax : Nat := 2 ^ F.eb - 1

def sgn (x : Nat) : Bool := x / F.signBit % 2 == 1
def bexp (x : Nat) : Nat := x / 2 ^ F.fb % 2 ^ F.eb
def frac (x : Nat) : Nat := x % 2 ^ F.fb

def isNaN (x : Nat) : Bool := F.bexp x == F.expMax && F.frac x != 0
def isInf (x : Nat) : Bool := F.bexp x == F.expMax && F.frac x == 0
def isZero (x : Nat) : Bool := F.bexp x == 0 && F.frac x == 0
def isSub (x : Nat) : Bool := F.bexp x == 0 && F.frac x != 0

def zero (neg : Bool) : Nat := if neg then F.signBit else 0
def inf (neg : Bool) : Nat := F.zero neg + F.expMax * 2 ^ F.fb
def maxFin (neg : Bool) : Nat := F.zero neg + (F.expMax - 1) * 2 ^ F.fb + (2 ^ F.fb - 1)
/-- `1.0`. -/
def one : Nat := F.bias * 2 ^ F.fb
/-- Only ever used where every NaN is acceptable. -/
def qnan : Nat := F.expMax * 2 ^ F.fb + 2 ^ (F.fb - 1)

/-- The value of a finite pattern (zeros, subnormals, normals). -/
def toQ (x : Nat) : Rat :=
  let mag : Rat :=
    if F.bexp x = 0 then (F.frac x : Rat) * pow2 (F.emin - F.fb)
    else ((F.frac x + 2 ^ F.fb : Nat) : Rat) * pow2 ((F.bexp x : Int) - F.bias - F.fb)
  if F.sgn x then -mag else mag

/-- The pattern of a nonzero finite number of `F` (subnormal or normal). -/
def encode (r : Rat) : Nat :=
  let a := r.abs
  let e := ilog2 a
  let s := F.zero (decide (r < 0))
  if e < F.emin then s + (a / pow2 (F.emin - F.fb)).floor.toNat
  else s + (e + F.bias).toNat * 2 ^ F.fb + ((a / pow2 (e - F.fb)).floor.toNat - 2 ^ F.fb)

/-- `.ftz` on an input: a subnormal becomes the zero of its sign. -/
def flush (ftz : Bool) (x : Nat) : Nat := if ftz && F.isSub x then F.zero (F.sgn x) else x

/-- Round the exact nonzero-or-zero result `q`; `zneg` is the sign an
exact zero takes (§6.3). Overflow gives infinity or the largest finite
number by direction (§7.4); with `ftz`, a tiny result is a zero. -/
def round (m : RMode) (ftz : Bool) (q : Rat) (zneg : Bool) : Nat :=
  let neg := decide (q < 0)
  if q = 0 then F.zero zneg
  else if overflows F m q then
    if m = .rn || (m = .rm && neg) || (m = .rp && !neg) then F.inf neg else F.maxFin neg
  else if ftz && tiny F m q then F.zero neg
  else
    let r := roundQ F m q
    if r = 0 then F.zero neg else F.encode r

/-- `.sat`: clamp to `[+0.0, 1.0]`, NaN to `+0.0`. -/
def sat (on : Bool) : Option Nat → Option Nat
  | none => if on then some 0 else none
  | some x =>
    if !on then some x
    else if F.isNaN x || F.sgn x then some 0
    else if F.isInf x || 1 < F.toQ x then some F.one
    else some x

end Fmt

open Fmt

/-- `add` (`neg_b` false) and `sub` (`neg_b` true) after `.ftz` on the
inputs. -/
def addCore (F : Fmt) (m : RMode) (ftz : Bool) (a b : Nat) : Option Nat :=
  if F.isNaN a || F.isNaN b then none
  else if F.isInf a && F.isInf b then (if F.sgn a == F.sgn b then some a else none)
  else if F.isInf a then some a
  else if F.isInf b then some b
  else
    let zneg := if F.isZero a && F.isZero b && F.sgn a == F.sgn b then F.sgn a else m == .rm
    some (F.round m ftz (F.toQ a + F.toQ b) zneg)

def negBits (F : Fmt) (x : Nat) : Nat := if F.sgn x then x - F.signBit else x + F.signBit

def fadd (F : Fmt) (m : RMode) (ftz sat : Bool) (a b : Nat) : Option Nat :=
  F.sat sat (addCore F m ftz (F.flush ftz a) (F.flush ftz b))

def fsub (F : Fmt) (m : RMode) (ftz sat : Bool) (a b : Nat) : Option Nat :=
  let b := F.flush ftz b
  F.sat sat (addCore F m ftz (F.flush ftz a) (if F.isNaN b then b else negBits F b))

def fmul (F : Fmt) (m : RMode) (ftz sat : Bool) (a b : Nat) : Option Nat :=
  let a := F.flush ftz a
  let b := F.flush ftz b
  let neg := F.sgn a != F.sgn b
  F.sat sat <|
    if F.isNaN a || F.isNaN b then none
    else if (F.isZero a && F.isInf b) || (F.isInf a && F.isZero b) then none
    else if F.isInf a || F.isInf b then some (F.inf neg)
    else some (F.round m ftz (F.toQ a * F.toQ b) neg)

/-- `fma.rnd d, a, b, c`: `a·b + c` rounded once. -/
def ffma (F : Fmt) (m : RMode) (ftz sat : Bool) (a b c : Nat) : Option Nat :=
  let a := F.flush ftz a
  let b := F.flush ftz b
  let c := F.flush ftz c
  let pneg := F.sgn a != F.sgn b
  F.sat sat <|
    if F.isNaN a || F.isNaN b || F.isNaN c then none
    else if (F.isZero a && F.isInf b) || (F.isInf a && F.isZero b) then none
    else if F.isInf a || F.isInf b then
      (if F.isInf c && F.sgn c != pneg then none else some (F.inf pneg))
    else if F.isInf c then some c
    else
      let zneg :=
        if (F.isZero a || F.isZero b) && F.isZero c && pneg == F.sgn c then pneg else m == .rm
      some (F.round m ftz (F.toQ a * F.toQ b + F.toQ c) zneg)

def fdiv (F : Fmt) (m : RMode) (ftz : Bool) (a b : Nat) : Option Nat :=
  let a := F.flush ftz a
  let b := F.flush ftz b
  let neg := F.sgn a != F.sgn b
  if F.isNaN a || F.isNaN b then none
  else if (F.isInf a && F.isInf b) || (F.isZero a && F.isZero b) then none
  else if F.isInf a then some (F.inf neg)
  else if F.isInf b then some (F.zero neg)
  else if F.isZero b then some (F.inf neg)
  else some (F.round m ftz (F.toQ a / F.toQ b) neg)

/-- `rcp.rnd`: `1 / a` rounded (IEEE division of 1.0). -/
def frcp (F : Fmt) (m : RMode) (ftz : Bool) (a : Nat) : Option Nat := fdiv F m ftz F.one a

def fsqrt (F : Fmt) (m : RMode) (ftz : Bool) (a : Nat) : Option Nat :=
  let a := F.flush ftz a
  if F.isNaN a then none
  else if F.isZero a then some a
  else if F.sgn a then none
  else if F.isInf a then some a
  else some (F.encode (roundSqrtQ F m (F.toQ a)))

/-- `neg`: the sign flips; a NaN input gives a NaN. -/
def fneg (F : Fmt) (ftz : Bool) (a : Nat) : Option Nat :=
  let a := F.flush ftz a
  if F.isNaN a then none else some (negBits F a)

def fabs (F : Fmt) (ftz : Bool) (a : Nat) : Option Nat :=
  let a := F.flush ftz a
  if F.isNaN a then none else some (if F.sgn a then a - F.signBit else a)

/-- `a < b` as numbers, with `-0 < +0` (the order `min`/`max` use). -/
def ltSigned (F : Fmt) (a b : Nat) : Bool :=
  if F.isInf a then F.sgn a && !(F.isInf b && F.sgn b)
  else if F.isInf b then !F.sgn b
  else if F.isZero a && F.isZero b then F.sgn a && !F.sgn b
  else decide (F.toQ a < F.toQ b)

/-- `min`/`max{.ftz}{.NaN}` (`isMax` selects `max`). -/
def fminmax (F : Fmt) (isMax ftz nanMod : Bool) (a b : Nat) : Option Nat :=
  let a := F.flush ftz a
  let b := F.flush ftz b
  if F.isNaN a && F.isNaN b then none
  else if nanMod && (F.isNaN a || F.isNaN b) then none
  else if F.isNaN a then some b
  else if F.isNaN b then some a
  else if isMax then some (if ltSigned F b a then a else b)
  else some (if ltSigned F a b then a else b)

/-- Floating-point comparisons of `setp` (Tables 23 to 25). -/
inductive FCmp where
  | eq | ne | lt | le | gt | ge | equ | neu | ltu | leu | gtu | geu | num | nan
  deriving Repr, DecidableEq, Inhabited

/-- The order of two non-NaN values as numbers (`-0 = +0`). -/
def cmpNum (F : Fmt) (a b : Nat) : Ordering :=
  if F.isZero a && F.isZero b then .eq
  else if ltSigned F a b then .lt
  else if ltSigned F b a then .gt
  else .eq

def fsetp (F : Fmt) (c : FCmp) (ftz : Bool) (a b : Nat) : Bool :=
  let a := F.flush ftz a
  let b := F.flush ftz b
  let un := F.isNaN a || F.isNaN b
  let o := cmpNum F a b
  match c with
  | .eq => !un && o == .eq
  | .ne => !un && o != .eq
  | .lt => !un && o == .lt
  | .le => !un && o != .gt
  | .gt => !un && o == .gt
  | .ge => !un && o != .lt
  | .equ => un || o == .eq
  | .neu => un || o != .eq
  | .ltu => un || o == .lt
  | .leu => un || o != .gt
  | .gtu => un || o == .gt
  | .geu => un || o != .lt
  | .num => !un
  | .nan => un

/-- `cvt.irnd.{u,s}{32,64}.f` (`w` the destination width): round to an
integer, clamp to the destination range, NaN as the ISA states. -/
def toInt (F : Fmt) (m : RMode) (ftz signed : Bool) (w : Nat) (a : Nat) : Nat :=
  let a := F.flush ftz a
  let lo : Int := if signed then -(2 ^ (w - 1) : Nat) else 0
  let hi : Int := if signed then (2 ^ (w - 1) - 1 : Nat) else (2 ^ w - 1 : Nat)
  let enc (v : Int) : Nat := (v % (2 ^ w : Nat)).toNat
  if F.isNaN a then (if F = Fmt.f64 || w = 64 then 2 ^ (w - 1) else 0)
  else if F.isInf a then enc (if F.sgn a then lo else hi)
  else enc (max lo (min hi (roundInt m (F.toQ a))))

/-- `cvt.frnd.f.{u,s}{32,64}`: the integer `v` rounded to `F`. -/
def ofInt (F : Fmt) (m : RMode) (ftz : Bool) (v : Int) : Nat := F.round m ftz v false

/-- `cvt.irnd.f.f` within one format: round to an integral value. -/
def roundIntegral (F : Fmt) (m : RMode) (ftz : Bool) (a : Nat) : Option Nat :=
  let a := F.flush ftz a
  if F.isNaN a then none
  else if F.isInf a || F.isZero a then some a
  else
    let v := roundInt m (F.toQ a)
    some (if v = 0 then F.zero (F.sgn a) else F.encode v)

/-- `cvt{.frnd}{.ftz}{.sat}.D.S` between formats: exact when widening
(`m` unused), rounded when narrowing. `.ftz` applies to `.f32` inputs and
results only. -/
def convertF (D S : Fmt) (m : RMode) (ftz sat : Bool) (a : Nat) : Option Nat :=
  let ftzS := ftz && S = Fmt.f32
  let ftzD := ftz && D = Fmt.f32
  let a := S.flush ftzS a
  D.sat sat <|
    if S.isNaN a then none
    else if S.isInf a then some (D.inf (S.sgn a))
    else if S.isZero a then some (D.zero (S.sgn a))
    else some (D.round m ftzD (S.toQ a) (S.sgn a))

end Ptx.Fp
