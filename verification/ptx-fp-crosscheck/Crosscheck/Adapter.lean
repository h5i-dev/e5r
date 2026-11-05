import Ptx.Semantics.Float
import Fp.Addition
import Fp.Subtraction
import Fp.Multiplication
import Fp.Division
import Fp.FMA
import Fp.Sqrt

/- Independent arithmetic only. PTX modifiers and the NaN oracle stay in Ptx.Fp.
   Upstream's `s` is the fraction width, not the precision including the hidden bit. -/
namespace Crosscheck
open Ptx.Fp

def mode : RMode → RoundingMode
  | .rn => .RNE | .rz => .RTZ | .rm => .RTN | .rp => .RTP

def unpack (F : Fmt) (bits : Nat) : PackedFloat F.eb F.fb :=
  PackedFloat.ofBits F.eb F.fb (BitVec.ofNat _ bits)

def observe (x : PackedFloat e s) : Option Nat :=
  if x.isNaN then none else some x.toBits.toNat

inductive Op where
  | add | sub | mul | div | fma | sqrt
  deriving Repr, BEq

def upstream (F : Fmt) (m : RMode) (op : Op) (a b c : Nat) : Option Nat :=
  let x := unpack F a
  let y := unpack F b
  let z := unpack F c
  observe <| match op with
  | .add => PackedFloat.add (mode m) x y
  | .sub => PackedFloat.sub (mode m) x y
  | .mul => PackedFloat.mul (mode m) x y
  | .div => PackedFloat.div (mode m) x y
  | .fma => PackedFloat.fma (mode m) x y z
  | .sqrt => _root_.sqrt x (mode m)

def production (F : Fmt) (m : RMode) (op : Op) (a b c : Nat) : Option Nat :=
  match op with
  | .add => fadd F m false false a b
  | .sub => fsub F m false false a b
  | .mul => fmul F m false false a b
  | .div => fdiv F m false a b
  | .fma => ffma F m false false a b c
  | .sqrt => fsqrt F m false a

/-- The unresolved generic arithmetic bridge, stated without assuming it. -/
def Agrees (F : Fmt) (m : RMode) (op : Op) : Prop :=
  ∀ a b c, a < 2^(1+F.eb+F.fb) → b < 2^(1+F.eb+F.fb) →
    c < 2^(1+F.eb+F.fb) → upstream F m op a b c = production F m op a b c
end Crosscheck
