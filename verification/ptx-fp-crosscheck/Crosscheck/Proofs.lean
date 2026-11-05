import Crosscheck.Adapter

namespace Crosscheck
open Ptx.Fp

/-- Observation respects upstream's exact NaN equivalence, retaining signed zero. -/
theorem observe_equiv {x y : PackedFloat e s} (h : x.EquivUptoNaN y) :
    observe x = observe y := by
  rcases h with h | ⟨hx, hy⟩
  · rw [h]
  · simp [observe, hx, hy]

/-- A symbolic bit-vector rewrite useful in sign-manipulating kernels. -/
theorem observe_neg_neg (x : PackedFloat e s) : observe (-(-x)) = observe x := by
  rw [PackedFloat.neg_neg]

/-- Symbolic NaN propagation on the production side, with arbitrary inputs and mode. -/
theorem production_add_nan (F : Fmt) (m : RMode) (a b : Nat)
    (h : F.isNaN a = true) : production F m .add a b 0 = none := by
  simp [production, fadd, Fmt.flush, Fmt.sat, addCore, h]

-- Kernel-reduced examples: these are proofs of individual equalities, not universal
-- equivalence. `decide` is kernel checked; no native_decide or evaluator axiom.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem f32_subnormal_add :
    upstream Fmt.f32 .rn .add 1 1 0 = production Fmt.f32 .rn .add 1 1 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem f64_subnormal_add :
    upstream Fmt.f64 .rn .add 1 1 0 = production Fmt.f64 .rn .add 1 1 0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem f32_tie_even :
    upstream Fmt.f32 .rn .add 0x3f800000 0x33800000 0 = some 0x3f800000 ∧
    production Fmt.f32 .rn .add 0x3f800000 0x33800000 0 = some 0x3f800000 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem f64_tie_even :
    upstream Fmt.f64 .rn .add 0x3ff0000000000000 0x3ca0000000000000 0 = some 0x3ff0000000000000 ∧
    production Fmt.f64 .rn .add 0x3ff0000000000000 0x3ca0000000000000 0 = some 0x3ff0000000000000 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem f32_fma_cancellation :
    upstream Fmt.f32 .rn .fma 0x3f800001 0x3f7ffffe 0xbf800000 = some 0xa8800000 ∧
    production Fmt.f32 .rn .fma 0x3f800001 0x3f7ffffe 0xbf800000 = some 0xa8800000 := by
  decide +kernel
end Crosscheck

namespace Crosscheck
open Ptx.Fp
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Both zero signs and every rounding direction, including directed exact-zero rules. -/
theorem f32_signed_zero_add (a b : Bool) (m : RMode) :
    upstream Fmt.f32 m .add (Fmt.f32.zero a) (Fmt.f32.zero b) 0 =
    production Fmt.f32 m .add (Fmt.f32.zero a) (Fmt.f32.zero b) 0 := by
  cases a <;> cases b <;> cases m <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem f64_signed_zero_add (a b : Bool) (m : RMode) :
    upstream Fmt.f64 m .add (Fmt.f64.zero a) (Fmt.f64.zero b) 0 =
    production Fmt.f64 m .add (Fmt.f64.zero a) (Fmt.f64.zero b) 0 := by
  cases a <;> cases b <;> cases m <;> decide +kernel
end Crosscheck
