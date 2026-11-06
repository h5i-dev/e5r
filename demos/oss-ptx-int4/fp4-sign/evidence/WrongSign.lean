import Ptx.Semantics.Float

-- Exact binary32 bits from the pinned emitted PTX, not decimal re-rounding.
namespace FP4Sign
open Ptx.Fp

def table : Fin 8 → Nat
  | ⟨0, _⟩ => 0x00000000
  | ⟨1, _⟩ => 0x3baaaaab
  | ⟨2, _⟩ => 0x3f2aaaab
  | ⟨3, _⟩ => 0x3f800000
  | ⟨4, _⟩ => 0x3eaaaaab
  | ⟨5, _⟩ => 0x3f000000
  | ⟨6, _⟩ => 0x3e2aaaab
  | ⟨7, _⟩ => 0x3e800000

def originalSign (negative : Bool) : Nat :=
  (fsub .f32 .rn true false 0x3f800000
    (ofInt .f32 .rn false (if negative then 2 else 0))).getD 0

def inserted (i : Fin 8) (negative : Bool) : Nat :=
  Nat.lor (table i) (if negative then 0x40000000 else 0)


set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem wrong_sign_counterexample :
    fmul .f32 .rn true false (table ⟨0, by decide⟩) (originalSign true) ≠
      some (inserted ⟨0, by decide⟩ true) := by decide +kernel
#print axioms wrong_sign_counterexample
end FP4Sign
