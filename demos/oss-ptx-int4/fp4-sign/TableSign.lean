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
  Nat.lor (table i) (if negative then 0x80000000 else 0)

-- Kernel reduction checks all 16 finite table/sign cases in the actual FP model.
-- This is a local lemma, not a whole-kernel PTX equivalence certificate.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem table_sign : ∀ (i : Fin 8) (negative : Bool),
    fmul .f32 .rn true false (table i) (originalSign negative) =
      some (inserted i negative) := by decide +kernel

-- Identical intermediate bits imply identical modeled final scale products,
-- including subnormals, infinities and the model's nondeterministic NaNs.
theorem scaled_sign (i : Fin 8) (negative : Bool) (scale : Nat) :
    (fmul .f32 .rn true false (table i) (originalSign negative)).bind
      (fun signed => fmul .f32 .rn true false scale signed) =
    fmul .f32 .rn true false scale (inserted i negative) := by
  rw [table_sign]
  rfl

-- Original 16-bit sign extraction and rewritten 32-bit masks agree for
-- every possible zero-extended byte, independently of the table and scale.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem byte_sign_masks : ∀ b : Fin 256,
    (((b.val >>> 6) &&& 2) <<< 30 = (b.val <<< 24) &&& 0x80000000) ∧
    ((((b.val &&& 8) >>> 2) <<< 30) = (b.val <<< 28) &&& 0x80000000) := by
  decide +kernel

#print axioms byte_sign_masks
#print axioms table_sign
#print axioms scaled_sign
end FP4Sign
