import Theories.ELF
import Projects.ClampSpec
import Projects.clamp.Image

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Clamp
open RV32

-- Independent ELF reader agrees with the actual e5r loaded memory, not a hash.
theorem image_fidelity : loadElf Exported.elfBytes = .ok (Exported.entry, Exported.image) := by
  decide +kernel

-- Successful instruction-level reachability, exact result and whole-memory frame
-- for all 256 inputs, including both sides of the conditional branch.
theorem all_byte_inputs : ∀ input : Fin 256, check Exported.image Exported.entry 0x101c 7 input.val = true := by
  decide +kernel

theorem bounded_safety (input : Nat) (h : input < 256) :
    Ensures Exported.image Exported.entry 0x101c 7 input :=
  check_sound (all_byte_inputs ⟨input, h⟩)

#print axioms bounded_safety
#print axioms image_fidelity
#print axioms all_byte_inputs
end Clamp
