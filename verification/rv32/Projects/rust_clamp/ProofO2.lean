import Theories.ELF
import Projects.ClampSpec
import Projects.rust_clamp.ImageO2
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RustO2
open RV32 Clamp

theorem image_fidelity : loadElf Exported.elfBytes = .ok (Exported.entry, Exported.image) := by
  decide +kernel

theorem all_byte_inputs : ∀ input : Fin 256,
    check Exported.image Exported.entry 0x1000 9 input.val = true := by
  decide +kernel

theorem bounded_safety (input : Nat) (h : input < 256) :
    Ensures Exported.image Exported.entry 0x1000 9 input :=
  check_sound (all_byte_inputs ⟨input, h⟩)

#print axioms image_fidelity
#print axioms all_byte_inputs
#print axioms bounded_safety
end RustO2
