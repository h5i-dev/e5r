import Projects.clamp.Image
import Theories.ELF
import Projects.ClampSpec
open RV32
namespace Negative
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def single (w : Nat) (pc := 4096) (execute := true) : State :=
  { pc := pc, mem := [⟨4096, [w%256,w/256%256,w/65536%256,w/16777216%256], true, false, execute⟩] }

-- C, M, CSR, ECALL, reserved branch and non-word load/store must fail.
theorem unsupported : ∀ w ∈ [0x00000001, 0x02c58533, 0x00151573, 0x00000073,
    0x00c5a663, 0x00058503, 0x00c58023], step (single w) = .error .unsupported := by
  decide +kernel

theorem load_x0_still_faults : step (single 0x00002003) = .error .unmapped := by decide +kernel

theorem no_memory : step { pc := 4096, mem := [] } = .error .unmapped := by decide +kernel
theorem no_execute : step (single 0x00700513 4096 false) = .error .permission := by decide +kernel
theorem bad_pc_alignment : step (single 0x00700513 4098) = .error .alignment := by decide +kernel
theorem missing_instruction_byte : readWord [⟨4096, [19,5,112], true, false, true⟩] 4096 true = .error .unmapped := by decide +kernel
theorem malformed_byte : byteAt [⟨0, [256], true, false, false⟩] 0 false = .error .malformed := by decide +kernel
theorem bad_load_alignment : readWord [⟨8192, [0,0,0,0,0], true, true, false⟩] 8193 = .error .alignment := by decide +kernel
theorem bad_store_permission : writeWord [⟨8192, [0,0,0,0], true, false, false⟩] 8192 1 = .error .permission := by decide +kernel
theorem store_crosses_end : writeWord [⟨8192, [0,0,0], true, true, false⟩] 8192 1 = .error .unmapped := by decide +kernel
theorem address_overflow : readWord [⟨4294967292, [0,0,0], true, true, true⟩] 4294967292 = .error .unmapped := by decide +kernel
theorem branch_misaligned : step (single 0x00000163) = .error .alignment := by decide +kernel
theorem untaken_branch_need_not_align : (step (single 0x00001163)).map State.pc = .ok 4100 := by decide +kernel
theorem fuel_is_failure : reach 1 123 (single 0x00000013) = .error .fuel := by decide +kernel
theorem missing_elf : loadElf [] = .error .malformed := by decide +kernel
-- Changing a loaded instruction in the original file breaks image agreement.
theorem image_mismatch : loadElf (Exported.elfBytes.set 116 0) ≠ .ok (Exported.entry, Exported.image) := by decide +kernel
-- Execution really faults after an allowed step into an unmapped next page.
theorem fetch_after_end : (step (single 0x00000013) >>= step) = .error .unmapped := by decide +kernel

def wrongImage : List Region := Exported.image.modify 0 fun r =>
  { r with bytes := r.bytes.set 10 133 }

-- Mutating the ADDI immediate from 7 to 8 must fail the common specification,
-- even though execution still succeeds and the output remains in range.
theorem changed_clamp_rejected :
    Clamp.check wrongImage Exported.entry 0x101c 7 0 = false := by decide +kernel

#print axioms unsupported
#print axioms image_mismatch
#print axioms fetch_after_end
end Negative
