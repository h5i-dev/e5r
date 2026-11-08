import Projects.thermostat.AuthLiterals
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.JsonLiterals
open E5R E5R.Thermostat

def prefixBytes := WireSpec.ascii "{\"setpoint_dc\":"

theorem prefix_data : ∀ i : Fin 15,
    BitVec.ofNat 32 (PackedData.dataByte (0x8000574c#32+BitVec.ofNat 32 i.val).toNat) =
      BitVec.ofNat 32 prefixBytes[i.val].toNat := by decide +kernel

theorem prefix_outside : ∀ i : Fin 15, UartPlatform.board.inRam (0x8000574c#32+BitVec.ofNat 32 i.val) 1 = false := by
  unfold UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel

theorem prefix_span (ram : Word → BitVec 8) : ReadBytes.Span UartPlatform.board img ram 0x8000574c#32 prefixBytes := by
  refine ⟨by decide,by decide,?_⟩
  intro i
  have hi : i.val < 15 := i.isLt
  have bounds : 0x800056a8 ≤ (0x8000574c#32+BitVec.ofNat 32 i.val).toNat ∧
      (0x8000574c#32+BitVec.ofNat 32 i.val).toNat < 0x80005f18 := by
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat];omega
  refine .rom (prefix_outside i) ?_
  rw [PackedData.read_byte _ bounds.1 bounds.2]
  exact congrArg some (prefix_data i)
end E5R.Thermostat.JsonLiterals
