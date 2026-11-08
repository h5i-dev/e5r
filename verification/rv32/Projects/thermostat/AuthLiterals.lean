import Projects.thermostat.PackedData
import Projects.thermostat.ReadBytes
import Projects.thermostat.UartPlatform
import Projects.thermostat.WireSpec
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.AuthLiterals
open E5R E5R.Thermostat

theorem key_data : ∀ i : Fin 7,
    BitVec.ofNat 32 (PackedData.dataByte (0x80005b7c#32+BitVec.ofNat 32 i.val).toNat) =
      BitVec.ofNat 32 (WireSpec.ascii "dev-key")[i.val].toNat := by decide +kernel
theorem key_outside : ∀ i : Fin 7, UartPlatform.board.inRam (0x80005b7c#32+BitVec.ofNat 32 i.val) 1 = false := by
  unfold UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
theorem key (ram : Word → BitVec 8) : ReadBytes.Span UartPlatform.board img ram 0x80005b7c#32 (WireSpec.ascii "dev-key") := by
  refine ⟨by decide,by decide,?_⟩
  intro i
  have hi : i.val < 7 := i.isLt
  have bounds : 0x800056a8 ≤ (0x80005b7c#32+BitVec.ofNat 32 i.val).toNat ∧
      (0x80005b7c#32+BitVec.ofNat 32 i.val).toNat < 0x80005f18 := by
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
    omega
  refine .rom (key_outside i) ?_
  rw [PackedData.read_byte _ bounds.1 bounds.2]
  exact congrArg some (key_data i)

theorem bearer_data : ∀ i : Fin 7,
    BitVec.ofNat 32 (PackedData.dataByte (0x80005b75#32+BitVec.ofNat 32 i.val).toNat) =
      BitVec.ofNat 32 (WireSpec.ascii "Bearer ")[i.val].toNat := by decide +kernel
theorem bearer_outside : ∀ i : Fin 7, UartPlatform.board.inRam (0x80005b75#32+BitVec.ofNat 32 i.val) 1 = false := by
  unfold UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
theorem bearer (ram : Word → BitVec 8) : ReadBytes.Span UartPlatform.board img ram 0x80005b75#32 (WireSpec.ascii "Bearer ") := by
  refine ⟨by decide,by decide,?_⟩
  intro i
  have hi : i.val < 7 := i.isLt
  have bounds : 0x800056a8 ≤ (0x80005b75#32+BitVec.ofNat 32 i.val).toNat ∧
      (0x80005b75#32+BitVec.ofNat 32 i.val).toNat < 0x80005f18 := by
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
    omega
  refine .rom (bearer_outside i) ?_
  rw [PackedData.read_byte _ bounds.1 bounds.2]
  exact congrArg some (bearer_data i)

theorem header_data : ∀ i : Fin 13,
    BitVec.ofNat 32 (PackedData.dataByte (0x80005b68#32+BitVec.ofNat 32 i.val).toNat) =
      BitVec.ofNat 32 (WireSpec.ascii "authorization")[i.val].toNat := by decide +kernel
theorem header_outside : ∀ i : Fin 13, UartPlatform.board.inRam (0x80005b68#32+BitVec.ofNat 32 i.val) 1 = false := by
  unfold UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
theorem header (ram : Word → BitVec 8) : ReadBytes.Span UartPlatform.board img ram 0x80005b68#32 (WireSpec.ascii "authorization") := by
  refine ⟨by decide,by decide,?_⟩
  intro i
  have hi : i.val < 13 := i.isLt
  have bounds : 0x800056a8 ≤ (0x80005b68#32+BitVec.ofNat 32 i.val).toNat ∧
      (0x80005b68#32+BitVec.ofNat 32 i.val).toNat < 0x80005f18 := by
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
    omega
  refine .rom (header_outside i) ?_
  rw [PackedData.read_byte _ bounds.1 bounds.2]
  exact congrArg some (header_data i)
end E5R.Thermostat.AuthLiterals
