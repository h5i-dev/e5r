import Projects.thermostat.RomSpan
import Projects.thermostat.WireSpec
import Projects.thermostat.UartPlatform
namespace E5R.Thermostat.ResponseLiterals
open E5R E5R.Thermostat

theorem json_data : ∀ i : Fin (WireSpec.ascii "application/json").length,
    BitVec.ofNat 32 (PackedData.dataByte (0x800056a8#32+BitVec.ofNat 32 i.val).toNat) =
      BitVec.ofNat 32 (WireSpec.ascii "application/json")[i.val].toNat := by decide +kernel

theorem json_outside : ∀ i : Fin (WireSpec.ascii "application/json").length,
    UartPlatform.board.inRam (0x800056a8#32+BitVec.ofNat 32 i.val) 1 = false := by
  unfold UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel

theorem json (ram : Word → BitVec 8) : ReadBytes.Span UartPlatform.board img ram 0x800056a8#32 (WireSpec.ascii "application/json") := by
  apply ReadBytes.of_data _ _ _ _ (by decide) (by decide +kernel) _ json_outside json_data
  intro i
  have hi := i.isLt
  change i.val<16 at hi
  simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
  omega
end E5R.Thermostat.ResponseLiterals
