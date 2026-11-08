import Projects.thermostat.AlignedSource
import Projects.thermostat.AlignedCopyMemory
import Projects.thermostat.RomSpan
import Projects.thermostat.ReplyJson
import Projects.thermostat.UartPlatform
namespace E5R.Thermostat.ForbiddenCopyData
open E5R E5R.Thermostat

def words : List Word := [0x7265227b#32,0x22726f72#32,0x6f66223a#32,0x64696272#32,0x226e6564#32]

theorem data : ∀ i : Fin words.length,
    BitVec.ofNat 32 (PackedFetch.rd PackedData.dataByte (0x80005be0#32+BitVec.ofNat 32 (4*i.val)).toNat 4) = words[i.val] := by decide +kernel

theorem outside : ∀ i : Fin words.length,
    UartPlatform.board.inRam (0x80005be0#32+BitVec.ofNat 32 (4*i.val)) 4 = false := by
  unfold UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel

theorem source : AlignedSource.Source UartPlatform.board 0x80005be0#32 words := by
  refine ⟨by decide,outside,?_⟩
  intro i
  have hi : i.val<5 := i.isLt
  have bounds : 0x800056a8 ≤ (0x80005be0#32+BitVec.ofNat 32 (4*i.val)).toNat ∧
      (0x80005be0#32+BitVec.ofNat 32 (4*i.val)).toNat+4 ≤ 0x80005f18 := by
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat];omega
  rw [PackedData.read_data _ 4 bounds.1 bounds.2]
  exact congrArg some (data i)

theorem final_outside : UartPlatform.board.inRam 0x80005bf4#32 1 = false := by
  unfold UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel

theorem final_byte (ram : Word → BitVec 8) : ReadBytes.Span UartPlatform.board img ram 0x80005bf4#32 [125#8] := by
  apply ReadBytes.of_data _ _ _ _ (by decide) (by decide +kernel)
  · intro i
    have hi : i.val=0 := by have := i.isLt;change i.val<1 at this;omega
    simp only [hi,BitVec.add_zero];constructor <;> decide +kernel
  · intro i
    have hi : i.val=0 := by have := i.isLt;change i.val<1 at this;omega
    simpa only [hi,BitVec.add_zero] using final_outside
  · decide +kernel

theorem bytes : AlignedCopyLoop.bytes words ++ [125#8] = ReplyJson.errorBody .forbidden := by decide +kernel
end E5R.Thermostat.ForbiddenCopyData
