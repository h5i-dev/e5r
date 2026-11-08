import Projects.thermostat.FormatLiterals
namespace E5R.Thermostat.ModeLiterals
open E5R E5R.Thermostat

def pointer : Spec.Mode → Word
  | .off => 0x80005bf5#32 | .heat => 0x80005c00#32 | .auto => 0x80005bf8#32

theorem data (m : Spec.Mode) : ∀ i : Fin (ReplyJson.mode m).length,
    BitVec.ofNat 32 (PackedData.dataByte (pointer m+BitVec.ofNat 32 i.val).toNat) =
      BitVec.ofNat 32 (ReplyJson.mode m)[i.val].toNat := by cases m <;> decide +kernel

theorem outside (m : Spec.Mode) : ∀ i : Fin (ReplyJson.mode m).length,
    UartPlatform.board.inRam (pointer m+BitVec.ofNat 32 i.val) 1 = false := by
  cases m <;> (unfold UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel)

theorem span (m : Spec.Mode) (ram : Word → BitVec 8) :
    ReadBytes.Span UartPlatform.board img ram (pointer m) (ReplyJson.mode m) := by
  refine ⟨by cases m <;> decide,by cases m <;> decide,?_⟩
  intro i
  have bounds : 0x800056a8 ≤ (pointer m+BitVec.ofNat 32 i.val).toNat ∧
      (pointer m+BitVec.ofNat 32 i.val).toNat < 0x80005f18 := by
    have hi := i.isLt
    cases m with
    | off =>
      change i.val < 3 at hi
      change 0x800056a8 ≤ (0x80005bf5#32+BitVec.ofNat 32 i.val).toNat ∧ (0x80005bf5#32+BitVec.ofNat 32 i.val).toNat < 0x80005f18
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat];omega
    | heat =>
      change i.val < 4 at hi
      change 0x800056a8 ≤ (0x80005c00#32+BitVec.ofNat 32 i.val).toNat ∧ (0x80005c00#32+BitVec.ofNat 32 i.val).toNat < 0x80005f18
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat];omega
    | auto =>
      change i.val < 4 at hi
      change 0x800056a8 ≤ (0x80005bf8#32+BitVec.ofNat 32 i.val).toNat ∧ (0x80005bf8#32+BitVec.ofNat 32 i.val).toNat < 0x80005f18
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat];omega
  apply ReadBytes.Byte.rom (outside m i)
  rw [PackedData.read_byte _ bounds.1 bounds.2]
  exact congrArg some (data m i)
end E5R.Thermostat.ModeLiterals
