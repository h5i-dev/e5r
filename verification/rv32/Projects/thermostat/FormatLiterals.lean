import Projects.thermostat.ReplyJson
import Projects.thermostat.AuthLiterals
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.FormatLiterals
open E5R E5R.Thermostat

def boolPointer (b : Bool) : Word := if b then 0x80005bfc#32 else 0x80005efb#32

theorem bool_data (b : Bool) : ∀ i : Fin (ReplyJson.boolean b).length,
    BitVec.ofNat 32 (PackedData.dataByte (boolPointer b+BitVec.ofNat 32 i.val).toNat) =
      BitVec.ofNat 32 (ReplyJson.boolean b)[i.val].toNat := by cases b <;> decide +kernel

theorem bool_outside (b : Bool) : ∀ i : Fin (ReplyJson.boolean b).length,
    UartPlatform.board.inRam (boolPointer b+BitVec.ofNat 32 i.val) 1 = false := by
  cases b <;> (unfold UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel)

theorem bool_span (b : Bool) (ram : Word → BitVec 8) :
    ReadBytes.Span UartPlatform.board img ram (boolPointer b) (ReplyJson.boolean b) := by
  refine ⟨by cases b <;> decide,by cases b <;> decide,?_⟩
  intro i
  have bounds : 0x800056a8 ≤ (boolPointer b+BitVec.ofNat 32 i.val).toNat ∧
      (boolPointer b+BitVec.ofNat 32 i.val).toNat < 0x80005f18 := by
    have hi := i.isLt
    cases b with
    | false =>
      change i.val < 5 at hi
      change 0x800056a8 ≤ (0x80005efb#32+BitVec.ofNat 32 i.val).toNat ∧ (0x80005efb#32+BitVec.ofNat 32 i.val).toNat < 0x80005f18
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat];omega
    | true =>
      change i.val < 4 at hi
      change 0x800056a8 ≤ (0x80005bfc#32+BitVec.ofNat 32 i.val).toNat ∧ (0x80005bfc#32+BitVec.ofNat 32 i.val).toNat < 0x80005f18
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat];omega
  refine .rom (bool_outside b i) ?_
  rw [PackedData.read_byte _ bounds.1 bounds.2]
  exact congrArg some (bool_data b i)

theorem cursor_method_word : romRead? img 0x80005c10 4 false = some 0x800022a0#32 := by
  rw [PackedData.read_data 0x80005c10 4 (by decide) (by decide)]
  decide +kernel

theorem cursor_method_outside : UartPlatform.board.inRam 0x80005c10#32 4 = false := by
  unfold UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
end E5R.Thermostat.FormatLiterals
