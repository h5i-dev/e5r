import Projects.thermostat.RomSpan
import Projects.thermostat.ReplyJson
import Projects.thermostat.UartPlatform
namespace E5R.Thermostat.ErrorLiterals
open E5R E5R.Thermostat

def pointer : Spec.Error → Word
  | .setpointOutOfRange => 0x80005ba6#32
  | .noSuchRelay => 0x80005bc7#32
  | .forbidden => 0x80005be0#32

def status : Spec.Error → Word
  | .setpointOutOfRange => 422#32 | .noSuchRelay => 404#32 | .forbidden => 403#32

theorem data (e : Spec.Error) : ∀ i : Fin (ReplyJson.errorBody e).length,
    BitVec.ofNat 32 (PackedData.dataByte (pointer e+BitVec.ofNat 32 i.val).toNat) =
      BitVec.ofNat 32 (ReplyJson.errorBody e)[i.val].toNat := by cases e <;> decide +kernel

theorem outside (e : Spec.Error) : ∀ i : Fin (ReplyJson.errorBody e).length,
    UartPlatform.board.inRam (pointer e+BitVec.ofNat 32 i.val) 1 = false := by
  cases e <;> (unfold UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel)

theorem span (e : Spec.Error) (ram : Word → BitVec 8) : ReadBytes.Span UartPlatform.board img ram (pointer e) (ReplyJson.errorBody e) := by
  apply ReadBytes.of_data _ _ _ _ _ _ _ (outside e) (data e)
  · cases e <;> decide
  · cases e <;> decide +kernel
  · intro i
    have hi := i.isLt
    cases e with
    | setpointOutOfRange =>
      change i.val<33 at hi
      change 0x800056a8≤(0x80005ba6#32+BitVec.ofNat 32 i.val).toNat ∧ (0x80005ba6#32+BitVec.ofNat 32 i.val).toNat<0x80005f18
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat];omega
    | noSuchRelay =>
      change i.val<25 at hi
      change 0x800056a8≤(0x80005bc7#32+BitVec.ofNat 32 i.val).toNat ∧ (0x80005bc7#32+BitVec.ofNat 32 i.val).toNat<0x80005f18
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat];omega
    | forbidden =>
      change i.val<21 at hi
      change 0x800056a8≤(0x80005be0#32+BitVec.ofNat 32 i.val).toNat ∧ (0x80005be0#32+BitVec.ofNat 32 i.val).toNat<0x80005f18
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat];omega
end E5R.Thermostat.ErrorLiterals
