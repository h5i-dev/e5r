import Projects.thermostat.EncodeModeOff
import Projects.thermostat.EncodeModeHeat
import Projects.thermostat.EncodeModeAuto
import Projects.thermostat.ModeLiterals
import Projects.thermostat.Fields
namespace E5R.Thermostat.EncodeMode
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (m : Spec.Mode)
    (hp : c.pc = 0x80001ec6#32) (h13 : c.get 13 = Fields.modeWord m) :
    ∃ d n, n ≤ 7 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80001ef0#32 ∧
      d.get 11 = BitVec.ofNat 32 (ReplyJson.mode m).length ∧ d.get 12 = ModeLiterals.pointer m ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  cases m with
  | off =>
    obtain ⟨d,td,hp,h11,h12,hr,hc⟩ := EncodeModeOff.contract B c ram h13 hp
    exact ⟨d,5,by decide,td,hp,h11,h12,hr,hc⟩
  | heat =>
    obtain ⟨d,td,hp,h11,h12,hr,hc⟩ := EncodeModeHeat.contract B c ram h13 hp
    exact ⟨d,7,by decide,td,hp,h11,h12,hr,hc⟩
  | auto =>
    obtain ⟨d,td,hp,h11,h12,hr,hc⟩ := EncodeModeAuto.contract B c ram h13 hp
    exact ⟨d,6,by decide,td,hp,h11,h12,hr,hc⟩
end E5R.Thermostat.EncodeMode
