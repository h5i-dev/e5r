-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.EncodeMode
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.EncodeModeAutoQuiet
import Projects.thermostat.EncodeModeHeatQuiet
import Projects.thermostat.EncodeModeOffQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.EncodeMode
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (m : Spec.Mode)
    (hp : c.pc = 0x80001ec6#32) (h13 : c.get 13 = Fields.modeWord m) :
    ∃ d n, n ≤ 7 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80001ef0#32 ∧
      d.get 11 = BitVec.ofNat 32 (ReplyJson.mode m).length ∧ d.get 12 = ModeLiterals.pointer m ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  cases m with
  | off =>
    obtain ⟨d,td,hp,h11,h12,hr,hc⟩ := E5R.Thermostat.EncodeModeOff.contract_quiet B c ram h13 hp
    exact ⟨d,5,by decide,td,hp,h11,h12,hr,hc⟩
  | heat =>
    obtain ⟨d,td,hp,h11,h12,hr,hc⟩ := E5R.Thermostat.EncodeModeHeat.contract_quiet B c ram h13 hp
    exact ⟨d,7,by decide,td,hp,h11,h12,hr,hc⟩
  | auto =>
    obtain ⟨d,td,hp,h11,h12,hr,hc⟩ := E5R.Thermostat.EncodeModeAuto.contract_quiet B c ram h13 hp
    exact ⟨d,6,by decide,td,hp,h11,h12,hr,hc⟩

end E5R.Thermostat.EncodeMode
