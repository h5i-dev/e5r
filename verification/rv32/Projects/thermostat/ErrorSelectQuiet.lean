-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ErrorSelect
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.ErrorSelectForbiddenQuiet
import Projects.thermostat.ErrorSelectRelayQuiet
import Projects.thermostat.ErrorSelectSetpointQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.ErrorSelect
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (cap : Nat) (e : Spec.Error)
    (hp : c.pc=0x80001e5a#32) (h8 : c.get 8=BitVec.ofNat 32 cap)
    (h12 : c.get 12=BitVec.ofNat 32 (Errors.code e).toNat) (hc : 33≤cap) (hb : cap<2^32) :
    ∃ d n, n≤9 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001e8c#32 ∧
      d.get 11=ErrorLiterals.pointer e ∧ d.get 12=BitVec.ofNat 32 (ReplyJson.errorBody e).length ∧
      d.get 9=ErrorLiterals.status e ∧ d.get 8=BitVec.ofNat 32 (ReplyJson.errorBody e).length ∧
      (∀ r : Reg, r≠11 → r≠12 → r≠9 → r≠8 → d.get r=c.get r) ∧ d.sameCsr c := by
  cases e with
  | setpointOutOfRange =>
    obtain ⟨d,td,hpc,h11,h12,h9,h8,hr,hcsr⟩ := E5R.Thermostat.ErrorSelectSetpoint.contract_quiet B c ram cap h8 h12 hc hb hp
    exact ⟨d,7,by decide,td,hpc,h11,h12,h9,h8,hr,hcsr⟩
  | noSuchRelay =>
    obtain ⟨d,td,hpc,h11,h12,h9,h8,hr,hcsr⟩ := E5R.Thermostat.ErrorSelectRelay.contract_quiet B c ram cap h8 h12 hc hb hp
    exact ⟨d,9,by decide,td,hpc,h11,h12,h9,h8,hr,hcsr⟩
  | forbidden =>
    obtain ⟨d,td,hpc,h11,h12,h9,h8,hr,hcsr⟩ := E5R.Thermostat.ErrorSelectForbidden.contract_quiet B c ram cap h8 h12 hc hb hp
    exact ⟨d,9,by decide,td,hpc,h11,h12,h9,h8,hr,hcsr⟩

end E5R.Thermostat.ErrorSelect
