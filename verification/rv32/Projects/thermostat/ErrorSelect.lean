import Projects.thermostat.ErrorSelectSetpoint
import Projects.thermostat.ErrorSelectRelay
import Projects.thermostat.ErrorSelectForbidden
import Projects.thermostat.ErrorLiterals
import Projects.thermostat.Errors
namespace E5R.Thermostat.ErrorSelect
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (cap : Nat) (e : Spec.Error)
    (hp : c.pc=0x80001e5a#32) (h8 : c.get 8=BitVec.ofNat 32 cap)
    (h12 : c.get 12=BitVec.ofNat 32 (Errors.code e).toNat) (hc : 33≤cap) (hb : cap<2^32) :
    ∃ d n, n≤9 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001e8c#32 ∧
      d.get 11=ErrorLiterals.pointer e ∧ d.get 12=BitVec.ofNat 32 (ReplyJson.errorBody e).length ∧
      d.get 9=ErrorLiterals.status e ∧ d.get 8=BitVec.ofNat 32 (ReplyJson.errorBody e).length ∧
      (∀ r : Reg, r≠11 → r≠12 → r≠9 → r≠8 → d.get r=c.get r) ∧ d.sameCsr c := by
  cases e with
  | setpointOutOfRange =>
    obtain ⟨d,td,hpc,h11,h12,h9,h8,hr,hcsr⟩ := ErrorSelectSetpoint.contract B c ram cap h8 h12 hc hb hp
    exact ⟨d,7,by decide,td,hpc,h11,h12,h9,h8,hr,hcsr⟩
  | noSuchRelay =>
    obtain ⟨d,td,hpc,h11,h12,h9,h8,hr,hcsr⟩ := ErrorSelectRelay.contract B c ram cap h8 h12 hc hb hp
    exact ⟨d,9,by decide,td,hpc,h11,h12,h9,h8,hr,hcsr⟩
  | forbidden =>
    obtain ⟨d,td,hpc,h11,h12,h9,h8,hr,hcsr⟩ := ErrorSelectForbidden.contract B c ram cap h8 h12 hc hb hp
    exact ⟨d,9,by decide,td,hpc,h11,h12,h9,h8,hr,hcsr⟩
end E5R.Thermostat.ErrorSelect
