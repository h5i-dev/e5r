-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.Kernel
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.ReadCallQuiet
import Projects.thermostat.RefusedCallQuiet
import Projects.thermostat.RelayQuiet
import Projects.thermostat.ReportTempQuiet
import Projects.thermostat.SetModeQuiet
import Projects.thermostat.SetpointQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.Kernel
theorem transition_contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command)
    (h : Call.Pre B c ram admin s cmd) :
    ∃ n m, n ≤ 81 ∧ Quiet.Steps B img n ⟨c,ram⟩ m ∧ Call.Post c ram m (Spec.transition admin s cmd) := by
  cases cmd with
  | read =>
    obtain ⟨n,m,hn,hr,hp⟩ := E5R.Thermostat.ReadCall.contract_quiet B c ram admin s h
    exact ⟨n,m,by omega,hr,hp⟩
  | reportTemp dc =>
    obtain ⟨n,m,hn,hr,hp⟩ := E5R.Thermostat.ReportTemp.contract_quiet B c ram admin s dc h
    exact ⟨n,m,by omega,hr,hp⟩
  | setpoint dc =>
    cases admin with
    | false =>
      obtain ⟨n,m,hn,hr,hp⟩ := E5R.Thermostat.RefusedCall.contract_quiet B c ram s (.setpoint dc) ⟨0,by decide⟩ h rfl rfl
      exact ⟨n,m,by omega,hr,hp⟩
    | true =>
      obtain ⟨n,m,hn,hr,hp⟩ := E5R.Thermostat.Setpoint.contract_quiet B c ram s dc h
      exact ⟨n,m,by omega,hr,hp⟩
  | relay idx on =>
    cases admin with
    | false =>
      obtain ⟨n,m,hn,hr,hp⟩ := E5R.Thermostat.RefusedCall.contract_quiet B c ram s (.relay idx on) ⟨1,by decide⟩ h rfl rfl
      exact ⟨n,m,by omega,hr,hp⟩
    | true => exact E5R.Thermostat.Relay.contract_quiet B c ram s idx on h
  | mode mode =>
    cases admin with
    | false =>
      obtain ⟨n,m,hn,hr,hp⟩ := E5R.Thermostat.RefusedCall.contract_quiet B c ram s (.mode mode) ⟨2,by decide⟩ h rfl rfl
      exact ⟨n,m,by omega,hr,hp⟩
    | true =>
      obtain ⟨n,m,hn,hr,hp⟩ := E5R.Thermostat.SetMode.contract_quiet B c ram s mode h
      exact ⟨n,m,by omega,hr,hp⟩

end E5R.Thermostat.Kernel
