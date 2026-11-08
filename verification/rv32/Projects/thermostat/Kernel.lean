import Projects.thermostat.Relay
import Projects.thermostat.ReadCall
import Projects.thermostat.ReportTemp
import Projects.thermostat.RefusedCall
namespace E5R.Thermostat.Kernel
open E5R E5R.Thermostat

/-- All five command variants and both actors, with the complete typed input
    domains. The concrete ELF returns the independently specified outcome. -/
theorem transition_contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command)
    (h : Call.Pre B c ram admin s cmd) :
    ∃ n m, n ≤ 81 ∧ DetSteps B img n ⟨c,ram⟩ m ∧ Call.Post c ram m (Spec.transition admin s cmd) := by
  cases cmd with
  | read =>
    obtain ⟨n,m,hn,hr,hp⟩ := ReadCall.contract B c ram admin s h
    exact ⟨n,m,by omega,hr,hp⟩
  | reportTemp dc =>
    obtain ⟨n,m,hn,hr,hp⟩ := ReportTemp.contract B c ram admin s dc h
    exact ⟨n,m,by omega,hr,hp⟩
  | setpoint dc =>
    cases admin with
    | false =>
      obtain ⟨n,m,hn,hr,hp⟩ := RefusedCall.contract B c ram s (.setpoint dc) ⟨0,by decide⟩ h rfl rfl
      exact ⟨n,m,by omega,hr,hp⟩
    | true =>
      obtain ⟨n,m,hn,hr,hp⟩ := Setpoint.contract B c ram s dc h
      exact ⟨n,m,by omega,hr,hp⟩
  | relay idx on =>
    cases admin with
    | false =>
      obtain ⟨n,m,hn,hr,hp⟩ := RefusedCall.contract B c ram s (.relay idx on) ⟨1,by decide⟩ h rfl rfl
      exact ⟨n,m,by omega,hr,hp⟩
    | true => exact Relay.contract B c ram s idx on h
  | mode mode =>
    cases admin with
    | false =>
      obtain ⟨n,m,hn,hr,hp⟩ := RefusedCall.contract B c ram s (.mode mode) ⟨2,by decide⟩ h rfl rfl
      exact ⟨n,m,by omega,hr,hp⟩
    | true =>
      obtain ⟨n,m,hn,hr,hp⟩ := SetMode.contract B c ram s mode h
      exact ⟨n,m,by omega,hr,hp⟩

/-- Instruction-level refinement plus preservation of the source invariant.
    The commit is the specified state operation; Apply.source_contract proves
    its separate concrete ELF implementation. -/
theorem transition_preserves_inv (B : Board) (c : Core) (ram : Word → BitVec 8)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command)
    (h : Call.Pre B c ram admin s cmd) (hi : Spec.Inv s) :
    (∃ n m, n ≤ 81 ∧ DetSteps B img n ⟨c,ram⟩ m ∧ Call.Post c ram m (Spec.transition admin s cmd)) ∧
      Spec.Inv (Spec.commit s (Spec.transition admin s cmd)) := by
  exact ⟨transition_contract B c ram admin s cmd h,Spec.commit_inv admin s cmd hi⟩
end E5R.Thermostat.Kernel
