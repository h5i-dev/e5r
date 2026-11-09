import Projects.thermostat.FirmwareBounds
import Projects.thermostat.IoBounds
import Projects.thermostat.CommittedCut
import Projects.thermostat.StackScope
set_option autoImplicit false
namespace E5R.Thermostat.FirmwarePrefix
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

/-- A finite quiet normalization to an actual reusable UART cut. The cut's
    committed state is in real RAM. No assertion is made about individual
    stores within this suffix, and no future input/readiness is needed. -/
def Boundary (m : Machine) (g : ProtocolStreamSpec.State) : Prop :=
  ∃ n cut,Quiet.Steps B img n m cut ∧ FirmwareStream.At cut g ∧
    AppState.At cut.ram (CommittedCut.snapshot g) ∧ Spec.Inv (CommittedCut.snapshot g) ∧
    ramRead cut.ram 0x80ffebbc#32 .w=0#32 ∧ StackScope.InStack cut.core

theorem boundary {m g} (env : ReactiveEnvelope.Envelope FirmwareStream.At m g) : Boundary m g := by
  obtain ⟨mask,n,cut,quiet,post⟩ := env
  obtain ⟨app,inv,borrow⟩ := CommittedCut.active post
  exact ⟨n,cut,quiet,post,app,inv,borrow,StackScope.active post⟩

/-- The current combined prefix result. All actual observations are included;
    the remaining stronger obligation is a bound on intermediate stack use,
    with the explicitly witnessed startup SP exception. This theorem is not
    named reset_stream_refines until that obligation is discharged. -/
theorem observed {m reads evs} (actual : Observed.Reach B img FirmwareStream.Reset m reads evs) :
    ¬Escapes B img m ∧ m.core.mie_=false ∧
    m.core.pc.getLsbD 0=false ∧ 0x80000000≤m.core.pc.toNat ∧ m.core.pc.toNat<0x800056a8 ∧
    ¬PanicEntries.At m.core ∧ m.core.pc∉PanicEntries.entries ∧ ¬PanicLoop.At m.core ∧
    IoBounds.Reads reads ∧ IoBounds.Writes evs ∧
    ∃ g,ProtocolStreamTrace.Trace ProtocolStreamSpec.initial (Observed.input reads) (Observed.output evs) g ∧ Boundary m g := by
  obtain ⟨g,env,trace,safe⟩ := FirmwareStream.observed_prefix actual
  have code := FirmwareBounds.reachable (Observed.reach_erase actual)
  have panic := FirmwareBounds.no_panic (Observed.reach_erase actual)
  have io := IoBounds.observed actual
  exact ⟨safe,env.1,code.1,code.2.1,code.2.2,panic.1,panic.2.1,panic.2.2,io.1,io.2,g,trace,boundary env⟩

/-- Erasing the instrumentation recovers actual RBR reads from Reach instead
    of assuming request bytes or a selected parser/route/handler outcome. -/
theorem platform {m evs} (actual : E5R.Reach B img FirmwareStream.Reset m evs) :
    ∃ reads,Observed.Reach B img FirmwareStream.Reset m reads evs ∧
      ¬Escapes B img m ∧ m.core.mie_=false ∧
      m.core.pc.getLsbD 0=false ∧ 0x80000000≤m.core.pc.toNat ∧ m.core.pc.toNat<0x800056a8 ∧
      ¬PanicEntries.At m.core ∧ m.core.pc∉PanicEntries.entries ∧ ¬PanicLoop.At m.core ∧
      IoBounds.Reads reads ∧ IoBounds.Writes evs ∧
      ∃ g,ProtocolStreamTrace.Trace ProtocolStreamSpec.initial (Observed.input reads) (Observed.output evs) g ∧ Boundary m g := by
  obtain ⟨reads,path⟩ := Observed.reach_complete actual
  exact ⟨reads,path,observed path⟩
end E5R.Thermostat.FirmwarePrefix
