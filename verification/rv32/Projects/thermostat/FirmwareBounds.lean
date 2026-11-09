import Projects.thermostat.FirmwareStream
import Projects.thermostat.ImageBounds
import Projects.thermostat.CutBounds
import Projects.thermostat.PanicEntries
set_option autoImplicit false
namespace E5R.Thermostat.FirmwareBounds
open E5R E5R.Thermostat
theorem reachable {m evs} (actual : E5R.Reach UartPlatform.board img FirmwareStream.Reset m evs) :
    m.core.pc.getLsbD 0=false ∧ 0x80000000≤m.core.pc.toNat ∧ m.core.pc.toNat<0x800056a8 :=
  ImageBounds.code (FirmwareStream.platform_prefix actual).1
theorem disjoint {c} (cut : CutBounds.Pc c) (panic : PanicEntries.Pc c) : False := by
  unfold CutBounds.Pc at cut
  rcases panic with pc|loop|routine
  · simp only [pc,BitVec.toNat_ofNat,Nat.reduceMod] at cut;omega
  · omega
  · omega

/-- An actual quiet suffix cannot leave any supported nonreturning Rust
    panic routine and reach a UART cut. Faults are excluded independently. -/
theorem no_panic_envelope {m g} (h : ReactiveEnvelope.Envelope FirmwareStream.At m g) : ¬PanicEntries.At m.core := by
  obtain ⟨mask,n,last,quiet,post⟩ := h
  intro panic
  exact disjoint (CutBounds.active post) (PanicEntries.pc_bound (PanicEntries.quiet panic quiet))

theorem no_panic {m evs} (actual : E5R.Reach UartPlatform.board img FirmwareStream.Reset m evs) :
    ¬PanicEntries.At m.core ∧ m.core.pc∉PanicEntries.entries ∧ ¬PanicLoop.At m.core := by
  obtain ⟨safe,reads,g,path,env,trace⟩ := FirmwareStream.platform_prefix actual
  have excluded := no_panic_envelope env
  exact ⟨excluded,(fun entry => excluded (PanicEntries.entry entry)),(fun loop => excluded (Or.inl loop))⟩

end E5R.Thermostat.FirmwareBounds
