import Projects.thermostat.FirmwarePrefix
import Projects.thermostat.StackFirmwareStream
set_option autoImplicit false
namespace E5R.Thermostat.Firmware
open E5R E5R.Thermostat

/-- Reset-to-loop safety and stream refinement for the unchanged ELF, for
    every finite actual prefix and arbitrary UART choices. The64KiB board is
    a checked RAM-access monitor with identical ROM and UART semantics.
    The original loader/reset hypotheses are the only premises. App/borrow/
    invariant claims apply at actual normalized UART cuts, not between stores.
    SP itself has the separately witnessed startup+8 exception. Progress still
    requires a complete request and suitable finite input/readiness schedule. -/
theorem reset_stream_refines {m reads evs}
    (actual : Observed.Reach UartPlatform.board img FirmwareStream.Reset m reads evs) :
    Observed.Reach StackBoard.board img FirmwareStream.Reset m reads evs ∧
    ¬Escapes StackBoard.board img m ∧
    ¬Escapes UartPlatform.board img m ∧ m.core.mie_=false ∧
    m.core.pc.getLsbD 0=false ∧ 0x80000000≤m.core.pc.toNat ∧ m.core.pc.toNat<0x800056a8 ∧
    ¬PanicEntries.At m.core ∧ m.core.pc∉PanicEntries.entries ∧ ¬PanicLoop.At m.core ∧
    IoBounds.Reads reads ∧ IoBounds.Writes evs ∧
    ∃ g,ProtocolStreamTrace.Trace ProtocolStreamSpec.initial (Observed.input reads) (Observed.output evs) g ∧
      FirmwarePrefix.Boundary m g := by
  obtain ⟨envelope,safe,monitored⟩ := StackFirmwareStream.observed actual
  exact ⟨monitored,safe,FirmwarePrefix.observed actual⟩

/-- Ordinary Reach supplies its actual receive observations existentially;
    neither input bytes nor parsing/authentication outcomes are postulated. -/
theorem reset_stream_refines_platform {m evs}
    (actual : E5R.Reach UartPlatform.board img FirmwareStream.Reset m evs) :
    ∃ reads,Observed.Reach UartPlatform.board img FirmwareStream.Reset m reads evs ∧
      Observed.Reach StackBoard.board img FirmwareStream.Reset m reads evs ∧
      ¬Escapes StackBoard.board img m ∧
      ¬Escapes UartPlatform.board img m ∧ m.core.mie_=false ∧
      m.core.pc.getLsbD 0=false ∧ 0x80000000≤m.core.pc.toNat ∧ m.core.pc.toNat<0x800056a8 ∧
      ¬PanicEntries.At m.core ∧ m.core.pc∉PanicEntries.entries ∧ ¬PanicLoop.At m.core ∧
      IoBounds.Reads reads ∧ IoBounds.Writes evs ∧
      ∃ g,ProtocolStreamTrace.Trace ProtocolStreamSpec.initial (Observed.input reads) (Observed.output evs) g ∧
        FirmwarePrefix.Boundary m g := by
  obtain ⟨reads,path⟩ := Observed.reach_complete actual
  exact ⟨reads,path,reset_stream_refines path⟩
end E5R.Thermostat.Firmware
