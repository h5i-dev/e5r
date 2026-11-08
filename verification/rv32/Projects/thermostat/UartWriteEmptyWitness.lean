import Projects.thermostat.UartWriteWitness
namespace E5R.Thermostat.UartWriteEmptyWitness
open E5R E5R.Thermostat

def ram (a : Word) : BitVec 8 := if a=0x80020008#32 then 0#8 else UartWriteWitness.ram a

theorem empty_span : ReadBytes.Span UartPlatform.board img ram 0x80010000#32 [] :=
  ⟨by decide,by decide,fun i => Fin.elim0 i⟩

/-- Empty write_all completes without status reads or UART writes, with no
    readiness premise and the same nonzero caller-save fixture. -/
theorem execution : ∃ d, Observed.Steps UartPlatform.board img 14 ⟨UartWriteWitness.core,ram⟩
      ⟨d,UartWriteAll.memory ram 0x80020000#32 0x80030000#32 0x80010000#32 []⟩ [] [] ∧
      FormatCursor.Returned UartWriteWitness.core d ∧ d.pc=0x80000abc#32 ∧
      UartWriteAll.memory ram 0x80020000#32 0x80030000#32 0x80010000#32 [] 0x80020028#32=1#8 := by
  obtain ⟨d,td,hr,hcomplete,_,_,_,_⟩ := UartWriteAll.contract UartWriteWitness.core ram 0x80020000#32 0x80030000#32 0x80010000#32 [] []
    rfl rfl (by change Memory.Block UartPlatform.board 0x80020000#32 41;unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) empty_span (by decide)
    (fun i => Fin.elim0 i)
  exact ⟨d,td,hr,by rw [hr.pc];rfl,hcomplete⟩
end E5R.Thermostat.UartWriteEmptyWitness
