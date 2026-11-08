import Projects.thermostat.WriteError
import Projects.thermostat.ErrorWriteRelay
namespace E5R.Thermostat.WriteErrorRelayWitness
open E5R E5R.Thermostat

theorem execution : ∃ d n r, n≤1325 ∧ Trace.Closed UartPlatform.board img n ⟨ErrorWriteRelay.core,ErrorWriteRelay.ram⟩ ⟨d,r⟩ ∧
    FormatCursor.Returned ErrorWriteRelay.core d ∧ d.pc=0x80000abc#32 ∧
    BodyMemory.At r 0x80060000#32 0x800056a8#32 16#32 (BitVec.ofNat 32 (ReplyJson.errorBody .noSuchRelay).length) (ErrorLiterals.status .noSuchRelay) ∧
    Bytes.Span UartPlatform.board r 0x80070000#32 (ReplyJson.errorBody .noSuchRelay) ∧
    Engine.InvariantAt r 0x80010000#32 ∧ ramRead r 0x80010000#32 .w=0#32 ∧
    r 0x80030024#32=1#8 ∧ r 0x80030028#32=1#8 := by
  have hpre : WriteInput.Pre UartPlatform.board ErrorWriteRelay.core ErrorWriteRelay.ram (0x8004ff10#32+240#32)
      0x80030000#32 0x80060000#32 0x80020000#32 0x80010000#32 0x80040000#32 0x80040005#32 0x8004004c#32
      ErrorRequestRelay.raw ErrorRequestRelay.path ErrorRequestRelay.body ErrorRequestRelay.entries (some (WireSpec.ascii "4")) true Spec.initial := by
    simpa only [show (0x8004ff10#32+240#32)=0x80050000#32 by decide +kernel] using ErrorWriteRelay.pre
  obtain ⟨d,n,r,hn,td,hret,hresponse,hbytes,_,hb,hinv,h36,h40,_,_⟩ := WriteError.contract_inv ErrorWriteRelay.core ErrorWriteRelay.ram
    0x8004ff10#32 0x80030000#32 0x80060000#32 0x80020000#32 0x80010000#32 0x80040000#32 0x80040005#32 0x8004004c#32 0x80070000#32
    ErrorRequestRelay.raw ErrorRequestRelay.path ErrorRequestRelay.body ErrorRequestRelay.entries (some (WireSpec.ascii "4")) 1024 true Spec.initial (.relay 4#8 true) .noSuchRelay hpre
    (by decide +kernel) (by decide +kernel) rfl Spec.initial_inv
    (by unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide)
    (by unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) (by decide) (by decide)
    (by unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) (by decide)
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
  exact ⟨d,n,r,hn,Interrupt.close td rfl,hret,by rw [hret.pc];rfl,hresponse,hbytes,hinv,hb,h36,h40⟩
end E5R.Thermostat.WriteErrorRelayWitness
