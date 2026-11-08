import Projects.thermostat.WriteError
import Projects.thermostat.ErrorWriteRange
namespace E5R.Thermostat.WriteErrorRangeWitness
open E5R E5R.Thermostat

theorem execution : ∃ d n r, n≤1343 ∧ Trace.Closed UartPlatform.board img n ⟨ErrorWriteRange.core,ErrorWriteRange.ram⟩ ⟨d,r⟩ ∧
    FormatCursor.Returned ErrorWriteRange.core d ∧ d.pc=0x80000abc#32 ∧
    BodyMemory.At r 0x80060000#32 0x800056a8#32 16#32 (BitVec.ofNat 32 (ReplyJson.errorBody .setpointOutOfRange).length) (ErrorLiterals.status .setpointOutOfRange) ∧
    Bytes.Span UartPlatform.board r 0x80070000#32 (ReplyJson.errorBody .setpointOutOfRange) ∧
    Engine.InvariantAt r 0x80010000#32 ∧ ramRead r 0x80010000#32 .w=0#32 ∧
    r 0x80030024#32=1#8 ∧ r 0x80030028#32=1#8 := by
  have hpre : WriteInput.Pre UartPlatform.board ErrorWriteRange.core ErrorWriteRange.ram (0x8004ff10#32+240#32)
      0x80030000#32 0x80060000#32 0x80020000#32 0x80010000#32 0x80040000#32 0x80040005#32 0x8004004d#32
      ErrorRequestRange.raw ErrorRequestRange.path ErrorRequestRange.body ErrorRequestRange.entries none true Spec.initial := by
    simpa only [show (0x8004ff10#32+240#32)=0x80050000#32 by decide +kernel] using ErrorWriteRange.pre
  obtain ⟨d,n,r,hn,td,hret,hresponse,hbytes,_,hb,hinv,h36,h40,_,_⟩ := WriteError.contract_inv ErrorWriteRange.core ErrorWriteRange.ram
    0x8004ff10#32 0x80030000#32 0x80060000#32 0x80020000#32 0x80010000#32 0x80040000#32 0x80040005#32 0x8004004d#32 0x80070000#32
    ErrorRequestRange.raw ErrorRequestRange.path ErrorRequestRange.body ErrorRequestRange.entries none 1024 true Spec.initial (.setpoint 301#16) .setpointOutOfRange hpre
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
end E5R.Thermostat.WriteErrorRangeWitness
