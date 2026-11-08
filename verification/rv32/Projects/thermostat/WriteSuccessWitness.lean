import Projects.thermostat.WriteSuccess
import Projects.thermostat.WriteWitness
namespace E5R.Thermostat.WriteSuccessWitness
open E5R E5R.Thermostat

def snapshot : Spec.Snapshot := Spec.settle {Spec.initial with mode := .auto}
def result : Spec.Success := ⟨some snapshot,snapshot⟩

theorem json : ReplyJson.snapshot snapshot = WireSpec.ascii
    "{\"setpoint_dc\":200,\"temp_dc\":200,\"heater\":false,\"relays\":[false,false,false,false],\"mode\":\"auto\"}" := by decide +kernel

/-- The existing fresh Future/raw77-byte POST witness now executes through the
    actual JSON encoder,200 Response, both Future flags and original handler RET. -/
theorem complete_auto :
    ∃ d n r, n ≤ 5091 ∧ Trace.Closed UartPlatform.board img n ⟨WriteWitness.core,WriteWitness.ram⟩ ⟨d,r⟩ ∧
      FormatCursor.Returned WriteWitness.core d ∧ d.pc=0x80000abc#32 ∧
      BodyMemory.At r 0x80060000#32 0x800056a8#32 16#32 (BitVec.ofNat 32 (ReplyJson.snapshot snapshot).length) 200#32 ∧
      Bytes.Span UartPlatform.board r 0x80070000#32
        (WireSpec.ascii "{\"setpoint_dc\":200,\"temp_dc\":200,\"heater\":false,\"relays\":[false,false,false,false],\"mode\":\"auto\"}") ∧
      Engine.InvariantAt r 0x80010000#32 ∧ ramRead r 0x80010000#32 .w=0#32 ∧
      r 0x80030024#32=1#8 ∧ r 0x80030028#32=1#8 := by
  have hpre : WriteInput.Pre UartPlatform.board WriteWitness.core WriteWitness.ram (0x8004ff10#32+240#32)
      0x80030000#32 0x80060000#32 0x80020000#32 0x80010000#32 0x80040000#32 0x80040005#32 0x80040049#32
      RequestWitness.raw RequestWitness.path RequestWitness.body RequestWitness.entries none true Spec.initial := by
    simpa only [show (0x8004ff10#32+240#32)=0x80050000#32 by decide +kernel] using WriteWitness.pre
  obtain ⟨d,n,r,hn,td,hret,hresponse,hbytes,_,hb,hinv,h36,h40,_,_⟩ := WriteSuccess.contract_inv WriteWitness.core WriteWitness.ram
    0x8004ff10#32 0x80030000#32 0x80060000#32 0x80020000#32 0x80010000#32 0x80040000#32 0x80040005#32 0x80040049#32 0x80070000#32
    RequestWitness.raw RequestWitness.path RequestWitness.body RequestWitness.entries none 1024 true Spec.initial (.mode .auto) result hpre
    (by decide +kernel) (by decide +kernel) rfl Spec.initial_inv
    (by unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide)
    (by unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) (by decide)
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
  refine ⟨d,n,r,hn,Interrupt.close td rfl,hret,?_,hresponse,?_,hinv,hb,h36,h40⟩
  · rw [hret.pc];rfl
  · rw [←json];exact hbytes
end E5R.Thermostat.WriteSuccessWitness
