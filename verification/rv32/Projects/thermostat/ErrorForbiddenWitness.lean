import Projects.thermostat.ErrorForbidden
import Projects.thermostat.Interrupt
namespace E5R.Thermostat.ErrorForbiddenWitness
open E5R E5R.Thermostat

def ram (x : Word) : BitVec 8 := if x=0x80010000#32 then 2#8 else 255#8
def core : Core := ⟨0x80001e4a#32,(fun r => if r=1 then 0x80000abc#32 else if r=2 then 0x80050020#32
  else if r=10 then 0x80010000#32 else if r=11 then 0x80070000#32 else if r=12 then 1024#32
  else BitVec.ofNat 32 (0x11110000+r.val)),false,false,3,0,0,0,0,0,false⟩

theorem execution : ∃ d n r, n≤81 ∧ Trace.Closed UartPlatform.board img n ⟨core,ram⟩ ⟨d,r⟩ ∧
    FormatCursor.Returned core d ∧ d.pc=0x80000abc#32 ∧ d.get 10=403#32 ∧ d.get 11=21#32 ∧
    Bytes.Span UartPlatform.board r 0x80070000#32 (WireSpec.ascii "{\"error\":\"forbidden\"}") := by
  obtain ⟨d,n,r,hn,td,hr,h10,h11,hs,_⟩ := ErrorForbidden.contract core ram 0x80050000#32 0x80010000#32 0x80070000#32 1024
    rfl rfl rfl rfl rfl (by decide) (by decide)
    (by unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) (by decide)
    (.ram (by unfold UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) (by rfl))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (by unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) (by decide) (by decide)
  exact ⟨d,n,r,hn,Interrupt.close td rfl,hr,by rw [hr.pc];rfl,h10,h11,hs⟩
end E5R.Thermostat.ErrorForbiddenWitness
