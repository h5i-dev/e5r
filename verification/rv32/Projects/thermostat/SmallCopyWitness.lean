import Projects.thermostat.SmallCopy
import Projects.thermostat.AuthLiterals
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.SmallCopyWitness
open E5R E5R.Thermostat

def ram (_ : Word) : BitVec 8 := 255#8

def core : Core :=
  ⟨0x80005182#32,(fun r => if r = 1 then 0x80000abc#32 else if r = 2 then 0x80050050#32
    else if r = 10 then 0x80070001#32 else if r = 11 then 0x80005b75#32 else if r = 12 then 7#32
    else BitVec.ofNat 32 (0x11110000+r.val)),false,false,3,0,0,0,0,0,false⟩

/-- Actual memcpy copies ROM bytes into an unaligned RAM destination and returns
    with the same stack/RA; both adjacent bytes remain untouched. -/
theorem copies_bearer :
    ∃ d n r, n ≤ 53 ∧ Trace.Closed UartPlatform.board img n ⟨core,ram⟩ ⟨d,r⟩ ∧
      d.pc = 0x80000abc#32 ∧ d.get 2 = 0x80050050#32 ∧
      Bytes.Span UartPlatform.board r 0x80070001#32 (WireSpec.ascii "Bearer ") ∧
      r 0x80070000#32 = 255#8 ∧ r 0x80070008#32 = 255#8 := by
  have hm : Memory.Block UartPlatform.board 0x80070001#32 (WireSpec.ascii "Bearer ").length := by
    unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
  obtain ⟨d,n,hn,ht,hpc,hsp,_,_,_,hs⟩ := SmallCopy.contract UartPlatform.board core ram 0x80005b75#32 0x80070001#32
    (WireSpec.ascii "Bearer ") rfl rfl rfl rfl (by decide) (AuthLiterals.bearer ram) hm (by decide)
    (WordRegions.before _ _ _ _ (by decide) (by decide))
  refine ⟨d,n,ByteWrite.write ram 0x80070001#32 (WireSpec.ascii "Bearer "),hn,Interrupt.close ht rfl,hpc,hsp,hs,?_,?_⟩
  · exact ByteWrite.frame ram _ _ _ (by decide +kernel)
  · exact ByteWrite.frame ram _ _ _ (by decide +kernel)
end E5R.Thermostat.SmallCopyWitness
