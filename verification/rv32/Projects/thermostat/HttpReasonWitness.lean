import Projects.thermostat.HttpReason
import Projects.thermostat.UartWriteWitness
namespace E5R.Thermostat.HttpReasonWitness
open E5R E5R.Thermostat
abbrev B := UartPlatform.board
abbrev ram := UartWriteWitness.ram

def core (status : Nat) : Core := ⟨0x80003584#32,(fun r => if r=10 then 0x80020000#32 else if r=11 then 192#32
  else if r=12 then 13#32 else if r=13 then BitVec.ofNat 32 status else UartWriteWitness.core.get r),
  false,false,3,0,0,0,0,0,false⟩

/-- A concrete nonzero saved-register caller and allocated destination satisfy
    the complete real reason-encoder preconditions for every valid status. -/
theorem execution (status : Nat) (hlo : 100≤status) (hhi : status≤599) :
    ∃ d n, n≤178 ∧ Quiet.Steps B img n ⟨core status,ram⟩
      ⟨d,ByteWrite.write ram 0x8002000d#32 (WireSpec.ascii (ResponseHeadSpec.reason status))⟩ ∧
      FormatCursor.Returned (core status) d ∧ d.pc=0x80000abc#32 ∧ d.get 10=1#32 ∧
      d.get 11=BitVec.ofNat 32 (13+(WireSpec.ascii (ResponseHeadSpec.reason status)).length) ∧
      Bytes.Span B (ByteWrite.write ram 0x8002000d#32 (WireSpec.ascii (ResponseHeadSpec.reason status)))
        0x8002000d#32 (WireSpec.ascii (ResponseHeadSpec.reason status)) := by
  obtain ⟨d,n,hn,td,hr,d10,d11,hbytes⟩ := HttpReason.contract (core status) ram 0x80020000#32 status hlo hhi rfl rfl rfl rfl rfl
    (by change Memory.Block UartPlatform.board 0x80020000#32 192;unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel)
  refine ⟨d,n,hn,td,hr,?_,d10,d11,hbytes⟩
  rw [hr.pc]
  change (0x80000abc#32 &&& ~~~1)=0x80000abc#32
  decide +kernel

/-- The 431 phrase traverses its actual 31-byte ROM-copy loop. -/
theorem longest : ∃ d, Quiet.Steps B img 178 ⟨core 431,ram⟩
      ⟨d,ByteWrite.write ram 0x8002000d#32 (WireSpec.ascii "Request Header Fields Too Large")⟩ ∧
      FormatCursor.Returned (core 431) d ∧ d.get 10=1#32 ∧ d.get 11=44#32 := by
  obtain ⟨d,td,hr,d10,d11,_⟩ := HttpReason431Data.contract (core 431) ram 0x80020000#32 rfl rfl rfl rfl rfl
    (by change Memory.Block UartPlatform.board 0x80020000#32 192;unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel)
  exact ⟨d,td,hr,d10,d11⟩
end E5R.Thermostat.HttpReasonWitness
