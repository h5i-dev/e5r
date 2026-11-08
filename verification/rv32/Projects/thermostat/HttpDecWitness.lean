import Projects.thermostat.HttpDec
import Projects.thermostat.UartWriteWitness
namespace E5R.Thermostat.HttpDecWitness
open E5R E5R.Thermostat
abbrev B := UartPlatform.board
abbrev ram := UartWriteWitness.ram

def core (n : Nat) : Core := ⟨0x80004180#32,(fun r => if r=2 then 0x80040010#32
  else if r=10 then 0x80020000#32 else if r=11 then 192#32 else if r=12 then 65#32
  else if r=13 then BitVec.ofNat 32 n else UartWriteWitness.core.get r),false,false,3,0,0,0,0,0,false⟩

theorem execution (n : Nat) (hn : n≤832) :
    ∃ d, Quiet.Steps B img (HttpDec.time n) ⟨core n,ram⟩
      ⟨d,HttpDecMemory.memory ram 0x80040000#32 0x80020000#32 65 n⟩ ∧
      FormatCursor.Returned (core n) d ∧ d.pc=0x80000abc#32 ∧ d.get 10=1#32 ∧
      d.get 11=BitVec.ofNat 32 (65+(ReplyJson.decimal n).length) ∧
      Bytes.Span B (HttpDecMemory.memory ram 0x80040000#32 0x80020000#32 65 n) 0x80020041#32 (ReplyJson.decimal n) := by
  obtain ⟨d,td,hr,d10,d11,hbytes,_⟩ := HttpDec.contract B (core n) ram 0x80040000#32 0x80020000#32 65 n hn (by decide)
    rfl rfl rfl rfl rfl rfl
    (by unfold Memory.Block B UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) (by decide)
    (by unfold Memory.Block B UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel)
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
  refine ⟨d,td,hr,?_,d10,d11,hbytes⟩
  rw [hr.pc]
  change (0x80000abc#32 &&& ~~~1)=0x80000abc#32
  decide +kernel

/-- The actual zero-length representation still emits its mandatory digit. -/
theorem zero : ∃ d, Quiet.Steps B img 107 ⟨core 0,ram⟩
    ⟨d,HttpDecMemory.memory ram 0x80040000#32 0x80020000#32 65 0⟩ ∧
    FormatCursor.Returned (core 0) d ∧
    Bytes.Span B (HttpDecMemory.memory ram 0x80040000#32 0x80020000#32 65 0) 0x80020041#32 [48#8] := by
  obtain ⟨d,td,hr,_,_,_,hb⟩ := execution 0 (by decide)
  rw [show HttpDec.time 0=107 by decide +kernel] at td
  rw [show ReplyJson.decimal 0=[48#8] by decide +kernel] at hb
  exact ⟨d,td,hr,hb⟩

theorem two : ∃ d, Quiet.Steps B img 116 ⟨core 99,ram⟩
    ⟨d,HttpDecMemory.memory ram 0x80040000#32 0x80020000#32 65 99⟩ ∧
    FormatCursor.Returned (core 99) d ∧
    Bytes.Span B (HttpDecMemory.memory ram 0x80040000#32 0x80020000#32 65 99) 0x80020041#32 [57#8,57#8] := by
  obtain ⟨d,td,hr,_,_,_,hb⟩ := execution 99 (by decide)
  rw [show HttpDec.time 99=116 by decide +kernel] at td
  rw [show ReplyJson.decimal 99=[57#8,57#8] by decide +kernel] at hb
  exact ⟨d,td,hr,hb⟩

theorem maximum : ∃ d, Quiet.Steps B img 126 ⟨core 832,ram⟩
    ⟨d,HttpDecMemory.memory ram 0x80040000#32 0x80020000#32 65 832⟩ ∧
    FormatCursor.Returned (core 832) d ∧
    Bytes.Span B (HttpDecMemory.memory ram 0x80040000#32 0x80020000#32 65 832) 0x80020041#32 [56#8,51#8,50#8] := by
  obtain ⟨d,td,hr,_,_,_,hb⟩ := execution 832 (by decide)
  rw [show HttpDec.time 832=126 by decide +kernel] at td
  rw [show ReplyJson.decimal 832=[56#8,51#8,50#8] by decide +kernel] at hb
  exact ⟨d,td,hr,hb⟩
end E5R.Thermostat.HttpDecWitness
