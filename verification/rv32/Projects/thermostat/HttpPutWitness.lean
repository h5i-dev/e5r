import Projects.thermostat.HttpPut
import Projects.thermostat.UartWriteWitness
namespace E5R.Thermostat.HttpPutWitness
open E5R E5R.Thermostat
abbrev B := UartPlatform.board
abbrev ram := UartWriteWitness.ram

def core : Core := ⟨0x80004122#32,(fun r => if r=10 then 0x80020000#32 else if r=11 then 192#32
  else if r=12 then 13#32 else if r=13 then 0x80010000#32 else if r=14 then 2#32 else UartWriteWitness.core.get r),
  false,false,3,0,0,0,0,0,false⟩

theorem execution : ∃ d, Quiet.Steps B img 29 ⟨core,ram⟩
    ⟨d,ByteWrite.write ram 0x8002000d#32 [79#8,75#8]⟩ ∧
    FormatCursor.Returned core d ∧ d.pc=0x80000abc#32 ∧ d.get 10=1#32 ∧ d.get 11=15#32 ∧
    Bytes.Span B (ByteWrite.write ram 0x8002000d#32 [79#8,75#8]) 0x8002000d#32 [79#8,75#8] := by
  have hd : Memory.Block B 0x8002000d#32 2 := by
    unfold Memory.Block B UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
  obtain ⟨d,td,hr,d10,d11,_⟩ := HttpPut.contract B core ram 0x80010000#32 0x80020000#32 192#32 13 [79#8,75#8]
    (by decide) (by decide) rfl rfl rfl rfl rfl rfl
    (fun _ _ => UartWriteWitness.span) (fun _ _ => hd)
    (fun _ _ => WordRegions.before _ _ _ _ (by decide) (by decide))
  have ht : HttpPut.duration (192#32).toNat 13 [79#8,75#8].length=29 := by decide
  have hm : HttpPut.memory ram 0x80020000#32 192#32 13 [79#8,75#8]=ByteWrite.write ram 0x8002000d#32 [79#8,75#8] := by
    rfl
  rw [ht,hm] at td
  refine ⟨d,td,hr,?_,by simpa using d10,?_,ByteWrite.span hd (by decide)⟩
  · rw [hr.pc];rfl
  · exact d11 (by decide)
end E5R.Thermostat.HttpPutWitness
