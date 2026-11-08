import Projects.thermostat.UartWriteAll
set_option maxRecDepth 3000
namespace E5R.Thermostat.UartWriteWitness
open E5R E5R.Thermostat

def bytes : List (BitVec 8) := [79#8,75#8]
def slot0 : UartTxLoop.Slot := ⟨[0#32,1#32,16#32,256#32],288#32,(by
  intro s hs
  simp at hs
  rcases hs with h|h|h|h <;> subst s <;> decide +kernel),by decide +kernel⟩
def slot1 : UartTxLoop.Slot := ⟨[0#32],32#32,(by
  intro s hs
  have he : s=0#32 := List.mem_singleton.mp hs
  subst s;decide +kernel),by decide +kernel⟩
def slots := [slot0,slot1]

def objectByte : Nat → BitVec 8
  | 2 => 3#8 | 3 => 128#8 | 6 => 1#8 | 7 => 128#8 | 8 => 2#8 | _ => 0#8

def ram (a : Word) : BitVec 8 :=
  if 0x80020000≤a.toNat ∧ a.toNat<0x80020029 then objectByte (a.toNat-0x80020000)
  else if a=0x80010000#32 then 79#8 else if a=0x80010001#32 then 75#8 else 255#8

def core : Core := ⟨0x80000786#32,(fun r => if r=1 then 0x80000abc#32 else if r=2 then 0x80050000#32
  else if r=10 then 0x80020000#32 else BitVec.ofNat 32 (0x11110000+r.val)),false,false,3,0,0,0,0,0,false⟩

theorem span : ReadBytes.Span UartPlatform.board img ram 0x80010000#32 bytes := by
  apply ReadBytes.of_ram
  apply Bytes.of_block
  · unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
  · decide
  · change ∀ i : Fin 2, ram (0x80010000#32+BitVec.ofNat 32 i.val)=bytes[i.val]
    decide +kernel

/-- Actual delayed statuses exercise both polling cycles and both bytes,
    with a high status word correctly truncated to its byte-wide device value. -/
theorem execution : ∃ d, Observed.Steps UartPlatform.board img 75 ⟨core,ram⟩
      ⟨d,UartWriteAll.memory ram 0x80020000#32 0x80030000#32 0x80010000#32 bytes⟩
      (UartTxLoop.reads slots) (UartTxLoop.events bytes) ∧ FormatCursor.Returned core d ∧
      d.pc=0x80000abc#32 ∧ Observed.input (UartTxLoop.reads slots)=[] ∧
      Observed.output (UartTxLoop.events bytes)=[79#8,75#8] ∧
      UartWriteAll.memory ram 0x80020000#32 0x80030000#32 0x80010000#32 bytes 0x80020028#32=1#8 := by
  obtain ⟨d,td,hr,hcomplete,_,_,_,_⟩ := UartWriteAll.contract core ram 0x80020000#32 0x80030000#32 0x80010000#32 bytes slots
    rfl rfl (by change Memory.Block UartPlatform.board 0x80020000#32 41;unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) span (by decide)
    (WordRegions.before _ _ _ _ (by decide) (by decide))
  refine ⟨d,?_,hr,by rw [hr.pc];rfl,UartTxLoop.no_input slots,UartTxLoop.output bytes,hcomplete⟩
  have ht : UartWriteAll.time bytes slots=75 := by decide +kernel
  rw [ht] at td;exact td
end E5R.Thermostat.UartWriteWitness
