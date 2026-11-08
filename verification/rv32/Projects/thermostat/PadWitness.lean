import Projects.thermostat.PadPositiveCursor
import Projects.thermostat.PadNegativeCursor
import Projects.thermostat.UartPlatform
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.PadWitness
open E5R E5R.Thermostat

def digits : List (BitVec 8) := [49#8,50#8,51#8]
def capacity (space : Bool) : Nat := if space then 32 else 5

def ram (space : Bool) (a : Word) : BitVec 8 :=
  if a.toNat = 0x80010000 then 49#8 else if a.toNat = 0x80010001 then 50#8 else if a.toNat = 0x80010002 then 51#8
  else if a.toNat = 0x80020002 then 7#8 else if a.toNat = 0x80020003 then 128#8
  else if a.toNat = 0x80020004 then BitVec.ofNat 8 (capacity space) else if a.toNat = 0x80020008 then 3#8
  else if a.toNat = 0x80030002 then 2#8 else if a.toNat = 0x80030003 then 128#8
  else if a.toNat = 0x80030004 then 4#8 else if a.toNat = 0x80030005 then 92#8 else if a.toNat = 0x80030007 then 128#8
  else if (0x80020000 ≤ a.toNat ∧ a.toNat < 0x8002000c) ∨ (0x80030000 ≤ a.toNat ∧ a.toNat < 0x80030010) then 0#8
  else if a.toNat = 0x80070000 then 65#8 else if a.toNat = 0x80070001 then 66#8 else if a.toNat = 0x80070002 then 67#8
  else 255#8

def core (negative : Bool) : Core :=
  ⟨0x80004514#32,(fun r => if r = 1 then 0x80000abc#32 else if r = 2 then (if negative then 0x80050080#32 else 0x80050060#32)
    else if r = 10 then 0x80030000#32 else if r = 11 then (if negative then 0#32 else 1#32)
    else if r = 13 then 0#32 else if r = 14 then 0x80010000#32 else if r = 15 then 3#32
    else BitVec.ofNat 32 (0x11110000+r.val)),false,false,3,0,0,0,0,0,false⟩

theorem source (space : Bool) : ReadBytes.Span UartPlatform.board img (ram space) 0x80010000#32 digits := by
  apply ReadBytes.of_ram
  apply Bytes.of_block
  · unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
  · decide
  · cases space <;> unfold Bytes.At <;> decide +kernel

theorem layout (space negative : Bool) : CursorInput.Layout UartPlatform.board (ram space)
    (if negative then 0x80050060#32 else 0x80050040#32) 0x80020000#32 0x80010000#32 0x80070000#32 (capacity space) 3 digits := by
  cases space <;> cases negative
  all_goals refine ⟨?_,by decide,?_,by decide,by decide,by decide,by decide +kernel,by decide +kernel,by decide +kernel,
    source _,by decide,?_,by decide,?_,?_,?_,?_,?_⟩
  all_goals first
    | (unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel)
    | (exact WordRegions.before _ _ _ _ (by decide) (by decide))
    | (exact WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))

theorem char_data : CharInput.Data UartPlatform.board (ram true) 0x80050000#32 0x80020000#32 0x80070000#32 32 3 := by
  refine ⟨?_,by decide,?_,by decide,by decide,by decide,by decide +kernel,by decide +kernel,by decide +kernel,?_,by decide,?_,?_,?_⟩
  all_goals first
    | (unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel)
    | (exact WordRegions.before _ _ _ _ (by decide) (by decide))
    | (exact WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))

theorem positive (space : Bool) :
    ∃ d n r, n ≤ 144 ∧ Trace.Closed UartPlatform.board img n ⟨core false,ram space⟩ ⟨d,r⟩ ∧
      AppendPost.Post UartPlatform.board (core false) d (ram space) r 0x80050000#32 0x80020000#32 0x80070000#32 96 (capacity space) 3 digits ∧
      d.get 10 = (if space then 0#32 else 1#32) ∧ r 0x80070003#32 = (if space then 49#8 else 255#8) := by
  obtain ⟨d,n,r,hn,ht,hd⟩ := PadPositiveCursor.contract UartPlatform.board (core false) (ram space)
    0x80050000#32 0x80030000#32 0x80020000#32 0x80010000#32 0x80070000#32 (capacity space) 3 digits
    rfl rfl rfl rfl rfl rfl rfl
    (by unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) (by decide)
    (by unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) (by decide)
    (by cases space <;> decide +kernel) (by cases space <;> decide +kernel) (by cases space <;> decide +kernel) (by cases space <;> decide +kernel)
    (WordRegions.before _ _ _ _ (by decide) (by decide)) FormatLiterals.cursor_method_outside
    (layout space false) (WordRegions.before _ _ _ _ (by decide) (by decide)) (WordRegions.before _ _ _ _ (by decide) (by decide))
  refine ⟨d,n,r,hn,Interrupt.close ht rfl,hd,?_,?_⟩
  · cases space <;> exact hd.result
  · cases space with
    | false => exact hd.refused (by decide) 0x80070003#32 (by decide +kernel)
    | true => exact (Bytes.head (hd.written (by decide))).1

theorem negative :
    ∃ d n r, n ≤ 199 ∧ Trace.Closed UartPlatform.board img n ⟨core true,ram true⟩ ⟨d,r⟩ ∧
      AppendPost.Post UartPlatform.board (core true) d (ram true) r 0x80050000#32 0x80020000#32 0x80070000#32 128 32 3 (45#8::digits) ∧
      d.get 10 = 0#32 ∧ r 0x80070003#32 = 45#8 := by
  obtain ⟨d,n,r,hn,ht,hd⟩ := PadNegativeCursor.contract UartPlatform.board (core true) (ram true)
    0x80050000#32 0x80030000#32 0x80020000#32 0x80010000#32 0x80070000#32 32 3 digits
    rfl rfl rfl rfl rfl rfl rfl
    (by unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) (by decide)
    (by unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (WordRegions.before _ _ _ _ (by decide) (by decide)) FormatLiterals.cursor_method_outside
    (layout true true) char_data (WordRegions.before _ _ _ _ (by decide) (by decide)) (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide))) (WordRegions.before _ _ _ _ (by decide) (by decide))
    (by decide) FormatData.cursor_char_method_outside
  refine ⟨d,n,r,hn,Interrupt.close ht rfl,hd,hd.result,(Bytes.head (hd.written (by decide))).1⟩
end E5R.Thermostat.PadWitness
