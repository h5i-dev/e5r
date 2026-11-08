import Projects.thermostat.WriteAsciiChar
import Projects.thermostat.UartPlatform
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.CharWitness
open E5R E5R.Thermostat

def capacity (space : Bool) : Nat := if space then 32 else 0

def ram (space : Bool) (a : Word) : BitVec 8 :=
  if a.toNat = 0x80020002 then 7#8 else if a.toNat = 0x80020003 then 128#8
  else if a.toNat = 0x80020004 then BitVec.ofNat 8 (capacity space)
  else if 0x80020000 ≤ a.toNat ∧ a.toNat < 0x8002000c then 0#8 else 255#8

def core : Core :=
  ⟨0x80002302#32,(fun r => if r = 1 then 0x80000abc#32 else if r = 2 then 0x80050020#32
    else if r = 10 then 0x80020000#32 else if r = 11 then 45#32
    else BitVec.ofNat 32 (0x11110000+r.val)),false,false,3,0,0,0,0,0,false⟩

theorem data (space : Bool) : CharInput.Data UartPlatform.board (ram space) 0x80050000#32 0x80020000#32 0x80070000#32 (capacity space) 0 := by
  cases space
  all_goals refine ⟨?_,by decide,?_,by decide,by decide,by decide,by decide +kernel,by decide +kernel,by decide +kernel,?_,by decide,?_,?_,?_⟩
  all_goals first
    | (unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel)
    | (exact WordRegions.before _ _ _ _ (by decide) (by decide))
    | (exact WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))

/-- Actual '-' char encoding uses its real stack scratch byte, writes one byte
    iff space is available, and restores the full callee ABI in both cases. -/
theorem minus (space : Bool) :
    ∃ d n r, n ≤ 53 ∧ Trace.Closed UartPlatform.board img n ⟨core,ram space⟩ ⟨d,r⟩ ∧
      CursorExit.Returned core d ∧ HighFrame.Frame core d ∧ d.get 10 = (if space then 0#32 else 1#32) ∧
      ramRead r 0x80020008#32 .w = (if space then 1#32 else 0#32) ∧
      r 0x80070000#32 = (if space then 45#8 else 255#8) := by
  obtain ⟨d,n,r,hn,ht,hd,hh⟩ := WriteAsciiChar.contract UartPlatform.board core (ram space) 0x80050000#32 0x80020000#32
    0x80070000#32 (capacity space) 0 45#8 (data space) rfl rfl rfl rfl (by decide)
  refine ⟨d,n,r,hn,Interrupt.close ht rfl,hd.returned,hh,?_,?_,?_⟩
  · cases space <;> exact hd.result
  · change ramRead r (0x80020000#32+8#32) .w = _
    cases space <;> exact hd.position
  · cases space with
    | false => exact hd.refused (by decide) 0x80070000#32 (by decide +kernel)
    | true =>
      change r 0x80070000#32 = 45#8
      have hb := (Bytes.head (hd.written (by decide))).1
      simpa only [BitVec.add_zero] using hb
end E5R.Thermostat.CharWitness
