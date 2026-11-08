import Projects.thermostat.I16Digits
import Projects.thermostat.Fields
import Projects.thermostat.UartPlatform
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.I16DigitsWitness
open E5R E5R.Thermostat

def ram (v : BitVec 16) := ramWrite (fun _ => 255#8) 0x80010000#32 (v.signExtend 32) .h

def core : Core :=
  ⟨0x80004e5e#32,(fun r => if r = 1 then 0x80000abc#32 else if r = 2 then 0x80050010#32
    else if r = 10 then 0x80010000#32 else if r = 11 then 0x80030000#32
    else BitVec.ofNat 32 (0x11110000+r.val)),false,false,3,0,0,0,0,0,false⟩

/-- A symbolic satisfiable prestate for every i16, not enumeration of inputs. -/
theorem all_values (v : BitVec 16) :
    ∃ d k r, k ≤ 77 ∧ Trace.Closed UartPlatform.board img k ⟨core,ram v⟩ ⟨d,r⟩ ∧
      I16Ready.Ready core d 0x80050000#32 0x80030000#32 v (I16Ready.offset v.toInt.natAbs) (I16Ready.length v.toInt.natAbs) ∧
      ReadBytes.Span UartPlatform.board img r (0x80050000#32+BitVec.ofNat 32 (I16Ready.offset v.toInt.natAbs)) (ReplyJson.decimal v.toInt.natAbs) := by
  obtain ⟨d,k,r,hk,td,hd,hbytes,_hs,_hf⟩ := I16Digits.contract UartPlatform.board core (ram v) 0x80050000#32 0x80010000#32 0x80030000#32 v
    rfl rfl rfl rfl
    (by unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) (by decide)
    (by unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) (by decide)
    (Fields.half_store_load _ _ v) (WordRegions.before _ _ _ _ (by decide) (by decide)) DigitTable.outside
  exact ⟨d,k,r,hk,Interrupt.close td rfl,hd,hbytes⟩

theorem minimum :
    ∃ d k r, k ≤ 77 ∧ Trace.Closed UartPlatform.board img k ⟨core,ram 0x8000#16⟩ ⟨d,r⟩ ∧
      d.get 11 = 0#32 ∧ ReadBytes.Span UartPlatform.board img r 0x80050003#32 (WireSpec.ascii "32768") := by
  obtain ⟨d,k,r,hk,td,hd,hbytes⟩ := all_values 0x8000#16
  refine ⟨d,k,r,hk,td,hd.x11,?_⟩
  simpa only [show (0x8000#16).toInt.natAbs = 32768 by decide +kernel,
    show I16Ready.offset 32768 = 3 from rfl,show 0x80050000#32+BitVec.ofNat 32 3 = 0x80050003#32 by decide +kernel,show ReplyJson.decimal 32768 = WireSpec.ascii "32768" by decide +kernel] using hbytes
end E5R.Thermostat.I16DigitsWitness
