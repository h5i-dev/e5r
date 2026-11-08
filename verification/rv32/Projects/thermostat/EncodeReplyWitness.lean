import Projects.thermostat.EncodeReply
import Projects.thermostat.JsonCapacity
import Projects.thermostat.Interrupt
set_option maxRecDepth 3000
namespace E5R.Thermostat.EncodeReplyWitness
open E5R E5R.Thermostat

def ram (s : Spec.Snapshot) (x : Word) : BitVec 8 :=
  if h : 0x80ff0000 ≤ x.toNat ∧ x.toNat < 0x80ff000a then
    Encoding.snapshotByte s ⟨x.toNat-0x80ff0000,by omega⟩ else 255#8

def core : Core :=
  ⟨0x80001eb8#32,(fun r => if r=1 then 0x80000abc#32 else if r=2 then 0x80fe0140#32
    else if r=10 then 0x80ff0000#32 else if r=11 then 0x80ff1000#32 else if r=12 then 1024#32
    else BitVec.ofNat 32 (0x11110000+r.val)),false,false,3,0,0,0,0,0,false⟩

theorem snapshot (s : Spec.Snapshot) : Encoding.SnapshotAt (ram s) 0x80ff0000#32 s := by
  intro i
  have hi := i.isLt
  have he : (0x80ff0000#32+BitVec.ofNat 32 i.val).toNat = 0x80ff0000+i.val := by
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat];omega
  unfold ram
  simp only [he]
  rw [dite_eq_left (by omega)]
  apply congrArg (Encoding.snapshotByte s)
  apply Fin.ext
  change (0x80ff0000+i.val-0x80ff0000) = i.val
  omega

/-- Satisfiable real RAM and nonzero saved registers for every typed snapshot,
    including both i16 extrema and every relay/heater/mode combination. -/
theorem all_snapshots (s : Spec.Snapshot) :
    ∃ d n r, n ≤ 3893 ∧ Trace.Closed UartPlatform.board img n ⟨core,ram s⟩ ⟨d,r⟩ ∧
      FormatCursor.Returned core d ∧ d.get 10 = 1#32 ∧ d.get 11 = BitVec.ofNat 32 (ReplyJson.snapshot s).length ∧
      Bytes.Span UartPlatform.board r 0x80ff1000#32 (ReplyJson.snapshot s) ∧ Encoding.SnapshotAt r 0x80ff0000#32 s := by
  have hfit : (ReplyJson.snapshot s).length ≤ 1024 := by have := JsonCapacity.snapshot_length s;omega
  obtain ⟨d,n,r,hn,td,hd,h10,h11,hout,hs,_⟩ := EncodeReply.contract core (ram s) 0x80fe0000#32 0x80ff0000#32 0x80ff1000#32 1024 s
    rfl rfl rfl rfl rfl
    (by unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) (by decide)
    (by unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) (by decide) (snapshot s) (by decide)
    (by unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) (by decide)
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.before _ _ _ _ (by decide) (by decide)) hfit
  exact ⟨d,n,r,hn,Interrupt.close td rfl,hd,h10,h11,hout,hs⟩

def extreme : Spec.Snapshot := {setpoint := 0x8000#16, temp := 0x7fff#16, heater := false, relays := fun _ => true, mode := .auto}

theorem extreme_json : ReplyJson.snapshot extreme = WireSpec.ascii
    "{\"setpoint_dc\":-32768,\"temp_dc\":32767,\"heater\":false,\"relays\":[true,true,true,true],\"mode\":\"auto\"}" := by decide +kernel

theorem extreme_execution :
    ∃ d n r, n ≤ 3893 ∧ Trace.Closed UartPlatform.board img n ⟨core,ram extreme⟩ ⟨d,r⟩ ∧
      d.pc = 0x80000abc#32 ∧ d.get 10 = 1#32 ∧ Bytes.Span UartPlatform.board r 0x80ff1000#32
        (WireSpec.ascii "{\"setpoint_dc\":-32768,\"temp_dc\":32767,\"heater\":false,\"relays\":[true,true,true,true],\"mode\":\"auto\"}") := by
  obtain ⟨d,n,r,hn,td,hd,h10,_,hs,_⟩ := all_snapshots extreme
  refine ⟨d,n,r,hn,td,?_,h10,?_⟩
  · rw [hd.pc];rfl
  · rw [←extreme_json];exact hs
end E5R.Thermostat.EncodeReplyWitness
