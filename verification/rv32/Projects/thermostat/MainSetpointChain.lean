import Projects.thermostat.MainRouteLiteralView
import Projects.thermostat.MainStateSetpoint
import Projects.thermostat.MainSetpointSetpoint
import Projects.thermostat.MainSecondMatcherCall
set_option autoImplicit false
set_option maxRecDepth 6000
namespace E5R.Thermostat.MainSetpointChain
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := MainRouteEnvelope.B
abbrev sp := MainRouteEnvelope.sp
abbrev fp := MainRouteEnvelope.fp
abbrev rx := MainRouteEnvelope.rx

theorem first {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat} {close : Bool}
    (h : MainRouterEntry.At c ram input s head amount served close)
    (futures : MainRouterFutures.At ram) (capacity : ramRead ram 0x80fff9fc#32 .w=832#32)
    (route : MainRequestSpans.path input head=WireSpec.ascii "/setpoint") :
    ∃ d, Quiet.Steps B img 158 ⟨c,ram⟩ ⟨d,MainPathStateSave.memory ram c⟩ ∧
      MainRouteEnvelope.At d (MainPathStateSave.memory ram c) input s head amount served close ∧
      d.pc=0x800013d2#32 ∧ d.get 10=0#32 ∧ d.get 11=0#32 ∧ d.sameCsr c := by
  have env := MainRouteLiteralView.entry h futures capacity
  obtain ⟨pathBytes,length,separate⟩ := MainRouteLiteralView.literal_view env _ route
  have pathLength : c.get 13=9#32 := by
    rw [h.pathLength]
    change BitVec.ofNat 32 (MainQuerySpec.pathLength (MainQuerySpec.bytes input) head.target.1 head.target.2)=9#32
    rw [length];rfl
  have stack : Memory.Block B 0x80ffeb50#32 64 := by
    have block := Memory.sub_block h.stable.stack (off := 60240) (m := 64) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60240#32=0x80ffeb50#32 by decide +kernel] using block
  have pattern : ReadBytes.Span B img ram 0x80005b83#32 (WireSpec.ascii "/state") :=
    ReadBytes.of_data B ram _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨d,steps,pc,result,captures,abi,csr⟩ := MainStateSetpoint.contract B c ram _ _ 0x800013d2#32
    (by decide) (by decide +kernel) h.pc h.stable.sp h.ret h.pattern h.patternLength h.path pathLength h.params stack pattern pathBytes separate
  have regs (r : Reg) (member : r∈[2,8,18,19,22]) : d.get r=c.get r := by
    apply abi r
    have subset : ∀ r : Reg, r∈[2,8,18,19,22] → r∈[1,2,3,4,8,9,18,19,20,21,22,23,24,25,26,27] := by decide +kernel
    exact subset r member
  exact ⟨d,steps,MainRouteEnvelope.saved env c regs csr,pc,result,captures,csr⟩

theorem second {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat} {close : Bool}
    (h : MainRouteEnvelope.At c ram input s head amount served close)
    (hp : c.pc=0x800013d2#32) (failed : c.get 10=0#32)
    (route : MainRequestSpans.path input head=WireSpec.ascii "/setpoint") :
    ∃ d n after, n≤250 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      MainRouteEnvelope.At d after input s head amount served close ∧
      d.pc=0x80001422#32 ∧ d.get 10=1#32 ∧ d.get 11=0#32 ∧ d.sameCsr c := by
  have stack : Memory.Block B sp 5232 := by
    have block := Memory.sub_block h.stable.stack (off := 60304) (m := 5232) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  have pathLength : MainRequestBuild.pathLength input head=9#32 := by
    change BitVec.ofNat 32 (MainQuerySpec.pathLength (MainQuerySpec.bytes input) head.target.1 head.target.2)=9#32
    rw [(MainRouteLiteralView.literal_view h _ route).2.1];rfl
  have paramLength : ramRead ram 0x80fff9b4#32 .w=9#32 := h.stored.request.pathLength.trans pathLength
  have futureRouter : ramRead ram 2164259480#32 .w=2164255728#32 := by
    have word := h.futures ⟨3,by decide⟩ ⟨0,by decide⟩
    change ramRead ram (fp+644#32) .w=2164255728#32 at word
    simpa only [show fp+644#32=2164259480#32 by decide +kernel] using word
  have futureRequest : ramRead ram 2164259484#32 .w=0x80fff880#32 := by
    have word := h.futures ⟨3,by decide⟩ ⟨1,by decide⟩
    change ramRead ram (fp+648#32) .w=0x80fff880#32 at word
    simpa only [show fp+648#32=2164259484#32 by decide +kernel] using word
  have pattern : ramRead ram 2164255728#32 .w=2147507081#32 := by
    have word := (h.table ⟨3,by decide⟩).1
    simpa only [show 0x80ffebd8#32+BitVec.ofNat 32 (8*3)=2164255728#32 by decide +kernel] using word
  have patternLength : ramRead ram 2164255732#32 .w=9#32 := by
    have word := (h.table ⟨3,by decide⟩).2.1
    simpa only [show 0x80ffebdc#32+BitVec.ofNat 32 (8*3)=2164255732#32 by decide +kernel] using word
  obtain ⟨a,call,pa,a9,a11,a14,a10,a12,a13,a1,ar,ac⟩ := MainSecondMatcherCall.contract B c ram _ 9#32 h.stable.sp h.stable.fp failed h.stable.one stack futureRouter futureRequest pattern patternLength h.stored.request.path paramLength hp
  let mid := MainSecondMatcherCall.memory ram (rx+BitVec.ofNat 32 head.target.1)
  have regs (r : Reg) (member : r∈[2,8,18,19,22]) : a.get r=c.get r := by
    have ne : ∀ r : Reg, r∈[2,8,18,19,22] → r≠9 ∧ r≠11 ∧ r≠14 ∧ r≠10 ∧ r≠12 ∧ r≠13 ∧ r≠1 := by decide +kernel
    have safe := ne r member
    exact ar r safe.1 safe.2.1 safe.2.2.1 safe.2.2.2.1 safe.2.2.2.2.1 safe.2.2.2.2.2.1 safe.2.2.2.2.2.2
  have live : ViewFrame.Region ram mid sp 3780 := by
    simpa only [BitVec.add_zero] using MainSecondMatcherCall.frame ram (rx+BitVec.ofNat 32 head.target.1) 0 3780 (by decide) (Or.inl (by decide))
  have futureFrames : ∀ r : Fin 5, ViewFrame.Region ram mid (MainRouterFutures.fp+BitVec.ofNat 32 (512+44*r.val)) 20 := by
    intro r
    have apart : 3716+44*r.val+20≤3912 ∨ 3913≤3716+44*r.val := by
      exact Or.inl (by have := r.isLt;omega)
    have region := MainSecondMatcherCall.frame ram (rx+BitVec.ofNat 32 head.target.1) (3716+44*r.val) 20 (by have := r.isLt;omega) apart
    have address : sp+BitVec.ofNat 32 (3716+44*r.val)=MainRouterFutures.fp+BitVec.ofNat 32 (512+44*r.val) := by
      rw [show 3716+44*r.val=3204+(512+44*r.val) by omega,BitVec.ofNat_add,←BitVec.add_assoc,show sp+3204#32=MainRouterFutures.fp by decide +kernel]
    rw [address] at region
    exact region
  have entered := MainRouteEnvelope.preserve h regs ac live futureFrames
  obtain ⟨pathBytes,length,separate⟩ := MainRouteLiteralView.literal_view entered _ route
  have patternBytes : ReadBytes.Span B img mid 2147507081#32 (WireSpec.ascii "/setpoint") :=
    ReadBytes.of_data B mid _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have matcherStack : Memory.Block B 0x80ffeb50#32 64 := by
    have block := Memory.sub_block h.stable.stack (off := 60240) (m := 64) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60240#32=0x80ffeb50#32 by decide +kernel] using block
  obtain ⟨d,matched,pd,result,captures,abi,dc⟩ := MainSetpointSetpoint.contract B a mid _ _ 2147488802#32 (by decide) (by decide +kernel) pa entered.stable.sp a1 a10 a11 a12 a13 a14 matcherStack patternBytes pathBytes separate
  have abiNeeded (r : Reg) (member : r∈[2,8,18,19,22]) : d.get r=a.get r := by
    apply abi r
    have subset : ∀ r : Reg, r∈[2,8,18,19,22] → r∈[1,2,3,4,8,9,18,19,20,21,22,23,24,25,26,27] := by decide +kernel
    exact subset r member
  have env := MainRouteEnvelope.saved entered a abiNeeded dc
  exact ⟨d,250,_,by decide,call.trans matched,env,pd,result,captures,dc.trans ac⟩

/-- Reset predecessor can derive both real matcher outcomes without a routing-result premise. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat} {close : Bool}
    (h : MainRouterEntry.At c ram input s head amount served close) (futures : MainRouterFutures.At ram)
    (route : MainRequestSpans.path input head=WireSpec.ascii "/setpoint")
    (capacity : ramRead ram 0x80fff9fc#32 .w=832#32) :
    ∃ d n after, n≤408 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      MainRouteEnvelope.At d after input s head amount served close ∧
      d.pc=0x80001422#32 ∧ d.get 10=1#32 ∧ d.get 11=0#32 ∧ d.sameCsr c := by
  obtain ⟨a,ta,env,pa,failed,_,csr⟩ := first h futures capacity route
  obtain ⟨d,n,after,bound,tb,ready,pc,result,captures,dc⟩ := second env pa failed route
  exact ⟨d,158+n,after,by omega,ta.trans tb,ready,pc,result,captures,dc.trans csr⟩
end E5R.Thermostat.MainSetpointChain
