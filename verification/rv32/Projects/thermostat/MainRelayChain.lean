import Projects.thermostat.MainRelayCaptured
import Projects.thermostat.MainStateRelay
import Projects.thermostat.MainSetpointRelay
import Projects.thermostat.MainTempRelay
import Projects.thermostat.MainModeRelay
import Projects.thermostat.MainSecondMatcherCall
import Projects.thermostat.MainThirdMatcherCall
import Projects.thermostat.MainFourthMatcherCall
import Projects.thermostat.MainRelayFifthCall
set_option autoImplicit false
set_option maxRecDepth 6000
namespace E5R.Thermostat.MainRelayChain
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := MainRouteEnvelope.B
abbrev sp := MainRouteEnvelope.sp
abbrev fp := MainRouteEnvelope.fp
abbrev rx := MainRouteEnvelope.rx

theorem first {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat} {close : Bool}
    (h : MainRouterEntry.At c ram input s head amount served close)
    (futures : MainRouterFutures.At ram) (capacity : ramRead ram 0x80fff9fc#32 .w=832#32)
    (param : List (BitVec 8)) (nonempty : param≠[])
    (route : MainRequestSpans.path input head=MainRelayCaptured.path param) :
    ∃ d, Quiet.Steps B img 156 ⟨c,ram⟩ ⟨d,MainPathStateSave.memory ram c⟩ ∧
      MainRouteEnvelope.At d (MainPathStateSave.memory ram c) input s head amount served close ∧
      d.pc=0x800013d2#32 ∧ d.get 10=0#32 ∧ d.get 11=0#32 ∧ d.get 24=c.get 24 ∧ d.sameCsr c := by
  have env := MainRouteLiteralView.entry h futures capacity
  obtain ⟨pathBytes,length,lower,separate⟩ := MainRelayCaptured.path_view env param route nonempty
  have pathLength : c.get 13=MainRelayCaptured.size param := h.pathLength.trans length
  have stack : Memory.Block B 0x80ffeb50#32 64 := by
    have block := Memory.sub_block h.stable.stack (off := 60240) (m := 64) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60240#32=0x80ffeb50#32 by decide +kernel] using block
  have pattern : ReadBytes.Span B img ram 0x80005b83#32 (WireSpec.ascii "/state") :=
    ReadBytes.of_data B ram _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨d,steps,pc,result,captures,abi,csr⟩ := MainStateRelay.contract B c ram _ _ 0x800013d2#32 param (MainRelayCaptured.size param) lower
    (by decide) (by decide +kernel) h.pc h.stable.sp h.ret h.pattern h.patternLength h.path pathLength h.params stack pattern pathBytes separate
  have regs (r : Reg) (member : r∈[2,8,18,19,22]) : d.get r=c.get r := by
    apply abi r
    have subset : ∀ r : Reg, r∈[2,8,18,19,22] → r∈[1,2,3,4,8,9,18,19,20,21,22,23,24,25,26,27] := by decide +kernel
    exact subset r member
  exact ⟨d,steps,MainRouteEnvelope.saved env c regs csr,pc,result,captures,abi 24 (by decide),csr⟩

theorem step1 {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat} {close : Bool}
    (h : MainRouteEnvelope.At c ram input s head amount served close)
    (hp : c.pc=0x800013d2#32) (failed : c.get 10=0#32) (param : List (BitVec 8))
    (nonempty : param≠[]) (route : MainRequestSpans.path input head=MainRelayCaptured.path param) :
    ∃ d n after, n≤172 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      MainRouteEnvelope.At d after input s head amount served close ∧
      d.pc=0x80001422#32 ∧ d.get 10=0#32 ∧ d.get 11=0#32 ∧ d.get 24=c.get 24 ∧ d.sameCsr c := by
  have stack : Memory.Block B sp 5232 := by
    have block := Memory.sub_block h.stable.stack (off := 60304) (m := 5232) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  have pathLength : MainRequestBuild.pathLength input head=MainRelayCaptured.size param :=
    (MainRelayCaptured.path_view h param route nonempty).2.1
  have paramLength : ramRead ram 0x80fff9b4#32 .w=MainRelayCaptured.size param := h.stored.request.pathLength.trans pathLength
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
  obtain ⟨a,call,pa,a9,a11,a14,a10,a12,a13,a1,ar,ac⟩ := MainSecondMatcherCall.contract B c ram _ (MainRelayCaptured.size param) h.stable.sp h.stable.fp failed h.stable.one stack futureRouter futureRequest pattern patternLength h.stored.request.path paramLength hp
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
  obtain ⟨pathBytes,length,lower,separate⟩ := MainRelayCaptured.path_view entered param route nonempty
  have patternBytes : ReadBytes.Span B img mid 2147507081#32 (WireSpec.ascii "/setpoint") :=
    ReadBytes.of_data B mid _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have matcherStack : Memory.Block B 0x80ffeb50#32 64 := by
    have block := Memory.sub_block h.stable.stack (off := 60240) (m := 64) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60240#32=0x80ffeb50#32 by decide +kernel] using block
  obtain ⟨d,matched,pd,result,captures,abi,dc⟩ := MainSetpointRelay.contract B a mid _ _ 2147488802#32 param (MainRelayCaptured.size param) lower (by decide) (by decide +kernel) pa entered.stable.sp a1 a10 a11 a12 a13 a14 matcherStack patternBytes pathBytes separate
  have abiNeeded (r : Reg) (member : r∈[2,8,18,19,22]) : d.get r=a.get r := by
    apply abi r
    have subset : ∀ r : Reg, r∈[2,8,18,19,22] → r∈[1,2,3,4,8,9,18,19,20,21,22,23,24,25,26,27] := by decide +kernel
    exact subset r member
  have env := MainRouteEnvelope.saved entered a abiNeeded dc
  exact ⟨d,172,_,by decide,call.trans matched,env,pd,result,captures,(abi 24 (by decide)).trans (ar 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)),dc.trans ac⟩


theorem step2 {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat} {close : Bool}
    (h : MainRouteEnvelope.At c ram input s head amount served close)
    (hp : c.pc=0x80001422#32) (failed : c.get 10=0#32) (param : List (BitVec 8))
    (nonempty : param≠[]) (route : MainRequestSpans.path input head=MainRelayCaptured.path param) :
    ∃ d n after, n≤151 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      MainRouteEnvelope.At d after input s head amount served close ∧
      d.pc=0x8000146c#32 ∧ d.get 10=0#32 ∧ d.get 11=0#32 ∧ d.get 24=c.get 24 ∧ d.sameCsr c := by
  have stack : Memory.Block B sp 5232 := by
    have block := Memory.sub_block h.stable.stack (off := 60304) (m := 5232) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  have pathLength : MainRequestBuild.pathLength input head=MainRelayCaptured.size param :=
    (MainRelayCaptured.path_view h param route nonempty).2.1
  have paramLength : ramRead ram 0x80fff9b4#32 .w=MainRelayCaptured.size param := h.stored.request.pathLength.trans pathLength
  have futureRouter : ramRead ram 2164259436#32 .w=2164255720#32 := by
    have word := h.futures ⟨2,by decide⟩ ⟨0,by decide⟩
    change ramRead ram (fp+600#32) .w=2164255720#32 at word
    simpa only [show fp+600#32=2164259436#32 by decide +kernel] using word
  have futureRequest : ramRead ram 2164259440#32 .w=0x80fff880#32 := by
    have word := h.futures ⟨2,by decide⟩ ⟨1,by decide⟩
    change ramRead ram (fp+604#32) .w=0x80fff880#32 at word
    simpa only [show fp+604#32=2164259440#32 by decide +kernel] using word
  have pattern : ramRead ram 2164255720#32 .w=2147507090#32 := by
    have word := (h.table ⟨2,by decide⟩).1
    simpa only [show 0x80ffebd8#32+BitVec.ofNat 32 (8*2)=2164255720#32 by decide +kernel] using word
  have patternLength : ramRead ram 2164255724#32 .w=5#32 := by
    have word := (h.table ⟨2,by decide⟩).2.1
    simpa only [show 0x80ffebdc#32+BitVec.ofNat 32 (8*2)=2164255724#32 by decide +kernel] using word
  obtain ⟨a,call,pa,a11,a14,a10,a12,a13,a1,ar,ac⟩ := MainThirdMatcherCall.contract B c ram _ (MainRelayCaptured.size param) h.stable.sp h.stable.fp failed h.stable.one stack futureRouter futureRequest pattern patternLength h.stored.request.path paramLength hp
  let mid := MainThirdMatcherCall.memory ram (rx+BitVec.ofNat 32 head.target.1)
  have regs (r : Reg) (member : r∈[2,8,18,19,22]) : a.get r=c.get r := by
    have ne : ∀ r : Reg, r∈[2,8,18,19,22] → r≠11 ∧ r≠14 ∧ r≠10 ∧ r≠12 ∧ r≠13 ∧ r≠1 := by decide +kernel
    have safe := ne r member
    exact ar r safe.1 safe.2.1 safe.2.2.1 safe.2.2.2.1 safe.2.2.2.2.1 safe.2.2.2.2.2
  have live : ViewFrame.Region ram mid sp 3780 := by
    simpa only [BitVec.add_zero] using MainThirdMatcherCall.frame ram (rx+BitVec.ofNat 32 head.target.1) 0 3780 (by decide) (Or.inl (by decide))
  have futureFrames : ∀ r : Fin 5, ViewFrame.Region ram mid (MainRouterFutures.fp+BitVec.ofNat 32 (512+44*r.val)) 20 := by
    intro r
    have apart : 3716+44*r.val+20≤3868 ∨ 3869≤3716+44*r.val := by
      by_cases before : r.val≤3
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    have region := MainThirdMatcherCall.frame ram (rx+BitVec.ofNat 32 head.target.1) (3716+44*r.val) 20 (by have := r.isLt;omega) apart
    have address : sp+BitVec.ofNat 32 (3716+44*r.val)=MainRouterFutures.fp+BitVec.ofNat 32 (512+44*r.val) := by
      rw [show 3716+44*r.val=3204+(512+44*r.val) by omega,BitVec.ofNat_add,←BitVec.add_assoc,show sp+3204#32=MainRouterFutures.fp by decide +kernel]
    rw [address] at region
    exact region
  have entered := MainRouteEnvelope.preserve h regs ac live futureFrames
  obtain ⟨pathBytes,length,lower,separate⟩ := MainRelayCaptured.path_view entered param route nonempty
  have patternBytes : ReadBytes.Span B img mid 2147507090#32 (WireSpec.ascii "/temp") :=
    ReadBytes.of_data B mid _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have matcherStack : Memory.Block B 0x80ffeb50#32 64 := by
    have block := Memory.sub_block h.stable.stack (off := 60240) (m := 64) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60240#32=0x80ffeb50#32 by decide +kernel] using block
  obtain ⟨d,matched,pd,result,captures,abi,dc⟩ := MainTempRelay.contract B a mid _ _ 2147488876#32 param (MainRelayCaptured.size param) lower (by decide) (by decide +kernel) pa entered.stable.sp a1 a10 a11 a12 a13 a14 matcherStack patternBytes pathBytes separate
  have abiNeeded (r : Reg) (member : r∈[2,8,18,19,22]) : d.get r=a.get r := by
    apply abi r
    have subset : ∀ r : Reg, r∈[2,8,18,19,22] → r∈[1,2,3,4,8,9,18,19,20,21,22,23,24,25,26,27] := by decide +kernel
    exact subset r member
  have env := MainRouteEnvelope.saved entered a abiNeeded dc
  exact ⟨d,151,_,by decide,call.trans matched,env,pd,result,captures,(abi 24 (by decide)).trans (ar 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)),dc.trans ac⟩

theorem step3 {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat} {close : Bool}
    (h : MainRouteEnvelope.At c ram input s head amount served close)
    (hp : c.pc=0x8000146c#32) (failed : c.get 10=0#32) (param : List (BitVec 8))
    (nonempty : param≠[]) (route : MainRequestSpans.path input head=MainRelayCaptured.path param) :
    ∃ d n after, n≤151 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      MainRouteEnvelope.At d after input s head amount served close ∧
      d.pc=0x800014b6#32 ∧ d.get 10=0#32 ∧ d.get 11=0#32 ∧ d.get 24=c.get 24 ∧ d.sameCsr c := by
  have stack : Memory.Block B sp 5232 := by
    have block := Memory.sub_block h.stable.stack (off := 60304) (m := 5232) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  have pathLength : MainRequestBuild.pathLength input head=MainRelayCaptured.size param :=
    (MainRelayCaptured.path_view h param route nonempty).2.1
  have paramLength : ramRead ram 0x80fff9b4#32 .w=MainRelayCaptured.size param := h.stored.request.pathLength.trans pathLength
  have futureRouter : ramRead ram 2164259392#32 .w=2164255712#32 := by
    have word := h.futures ⟨1,by decide⟩ ⟨0,by decide⟩
    change ramRead ram (fp+556#32) .w=2164255712#32 at word
    simpa only [show fp+556#32=2164259392#32 by decide +kernel] using word
  have futureRequest : ramRead ram 2164259396#32 .w=0x80fff880#32 := by
    have word := h.futures ⟨1,by decide⟩ ⟨1,by decide⟩
    change ramRead ram (fp+560#32) .w=0x80fff880#32 at word
    simpa only [show fp+560#32=2164259396#32 by decide +kernel] using word
  have pattern : ramRead ram 2164255712#32 .w=2147507095#32 := by
    have word := (h.table ⟨1,by decide⟩).1
    simpa only [show 0x80ffebd8#32+BitVec.ofNat 32 (8*1)=2164255712#32 by decide +kernel] using word
  have patternLength : ramRead ram 2164255716#32 .w=5#32 := by
    have word := (h.table ⟨1,by decide⟩).2.1
    simpa only [show 0x80ffebdc#32+BitVec.ofNat 32 (8*1)=2164255716#32 by decide +kernel] using word
  obtain ⟨a,call,pa,a11,a14,a10,a12,a13,a1,ar,ac⟩ := MainFourthMatcherCall.contract B c ram _ (MainRelayCaptured.size param) h.stable.sp h.stable.fp failed h.stable.one stack futureRouter futureRequest pattern patternLength h.stored.request.path paramLength hp
  let mid := MainFourthMatcherCall.memory ram (rx+BitVec.ofNat 32 head.target.1)
  have regs (r : Reg) (member : r∈[2,8,18,19,22]) : a.get r=c.get r := by
    have ne : ∀ r : Reg, r∈[2,8,18,19,22] → r≠11 ∧ r≠14 ∧ r≠10 ∧ r≠12 ∧ r≠13 ∧ r≠1 := by decide +kernel
    have safe := ne r member
    exact ar r safe.1 safe.2.1 safe.2.2.1 safe.2.2.2.1 safe.2.2.2.2.1 safe.2.2.2.2.2
  have live : ViewFrame.Region ram mid sp 3780 := by
    simpa only [BitVec.add_zero] using MainFourthMatcherCall.frame ram (rx+BitVec.ofNat 32 head.target.1) 0 3780 (by decide) (Or.inl (by decide))
  have futureFrames : ∀ r : Fin 5, ViewFrame.Region ram mid (MainRouterFutures.fp+BitVec.ofNat 32 (512+44*r.val)) 20 := by
    intro r
    have apart : 3716+44*r.val+20≤3824 ∨ 3825≤3716+44*r.val := by
      by_cases before : r.val≤2
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    have region := MainFourthMatcherCall.frame ram (rx+BitVec.ofNat 32 head.target.1) (3716+44*r.val) 20 (by have := r.isLt;omega) apart
    have address : sp+BitVec.ofNat 32 (3716+44*r.val)=MainRouterFutures.fp+BitVec.ofNat 32 (512+44*r.val) := by
      rw [show 3716+44*r.val=3204+(512+44*r.val) by omega,BitVec.ofNat_add,←BitVec.add_assoc,show sp+3204#32=MainRouterFutures.fp by decide +kernel]
    rw [address] at region
    exact region
  have entered := MainRouteEnvelope.preserve h regs ac live futureFrames
  obtain ⟨pathBytes,length,lower,separate⟩ := MainRelayCaptured.path_view entered param route nonempty
  have patternBytes : ReadBytes.Span B img mid 2147507095#32 (WireSpec.ascii "/mode") :=
    ReadBytes.of_data B mid _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have matcherStack : Memory.Block B 0x80ffeb50#32 64 := by
    have block := Memory.sub_block h.stable.stack (off := 60240) (m := 64) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60240#32=0x80ffeb50#32 by decide +kernel] using block
  obtain ⟨d,matched,pd,result,captures,abi,dc⟩ := MainModeRelay.contract B a mid _ _ 2147488950#32 param (MainRelayCaptured.size param) lower (by decide) (by decide +kernel) pa entered.stable.sp a1 a10 a11 a12 a13 a14 matcherStack patternBytes pathBytes separate
  have abiNeeded (r : Reg) (member : r∈[2,8,18,19,22]) : d.get r=a.get r := by
    apply abi r
    have subset : ∀ r : Reg, r∈[2,8,18,19,22] → r∈[1,2,3,4,8,9,18,19,20,21,22,23,24,25,26,27] := by decide +kernel
    exact subset r member
  have env := MainRouteEnvelope.saved entered a abiNeeded dc
  exact ⟨d,151,_,by decide,call.trans matched,env,pd,result,captures,(abi 24 (by decide)).trans (ar 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)),dc.trans ac⟩


theorem enter {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat} {close : Bool}
    (h : MainRouteEnvelope.At c ram input s head amount served close)
    (hp : c.pc=0x800014b6#32) (failed : c.get 10=0#32) (param : List (BitVec 8))
    (nonempty : param≠[]) (noSlash : ∀ b∈param, b≠47#8)
    (route : MainRequestSpans.path input head=MainRelayCaptured.path param) (pointer : c.get 24=0x80fffa2c#32) :
    ∃ origin before d after n, n≤251+5*param.length ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      MainRelayCaptured.At origin before d after input s head amount served close param := by
  have stack : Memory.Block B sp 5232 := by
    have block := Memory.sub_block h.stable.stack (off := 60304) (m := 5232) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  have pathLength : MainRequestBuild.pathLength input head=MainRelayCaptured.size param :=
    (MainRelayCaptured.path_view h param route nonempty).2.1
  have paramLength : ramRead ram 0x80fff9b4#32 .w=MainRelayCaptured.size param := h.stored.request.pathLength.trans pathLength
  have futureRouter : ramRead ram 2164259348#32 .w=2164255704#32 := by
    have word := h.futures ⟨0,by decide⟩ ⟨0,by decide⟩
    change ramRead ram (fp+512#32) .w=2164255704#32 at word
    simpa only [show fp+512#32=2164259348#32 by decide +kernel] using word
  have futureRequest : ramRead ram 2164259352#32 .w=0x80fff880#32 := by
    have word := h.futures ⟨0,by decide⟩ ⟨1,by decide⟩
    change ramRead ram (fp+516#32) .w=0x80fff880#32 at word
    simpa only [show fp+516#32=2164259352#32 by decide +kernel] using word
  have pattern : ramRead ram 2164255704#32 .w=2147507100#32 := by
    have word := (h.table ⟨0,by decide⟩).1
    simpa only [show 0x80ffebd8#32+BitVec.ofNat 32 (8*0)=2164255704#32 by decide +kernel] using word
  have patternLength : ramRead ram 2164255708#32 .w=10#32 := by
    have word := (h.table ⟨0,by decide⟩).2.1
    simpa only [show 0x80ffebdc#32+BitVec.ofNat 32 (8*0)=2164255708#32 by decide +kernel] using word
  obtain ⟨a,call,pa,a11,a14,a10,a12,a13,a1,ar,ac⟩ := MainRelayFifthCall.contract B c ram _ (MainRelayCaptured.size param) h.stable.sp h.stable.fp failed h.stable.one stack futureRouter futureRequest pattern patternLength h.stored.request.path paramLength hp
  let mid := MainRelayFifthCall.memory ram (rx+BitVec.ofNat 32 head.target.1) (MainRelayCaptured.size param)
  have regs (r : Reg) (member : r∈[2,8,18,19,22]) : a.get r=c.get r := by
    have ne : ∀ r : Reg, r∈[2,8,18,19,22] → r≠11 ∧ r≠14 ∧ r≠10 ∧ r≠12 ∧ r≠13 ∧ r≠1 := by decide +kernel
    have safe := ne r member
    exact ar r safe.1 safe.2.1 safe.2.2.1 safe.2.2.2.1 safe.2.2.2.2.1 safe.2.2.2.2.2
  have live : ViewFrame.Region ram mid sp 3780 := by
    simpa only [BitVec.add_zero] using MainRelayFifthCall.frame ram (rx+BitVec.ofNat 32 head.target.1) (MainRelayCaptured.size param) 0 3780 (by decide) (Or.inl (by decide))
  have futureFrames : ∀ r : Fin 5, ViewFrame.Region ram mid (MainRouterFutures.fp+BitVec.ofNat 32 (512+44*r.val)) 20 := by
    intro r
    have apart : 3716+44*r.val+20≤3780 ∨ 3781≤3716+44*r.val := by
      by_cases before : r.val≤1
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    have region := MainRelayFifthCall.frame ram (rx+BitVec.ofNat 32 head.target.1) (MainRelayCaptured.size param) (3716+44*r.val) 20 (by have := r.isLt;omega) apart
    have address : sp+BitVec.ofNat 32 (3716+44*r.val)=MainRouterFutures.fp+BitVec.ofNat 32 (512+44*r.val) := by
      rw [show 3716+44*r.val=3204+(512+44*r.val) by omega,BitVec.ofNat_add,←BitVec.add_assoc,show sp+3204#32=MainRouterFutures.fp by decide +kernel]
    rw [address] at region
    exact region
  have entered := MainRouteEnvelope.preserve h regs ac live futureFrames
  obtain ⟨pathBytes,length,lower,separate⟩ := MainRelayCaptured.path_view entered param route nonempty
  have patternBytes : ReadBytes.Span B img mid 2147507100#32 (WireSpec.ascii "/relay/{i}") :=
    ReadBytes.of_data B mid _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have matcherStack : Memory.Block B 0x80ffeb50#32 64 := by
    have block := Memory.sub_block h.stable.stack (off := 60240) (m := 64) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60240#32=0x80ffeb50#32 by decide +kernel] using block
  have paramsBlock : Memory.Block B MainRelayCaptured.params 8 := by
    have block := Memory.sub_block h.stable.stack (off := 63952) (m := 8) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+63952#32=MainRelayCaptured.params by decide +kernel] using block
  obtain ⟨d,matched,pd,result,captures,abi,dc⟩ := MainRelayMatch.contract B a mid _ _ 0x80001856#32 param
    (by decide) (by decide +kernel) pa entered.stable.sp a1 a10 a11 a12 a13 a14 matcherStack patternBytes pathBytes nonempty noSlash paramsBlock (by decide)
    separate (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
  have saved (r : Reg) (member : r∈[2,8,18,19,22,24]) : d.get r=a.get r := by
    apply abi r
    have subset : ∀ r : Reg, r∈[2,8,18,19,22,24] → r∈[1,2,3,4,8,9,18,19,20,21,22,23,24,25,26,27] := by decide +kernel
    exact subset r member
  have pointerAfter : d.get 24=0x80fffa2c#32 :=
    (abi 24 (by decide)).trans ((ar 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans pointer)
  exact ⟨a,mid,d,_,11+(240+5*param.length),by omega,call.trans matched,
    ⟨entered,route,nonempty,noSlash,rfl,pd,result,captures,saved,pointerAfter,dc⟩⟩

/-- All five real route attempts derive the first capture and actual relay
    caller state. The origin/before indices refer to the real fifth call. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat} {close : Bool}
    (h : MainRouterEntry.At c ram input s head amount served close) (futures : MainRouterFutures.At ram)
    (param : List (BitVec 8)) (nonempty : param≠[]) (noSlash : ∀ b∈param, b≠47#8)
    (route : MainRequestSpans.path input head=MainRelayCaptured.path param)
    (capacity : ramRead ram 0x80fff9fc#32 .w=832#32) :
    ∃ origin before d after n, n≤881+5*param.length ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      MainRelayCaptured.At origin before d after input s head amount served close param := by
  obtain ⟨a,ta,ea,pa,fa,_,ra,ac⟩ := first h futures capacity param nonempty route
  obtain ⟨b,nb,rb,bb,tb,eb,pb,fb,_,r24b,bc⟩ := step1 ea pa fa param nonempty route
  obtain ⟨z,nz,rz,bz,tz,ez,pz,fz,_,r24z,zc⟩ := step2 eb pb fb param nonempty route
  obtain ⟨e,ne,re,be,te,ee,pe,fe,_,r24e,ec⟩ := step3 ez pz fz param nonempty route
  have initial : c.get 24=0x80fffa2c#32 := by
    simpa only [show MainRouterEntry.sp+3740#32=0x80fffa2c#32 by decide +kernel] using h.firstSlot
  have pointer : e.get 24=0x80fffa2c#32 := r24e.trans (r24z.trans (r24b.trans (ra.trans initial)))
  obtain ⟨origin,before,d,after,nd,bd,td,ready⟩ := enter ee pe fe param nonempty noSlash route pointer
  exact ⟨origin,before,d,after,156+nb+nz+ne+nd,by omega,(((ta.trans tb).trans tz).trans te).trans td,ready⟩
end E5R.Thermostat.MainRelayChain
