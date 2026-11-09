import Projects.thermostat.LoopRouteFrames
import Projects.thermostat.MainRouteEnvelope
import Projects.thermostat.MainTempSecondCall
import Projects.thermostat.MainTempThirdCall
import Projects.thermostat.MainSetpointTemp
import Projects.thermostat.MainTempTemp
set_option autoImplicit false
set_option maxRecDepth 6000
namespace E5R.Thermostat.LoopTempChain
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := MainRouteEnvelope.B
abbrev sp := MainRouteEnvelope.sp
abbrev fp := MainRouteEnvelope.fp
abbrev rx := MainRouteEnvelope.rx

theorem next (second : Bool) {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat} {close : Bool}
    (h : MainRouteEnvelope.At c ram input s head amount served close)
    (hp : c.pc=(if second then 0x800013d2#32 else 0x80001422#32)) (failed : c.get 10=0#32)
    (route : MainRequestSpans.path input head=WireSpec.ascii "/temp") :
    ∃ d n after, n≤(if second then 165 else 181) ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      MainRouteEnvelope.At d after input s head amount served close ∧
      d.pc=(if second then 0x80001422#32 else 0x8000146c#32) ∧ d.get 10=(if second then 0#32 else 1#32) ∧ d.get 11=0#32 ∧ d.sameCsr c ∧ ViewFrame.Region ram after sp 3304 ∧ d.get 23=c.get 23 ∧ d.get 26=c.get 26 := by
  have stack : Memory.Block B sp 5232 := by
    have block := Memory.sub_block h.stable.stack (off := 60304) (m := 5232) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  have pathLength : MainRequestBuild.pathLength input head=5#32 := by
    change BitVec.ofNat 32 (MainQuerySpec.pathLength (MainQuerySpec.bytes input) head.target.1 head.target.2)=5#32
    rw [(MainRouteEnvelope.temp_view h route).2.1]
  have paramLength : ramRead ram 0x80fff9b4#32 .w=5#32 := h.stored.request.pathLength.trans pathLength
  cases second
  case false =>
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
    obtain ⟨a,call,pa,a11,a14,a10,a12,a13,a1,ar,ac⟩ := MainTempThirdCall.contract B c ram _ h.stable.sp h.stable.fp failed h.stable.one stack futureRouter futureRequest pattern patternLength h.stored.request.path paramLength hp
    let mid := MainTempThirdCall.memory ram (rx+BitVec.ofNat 32 head.target.1)
    have regs (r : Reg) (member : r∈[2,8,18,19,22]) : a.get r=c.get r := by
      have ne : ∀ r : Reg, r∈[2,8,18,19,22] → r≠11 ∧ r≠14 ∧ r≠10 ∧ r≠12 ∧ r≠13 ∧ r≠1 := by decide +kernel
      have safe := ne r member
      exact ar r safe.1 safe.2.1 safe.2.2.1 safe.2.2.2.1 safe.2.2.2.2.1 safe.2.2.2.2.2
    have live : ViewFrame.Region ram mid sp 3780 := by
      simpa only [BitVec.add_zero] using MainTempThirdCall.frame ram (rx+BitVec.ofNat 32 head.target.1) 0 3780 (by decide) (Or.inl (by decide))
    have futureFrames : ∀ r : Fin 5, ViewFrame.Region ram mid (MainRouterFutures.fp+BitVec.ofNat 32 (512+44*r.val)) 20 := by
      intro r
      have apart : 3716+44*r.val+20≤3868 ∨ 3869≤3716+44*r.val := by
        by_cases before : r.val≤3
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      have region := MainTempThirdCall.frame ram (rx+BitVec.ofNat 32 head.target.1) (3716+44*r.val) 20 (by have := r.isLt;omega) apart
      have address : sp+BitVec.ofNat 32 (3716+44*r.val)=MainRouterFutures.fp+BitVec.ofNat 32 (512+44*r.val) := by
        rw [show 3716+44*r.val=3204+(512+44*r.val) by omega,BitVec.ofNat_add,←BitVec.add_assoc,show sp+3204#32=MainRouterFutures.fp by decide +kernel]
      rw [address] at region
      exact region
    have entered := MainRouteEnvelope.preserve h regs ac live futureFrames
    obtain ⟨pathBytes,length,separate⟩ := MainRouteEnvelope.temp_view entered route
    have patternBytes : ReadBytes.Span B img mid 2147507090#32 (WireSpec.ascii "/temp") :=
      ReadBytes.of_data B mid _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have matcherStack : Memory.Block B 0x80ffeb50#32 64 := by
      have block := Memory.sub_block h.stable.stack (off := 60240) (m := 64) (by decide) (by decide)
      simpa only [show 0x80ff0000#32+60240#32=0x80ffeb50#32 by decide +kernel] using block
    obtain ⟨d,matched,pd,result,captures,abi,dc⟩ := MainTempTemp.contract B a mid _ _ 2147488876#32 (by decide) (by decide +kernel) pa entered.stable.sp a1 a10 a11 a12 a13 a14 matcherStack patternBytes pathBytes separate
    have abiNeeded (r : Reg) (member : r∈[2,8,18,19,22]) : d.get r=a.get r := by
      apply abi r
      have subset : ∀ r : Reg, r∈[2,8,18,19,22] → r∈[1,2,3,4,8,9,18,19,20,21,22,23,24,25,26,27] := by decide +kernel
      exact subset r member
    have env := MainRouteEnvelope.saved entered a abiNeeded dc
    refine ⟨d,181,_,by decide,call.trans matched,env,pd,result,captures,dc.trans ac,?_,?_,?_⟩
    · exact HeadRegionFrame.trans (ViewFrame.shrink live (by decide)) (LoopRouteFrames.saved mid a)
    · apply (abi 23 (by decide)).trans;apply ar;all_goals decide
    · apply (abi 26 (by decide)).trans;apply ar;all_goals decide
  case true =>
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
    obtain ⟨a,call,pa,a9,a11,a14,a10,a12,a13,a1,ar,ac⟩ := MainTempSecondCall.contract B c ram _ h.stable.sp h.stable.fp failed h.stable.one stack futureRouter futureRequest pattern patternLength h.stored.request.path paramLength hp
    let mid := MainTempSecondCall.memory ram (rx+BitVec.ofNat 32 head.target.1)
    have regs (r : Reg) (member : r∈[2,8,18,19,22]) : a.get r=c.get r := by
      have ne : ∀ r : Reg, r∈[2,8,18,19,22] → r≠9 ∧ r≠11 ∧ r≠14 ∧ r≠10 ∧ r≠12 ∧ r≠13 ∧ r≠1 := by decide +kernel
      have safe := ne r member
      exact ar r safe.1 safe.2.1 safe.2.2.1 safe.2.2.2.1 safe.2.2.2.2.1 safe.2.2.2.2.2.1 safe.2.2.2.2.2.2
    have live : ViewFrame.Region ram mid sp 3780 := by
      simpa only [BitVec.add_zero] using MainTempSecondCall.frame ram (rx+BitVec.ofNat 32 head.target.1) 0 3780 (by decide) (Or.inl (by decide))
    have futureFrames : ∀ r : Fin 5, ViewFrame.Region ram mid (MainRouterFutures.fp+BitVec.ofNat 32 (512+44*r.val)) 20 := by
      intro r
      have apart : 3716+44*r.val+20≤3912 ∨ 3913≤3716+44*r.val := by
        exact Or.inl (by have := r.isLt;omega)
      have region := MainTempSecondCall.frame ram (rx+BitVec.ofNat 32 head.target.1) (3716+44*r.val) 20 (by have := r.isLt;omega) apart
      have address : sp+BitVec.ofNat 32 (3716+44*r.val)=MainRouterFutures.fp+BitVec.ofNat 32 (512+44*r.val) := by
        rw [show 3716+44*r.val=3204+(512+44*r.val) by omega,BitVec.ofNat_add,←BitVec.add_assoc,show sp+3204#32=MainRouterFutures.fp by decide +kernel]
      rw [address] at region
      exact region
    have entered := MainRouteEnvelope.preserve h regs ac live futureFrames
    obtain ⟨pathBytes,length,separate⟩ := MainRouteEnvelope.temp_view entered route
    have patternBytes : ReadBytes.Span B img mid 2147507081#32 (WireSpec.ascii "/setpoint") :=
      ReadBytes.of_data B mid _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have matcherStack : Memory.Block B 0x80ffeb50#32 64 := by
      have block := Memory.sub_block h.stable.stack (off := 60240) (m := 64) (by decide) (by decide)
      simpa only [show 0x80ff0000#32+60240#32=0x80ffeb50#32 by decide +kernel] using block
    obtain ⟨d,matched,pd,result,captures,abi,dc⟩ := MainSetpointTemp.contract B a mid _ _ 2147488802#32 (by decide) (by decide +kernel) pa entered.stable.sp a1 a10 a11 a12 a13 a14 matcherStack patternBytes pathBytes separate
    have abiNeeded (r : Reg) (member : r∈[2,8,18,19,22]) : d.get r=a.get r := by
      apply abi r
      have subset : ∀ r : Reg, r∈[2,8,18,19,22] → r∈[1,2,3,4,8,9,18,19,20,21,22,23,24,25,26,27] := by decide +kernel
      exact subset r member
    have env := MainRouteEnvelope.saved entered a abiNeeded dc
    refine ⟨d,165,_,by decide,call.trans matched,env,pd,result,captures,dc.trans ac,?_,?_,?_⟩
    · exact HeadRegionFrame.trans (ViewFrame.shrink live (by decide)) (LoopRouteFrames.saved mid a)
    · apply (abi 23 (by decide)).trans;apply ar;all_goals decide
    · apply (abi 26 (by decide)).trans;apply ar;all_goals decide

end E5R.Thermostat.LoopTempChain
