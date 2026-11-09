import Projects.thermostat.RuntimeSecondCandidate
import Projects.thermostat.StackBoard
import Projects.thermostat.StackRuntimeApiWriteCaller
set_option autoImplicit false
set_option maxRecDepth 6000
namespace E5R.Thermostat.StackRuntimeSecondCandidate
open E5R E5R.Thermostat HttpRequestSpec RuntimeSecondCandidate
abbrev B := StackBoard.board
theorem call {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close) (pc : c.pc=0x800013fe#32) :
    ∃ d, Quiet.Steps B img 10 ⟨c,ram⟩ ⟨d,RouteSecondCore.memory ram (rx+BitVec.ofNat 32 head.target.1)⟩ ∧
      RuntimeLiteralInput.At d (RouteSecondCore.memory ram (rx+BitVec.ofNat 32 head.target.1)) input s head amount rawUsed served lowValue close
        (RouteLiteralInfo.pointer .setpoint) (BitVec.ofNat 32 (RouteLiteralInfo.text .setpoint).length) 0x80001422#32 ∧
      d.get 9=c.get 9 ∧ d.sameCsr c ∧ ViewFrame.Region ram (RouteSecondCore.memory ram (rx+BitVec.ofNat 32 head.target.1)) sp 3304 := by
  have stack : Memory.Block B sp 5232 := by
    have block := Memory.sub_block StackBoard.available (off := 60304) (m := 5232) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  have futureRouter : ramRead ram 0x80fffa98#32 .w=0x80ffebf0#32 := h.futures ⟨3,by decide⟩ ⟨0,by decide⟩
  have futureRequest : ramRead ram 0x80fffa9c#32 .w=0x80fff880#32 := h.futures ⟨3,by decide⟩ ⟨1,by decide⟩
  have pointer : ramRead ram 0x80ffebf0#32 .w=0x80005b89#32 := by
    simpa only [show 0x80ffebd8#32+BitVec.ofNat 32 (8*3)=0x80ffebf0#32 by decide +kernel] using (h.table ⟨3,by decide⟩).1
  have length : ramRead ram 0x80ffebf4#32 .w=9#32 := by
    simpa only [show 0x80ffebdc#32+BitVec.ofNat 32 (8*3)=0x80ffebf4#32 by decide +kernel] using (h.table ⟨3,by decide⟩).2.1
  obtain ⟨d,trace,pd,d9,d11,d14,d10,d12,d13,d1,dr,dc⟩ := RouteSecondCore.contract B c ram (rx+BitVec.ofNat 32 head.target.1)
    (MainRequestBuild.pathLength input head) h.stable.sp h.stable.fp h.stable.one stack futureRouter futureRequest pointer length
    h.stored.request.path h.stored.request.pathLength pc
  let after := RouteSecondCore.memory ram (rx+BitVec.ofNat 32 head.target.1)
  have keep (r : Reg) (member : r∈[2,8,18,19,22,23,24,25,26,27]) : d.get r=c.get r := by
    have safe : ∀ r : Reg,r∈[2,8,18,19,22,23,24,25,26,27] → r≠9 ∧ r≠11 ∧ r≠14 ∧ r≠10 ∧ r≠12 ∧ r≠13 ∧ r≠1 := by decide
    obtain ⟨n9,n11,n14,n10,n12,n13,n1⟩ := safe r member
    exact dr r n9 n11 n14 n10 n12 n13 n1
  have frame (off size : Nat) (bound : off+size≤3912) : ViewFrame.Region ram after (sp+BitVec.ofNat 32 off) size :=
    RouteSecondCore.frame ram _ off size (by omega) (Or.inl bound)
  have live : RuntimeRouteEnvelope.At d after input s head amount rawUsed served lowValue close := by
    apply RuntimeRouteEnvelope.preserve h keep dc
    · simpa only [BitVec.add_zero] using frame 0 3780 (by decide)
    · intro route
      have region := frame (3716+44*route.val) 20 (by have := route.isLt;omega)
      have address : sp+BitVec.ofNat 32 (3716+44*route.val)=MainRouterFutures.fp+BitVec.ofNat 32 (512+44*route.val) := by
        rw [show 3716+44*route.val=3204+(512+44*route.val) by omega,BitVec.ofNat_add,←BitVec.add_assoc,
          show sp+3204#32=MainRouterFutures.fp by decide +kernel]
      rw [address] at region;exact region
  exact ⟨d,trace,⟨live,pd,d1,d10,d11,d12,d13,d14⟩,d9,dc,by simpa only [BitVec.add_zero] using frame 0 3304 (by decide)⟩

/-- The real first-pattern miss sets404-candidate flag3, then makes the
    actual second matcher call with every Request/future premise retained. -/
theorem missing {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close)
    (pc : c.pc=0x800013d2#32) (result : c.get 10=0#32) :
    ∃ d, Quiet.Steps B img 12 ⟨c,ram⟩ ⟨d,RouteSecondCore.memory ram (rx+BitVec.ofNat 32 head.target.1)⟩ ∧
      RuntimeLiteralInput.At d (RouteSecondCore.memory ram (rx+BitVec.ofNat 32 head.target.1)) input s head amount rawUsed served lowValue close
        (RouteLiteralInfo.pointer .setpoint) (BitVec.ofNat 32 (RouteLiteralInfo.text .setpoint).length) 0x80001422#32 ∧
      d.get 9=3#32 ∧ d.sameCsr c ∧ ViewFrame.Region ram (RouteSecondCore.memory ram (rx+BitVec.ofNat 32 head.target.1)) sp 3304 := by
  have tested : taken .ne (c.get 10) (c.get 22)=true := by rw [result,h.stable.one];decide
  obtain ⟨a,ta,pa,ar,ac⟩ := QuietBranch.contract B img c ram 0x800013d2#32 4#32 42#32 .ne 10 22 true pc (by decide) (by decide) rt2147488722 tested
  have ap : a.pc=0x800013fc#32 := by simpa only [ite_true,show 0x800013d2#32+42#32=0x800013fc#32 by decide +kernel] using pa
  let b := a.wr 9 3#32 0x800013fe#32
  have tb : Quiet.Step B img ⟨a,ram⟩ ⟨b,ram⟩ := by
    refine Quiet.step_of (by rw [ap];decide) (by rw [ap];exact tc2147488764) fun o => ?_
    change Observed.interp B img o (exec a _ _) ram 0 [] []=⟨.ok b ram [],[]⟩
    rw [exec_opimm,Core.get_zero,ap];rfl
  have regs (r : Reg) (member : r∈[2,8,18,19,22,23,24,25,26,27]) : b.get r=c.get r := by
    have separate : ∀ r : Reg,r∈[2,8,18,19,22,23,24,25,26,27] → r≠9 := by decide
    exact (Core.wr_get_ne _ _ _ _ _ (separate r member)).trans (ar r)
  have live : RuntimeRouteEnvelope.At b ram input s head amount rawUsed served lowValue close :=
    RuntimeRouteEnvelope.preserve h regs ac (fun _ => rfl) (fun _ _ => rfl)
  obtain ⟨d,td,entry,d9,dc,frame⟩ := call live rfl
  have value : b.get 9=3#32 := Core.wr_get_self _ _ _ _ (by decide)
  exact ⟨d,(ta.trans (.single tb)).trans td,entry,d9.trans value,dc.trans ac,frame⟩

/-- Wrong first-route methods execute the real method guards, set405-candidate
    flag2 and enter the same second pattern call. Method facts are pure bytes. -/
theorem wrong_method {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close)
    (pc : c.pc=0x800013d2#32) (result : c.get 10=1#32)
    (wrong : MainMethodSpec.decode (MainMethodBytes.token input head.method.2)≠.get ∧
      MainMethodSpec.decode (MainMethodBytes.token input head.method.2)≠.head) :
    ∃ d, Quiet.Steps B img 22 ⟨c,ram⟩ ⟨d,RouteSecondCore.memory ram (rx+BitVec.ofNat 32 head.target.1)⟩ ∧
      RuntimeLiteralInput.At d (RouteSecondCore.memory ram (rx+BitVec.ofNat 32 head.target.1)) input s head amount rawUsed served lowValue close
        (RouteLiteralInfo.pointer .setpoint) (BitVec.ofNat 32 (RouteLiteralInfo.text .setpoint).length) 0x80001422#32 ∧
      d.get 9=2#32 ∧ d.sameCsr c ∧ ViewFrame.Region ram (RouteSecondCore.memory ram (rx+BitVec.ofNat 32 head.target.1)) sp 3304 := by
  have notGet : BitVec.ofNat 8 (MainMethodSpec.tag (MainMethodSpec.decode (MainMethodBytes.token input head.method.2)))≠0#8 := by
    cases decoded : MainMethodSpec.decode (MainMethodBytes.token input head.method.2) with
    | get => exact False.elim (wrong.1 decoded)
    | head | post | put | patch | delete | other => decide
  have notHead : BitVec.ofNat 8 (MainMethodSpec.tag (MainMethodSpec.decode (MainMethodBytes.token input head.method.2)))≠1#8 := by
    cases decoded : MainMethodSpec.decode (MainMethodBytes.token input head.method.2) with
    | head => exact False.elim (wrong.2 decoded)
    | get | post | put | patch | delete | other => decide
  have stack : Memory.Block B sp 5232 := by
    have block := Memory.sub_block StackBoard.available (off := 60304) (m := 5232) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  have getRoute : ram 0x80ffec00#32=0#8 := by
    simpa only [show 0x80ffec00#32+BitVec.ofNat 32 (4*0)=0x80ffec00#32 by decide +kernel] using (h.table ⟨0,by decide⟩).2.2
  obtain ⟨a,ta,pa,a13,a10,a12,a9,ar,ac⟩ := StateMethodRefusal.contract B c ram
    (BitVec.ofNat 8 (MainMethodSpec.tag (MainMethodSpec.decode (MainMethodBytes.token input head.method.2))))
    h.stable.fp result h.stable.one stack (h.futures ⟨4,by decide⟩ ⟨0,by decide⟩) (h.futures ⟨4,by decide⟩ ⟨1,by decide⟩)
    h.stored.methodByte getRoute notGet notHead pc
  have regs (r : Reg) (member : r∈[2,8,18,19,22,23,24,25,26,27]) : a.get r=c.get r := by
    have safe : ∀ r : Reg,r∈[2,8,18,19,22,23,24,25,26,27] → r≠13 ∧ r≠10 ∧ r≠12 ∧ r≠9 := by decide
    obtain ⟨n13,n10,n12,n9⟩ := safe r member;exact ar r n13 n10 n12 n9
  have live : RuntimeRouteEnvelope.At a ram input s head amount rawUsed served lowValue close :=
    RuntimeRouteEnvelope.preserve h regs ac (fun _ => rfl) (fun _ _ => rfl)
  obtain ⟨d,td,entry,d9,dc,frame⟩ := call live pa
  exact ⟨d,ta.trans td,entry,d9.trans a9,dc.trans ac,frame⟩

/-- The first-candidate decision is tied to the actual previous matcher
    conclusion and pure method/path predicates. No chosen branch is assumed. -/
theorem advance {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close)
    (pc : c.pc=0x800013d2#32)
    (result : c.get 10=(if RuntimeRequestSpans.path input head=WireSpec.ascii "/state" then 1#32 else 0#32))
    (eligible : RuntimeRequestSpans.path input head≠WireSpec.ascii "/state" ∨
      (MainMethodSpec.decode (MainMethodBytes.token input head.method.2)≠.get ∧ MainMethodSpec.decode (MainMethodBytes.token input head.method.2)≠.head)) :
    ∃ n d, n≤22 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,RouteSecondCore.memory ram (rx+BitVec.ofNat 32 head.target.1)⟩ ∧
      RuntimeLiteralInput.At d (RouteSecondCore.memory ram (rx+BitVec.ofNat 32 head.target.1)) input s head amount rawUsed served lowValue close
        (RouteLiteralInfo.pointer .setpoint) (BitVec.ofNat 32 (RouteLiteralInfo.text .setpoint).length) 0x80001422#32 ∧
      d.get 9=(if RuntimeRequestSpans.path input head=WireSpec.ascii "/state" then 2#32 else 3#32) ∧ d.sameCsr c ∧
      ViewFrame.Region ram (RouteSecondCore.memory ram (rx+BitVec.ofNat 32 head.target.1)) sp 3304 := by
  by_cases selected : RuntimeRequestSpans.path input head=WireSpec.ascii "/state"
  · have bad : MainMethodSpec.decode (MainMethodBytes.token input head.method.2)≠.get ∧ MainMethodSpec.decode (MainMethodBytes.token input head.method.2)≠.head := by
      rcases eligible with absent|wrong
      · exact False.elim (absent selected)
      · exact wrong
    obtain ⟨d,trace,entry,flag,csr,frame⟩ := wrong_method h pc (by simpa only [selected,ite_true] using result) bad
    exact ⟨22,d,by decide,trace,entry,by simpa only [selected,ite_true] using flag,csr,frame⟩
  · obtain ⟨d,trace,entry,flag,csr,frame⟩ := missing h pc (by simpa only [selected,ite_false] using result)
    exact ⟨12,d,by decide,trace,entry,by simpa only [selected,ite_false] using flag,csr,frame⟩
end E5R.Thermostat.StackRuntimeSecondCandidate
