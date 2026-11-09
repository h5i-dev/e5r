import Projects.thermostat.PreparedRefusalPrepare
import Projects.thermostat.RuntimeRelayRefusal
import Projects.thermostat.RuntimeRelayWrongMethod
import Projects.thermostat.RuntimeRouteRefusal
import Projects.thermostat.RuntimeRouteRelayWrongMethod
set_option autoImplicit false
namespace E5R.Thermostat.RouteRefusalPrepare
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
abbrev sp := 0x80ffeb90#32
abbrev fp := 0x80fff814#32
theorem unmatched {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot}
    {served : Nat} {used : Word} {close : Bool} (known : Bool)
    (h : MainTransactionStable.At c ram input s) (metadata : LoopTransactionMemory.At ram used)
    (serve : MainServeLayout.At ram served) (pc : c.pc=0x80001898#32)
    (flag : c.get 9=(if known then 2#32 else 3#32))
    (future : c.get 23=0x80fff9f0#32) (three : c.get 26=3#32) (two : c.get 18=2#32)
    (replyCapacity : ramRead ram 0x80fff9fc#32 .w=832#32)
    (closeByte : ram 0x80fff878#32=Encoding.boolByte close) (room : close=false → served<100)
    : ∃ n d after headOnly,Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      NormalSendPhase.Ready d after ⟨s,RuntimeRefusalNext.status known,[],[]⟩ served used false close headOnly := by
  have stack : Memory.Block B sp 5232 := by
    have part := Memory.sub_block h.stack (off := 60304) (m := 5232) (by decide) (by decide)
    exact part
  obtain ⟨a,ta,pa,a10,a11,a20,a13,a12,a9,a24,a6,ar,ac⟩ := UnmatchedCore.contract B c ram known h.sp h.fp flag stack pc
  let mid := MainWriteFlags.memory ram fp
  have regs (r : Reg) (safe : r∈[2,8,18,19,22,23,26]) : a.get r=c.get r := by
    have ns : ∀ r : Reg,r∈[2,8,18,19,22,23,26] → r≠11 ∧ r≠20 ∧ r≠13 ∧ r≠9 ∧ r≠12 ∧ r≠10 ∧ r≠24 ∧ r≠6 := by decide
    obtain ⟨n11,n20,n13,n9,n12,n10,n24,n6⟩ := ns r safe
    exact ar r n11 n20 n13 n9 n12 n10 n24 n6
  have frame (off len : Nat) (bound : off+len≤3312) : ViewFrame.Region ram mid (sp+BitVec.ofNat 32 off) len := LoopSharedFrame.write_flags ram off len bound
  have app : AppState.At mid s := by
    apply AppState.preserve ram mid s h.app
    simpa only [ViewFrame.Region,show sp+44#32=0x80ffebbc#32 by decide +kernel] using frame 44 25 (by decide)
  have fpFrame : ViewFrame.Region ram mid fp 532 := MainWriteFlags.low ram fp
  have cap : ramRead mid 0x80fff9fc#32 .w=832#32 := by
    have word := ViewFrame.word fpFrame 488 (by decide)
    simpa only [show fp+BitVec.ofNat 32 488=0x80fff9fc#32 by decide +kernel] using word.trans replyCapacity
  have closeFrame : mid 0x80fff878#32=Encoding.boolByte close := by
    have byte := fpFrame ⟨100,by decide⟩
    simpa only [show fp+BitVec.ofNat 32 100=0x80fff878#32 by decide +kernel] using byte.trans closeByte
  have serveFrame : ViewFrame.Region ram mid fp 92 := ViewFrame.shrink fpFrame (by decide)
  have serveA := MainServeLayout.preserve (MainServeLayout.region serveFrame) serve
  have metadataA := LoopTransactionMemory.caller metadata (by simpa only [BitVec.add_zero] using frame 0 3304 (by decide))
  have statusWord : a.get 10=BitVec.ofNat 32 (RuntimeRefusalNext.status known) := by cases known <;> exact a10
  have closeWord : mid 0x80fff878#32=(if close then 1#8 else 0#8) := by cases close <;> exact closeFrame
  have stable : MainTransactionStable.At a mid input s := by
    refine ⟨(regs 2 (by decide)).trans h.sp,(regs 8 (by decide)).trans h.fp,
      (regs 19 (by decide)).trans h.uart,(regs 22 (by decide)).trans h.one,h.bound,
      (ViewFrame.word fpFrame 84 (by decide)).trans h.filled,?_,app,h.invariant,h.stack,(congrArg Prod.fst ac).trans h.masked⟩
    intro i
    have rx := frame 132 2048 (by decide)
    exact (rx ⟨i.val,by have := i.isLt;have := h.bound;omega⟩).trans (h.bytes i)
  obtain ⟨d,after,prepare,ready⟩ := PreparedRefusalPrepare.contract (RuntimeRefusalNext.status known) stable metadataA serveA pa
    (by cases known <;> decide) (by cases known <;> decide) statusWord a11 a20 a13 a12 a9 a24
    ((regs 23 (by decide)).trans future) ((regs 26 (by decide)).trans three) ((regs 18 (by decide)).trans two) cap closeFrame room
  exact ⟨13+26,d,after,_,ta.trans prepare,ready⟩

theorem relay_miss {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool} {used : Word}
    (known : Bool)
    (h : RuntimeLiteralInput.At c ram input s head amount rawUsed served lowValue close 0x80005b9c#32 10#32 0x80001856#32)
    (flag : c.get 9=(if known then 2#32 else 3#32)) (leading : ∃ ys,RuntimeRequestSpans.path input head=47#8::ys)
    (missing : ¬RouteSpec.relayPath (RuntimeRequestSpans.path input head)) (metadata : LoopTransactionMemory.At ram used)
    : ∃ n d after headOnly,Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      NormalSendPhase.Ready d after ⟨s,RuntimeRefusalNext.status known,[],[]⟩ served used false close headOnly := by
  obtain ⟨nm,b,bound,matched,pb,b10,b11,abi,bc,low,high,stable⟩ := RuntimeRelayMatch.contract h leading
  let after := RuntimeRelayMatch.memory ram c input head
  have frame (off len : Nat) (fits : off+len≤3648) : ViewFrame.Region ram after (sp+BitVec.ofNat 32 off) len := by
    intro i
    have byte := low ⟨off+i.val,by have := i.isLt;omega⟩
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using byte
  have futureFrame : ViewFrame.Region ram after 0x80fff814#32 92 := by
    simpa only [show sp+3204#32=0x80fff814#32 by decide +kernel] using frame 3204 92 (by decide)
  have serve := MainServeLayout.preserve (MainServeLayout.region futureFrame) h.live.serve
  have cap : ramRead after 0x80fff9fc#32 .w=832#32 := by
    have word := ViewFrame.word high 36 (by decide)
    simpa only [BitVec.add_assoc,show 3656#32+36#32=3692#32 by decide +kernel,show sp+3692#32=0x80fff9fc#32 by decide +kernel] using word.trans h.live.replyCapacity
  have closeByte : after 0x80fff878#32=Encoding.boolByte close := by
    have byte := low ⟨3304,by decide⟩
    simpa only [show sp+BitVec.ofNat 32 3304=0x80fff878#32 by decide +kernel] using byte.trans h.live.closeByte
  have metadataB := LoopTransactionMemory.caller metadata (by simpa only [BitVec.add_zero] using frame 0 3304 (by decide))
  have tested : taken .ne (b.get 10) (b.get 22)=true := by rw [b10];simp only [missing,ite_false];rw [stable.one];decide
  obtain ⟨a,ta,pa,ar,ac⟩ := QuietBranch.contract B img b after 0x80001856#32 4#32 66#32 .ne 10 22 true pb
    (by decide) (by decide) rl2147489878 tested
  have ap : a.pc=0x80001898#32 := by simpa only [ite_true,show 0x80001856#32+66#32=0x80001898#32 by decide +kernel] using pa
  have stableA : MainTransactionStable.At a after input s :=
    ⟨(ar 2).trans stable.sp,(ar 8).trans stable.fp,(ar 19).trans stable.uart,(ar 22).trans stable.one,
      stable.bound,stable.filled,stable.bytes,stable.app,stable.invariant,stable.stack,(congrArg Prod.fst ac).trans stable.masked⟩
  have room : close=false → served<100 := by
    intro kept
    by_cases reached : 100≤served
    · have forced := MainCloseSpec.limit head.minor served reached (RuntimeRequestSpans.raw input rawUsed) (RuntimeRequestInputs.entries head)
      have contradiction := h.live.closeSpec.trans forced
      rw [kept] at contradiction;cases contradiction
    · omega
  obtain ⟨nr,d,final,headOnly,response,ready⟩ := unmatched known stableA metadataB serve ap
    ((ar 9).trans ((abi 9 (by decide)).trans flag))
    ((ar 23).trans ((abi 23 (by decide)).trans h.live.future)) ((ar 26).trans ((abi 26 (by decide)).trans h.live.three))
    ((ar 18).trans ((abi 18 (by decide)).trans h.live.two)) cap closeByte room
  exact ⟨nm+1+nr,d,final,headOnly,(matched.trans ta).trans response,ready⟩

theorem relay_wrong_method {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool} {used : Word}
    (h : RuntimeLiteralInput.At c ram input s head amount rawUsed served lowValue close 0x80005b9c#32 10#32 0x80001856#32)
    (leading : ∃ ys,RuntimeRequestSpans.path input head=47#8::ys)
    (route : RouteSpec.relayPath (RuntimeRequestSpans.path input head))
    (method : MainMethodSpec.decode (MainMethodBytes.token input head.method.2)≠.put)
    (metadata : LoopTransactionMemory.At ram used)
    : ∃ n d after headOnly,Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      NormalSendPhase.Ready d after ⟨s,405,[],[]⟩ served used false close headOnly := by
  obtain ⟨nm,b,_,matched,pb,b10,b11,abi,bc,low,high,stable⟩ := RuntimeRelayMatch.contract h leading
  let mid := RuntimeRelayMatch.memory ram c input head
  have region (off len : Nat) (fits : off+len≤3648) : ViewFrame.Region ram mid (sp+BitVec.ofNat 32 off) len := by
    intro i
    have byte := low ⟨off+i.val,by have := i.isLt;omega⟩
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using byte
  have word (off : Nat) (fit : off+4≤1576) := ViewFrame.word high off fit
  have router : ramRead mid 0x80fffa14#32 .w=0x80ffebd8#32 := by
    have w := word 60 (by decide)
    simpa only [BitVec.add_assoc,show 3656#32+60#32=3716#32 by decide +kernel,show sp+3716#32=0x80fffa14#32 by decide +kernel] using w.trans ((h.live.futures 0 0).trans (show MainRouterFutures.value 0 0=0x80ffebd8#32 by decide +kernel))
  have request : ramRead mid 0x80fffa18#32 .w=0x80fff880#32 := by
    have w := word 64 (by decide)
    simpa only [BitVec.add_assoc,show 3656#32+64#32=3720#32 by decide +kernel,show sp+3720#32=0x80fffa18#32 by decide +kernel] using w.trans ((h.live.futures 0 1).trans (show MainRouterFutures.value 0 1=0x80fff880#32 by decide +kernel))
  let tag : BitVec 8 := BitVec.ofNat 8 (MainMethodSpec.tag (MainMethodSpec.decode (MainMethodBytes.token input head.method.2)))
  have tagByte : mid 0x80fff9f4#32=tag := by
    have byte := high ⟨28,by decide⟩
    simpa only [BitVec.add_assoc,show 3656#32+BitVec.ofNat 32 28=3684#32 by decide +kernel,show sp+3684#32=0x80fff9f4#32 by decide +kernel] using byte.trans h.live.stored.methodByte
  have tagNotPut : tag≠3#8 := by
    unfold tag
    cases token : MainMethodSpec.decode (MainMethodBytes.token input head.method.2) with
    | put => exact False.elim (method token)
    | get | head | post | patch | delete | other => decide +kernel
  have routeTag : mid 0x80ffec10#32=3#8 := by
    have byte := low ⟨128,by decide⟩
    simpa only [show sp+BitVec.ofNat 32 128=0x80ffec10#32 by decide +kernel] using byte.trans (h.live.table ⟨4,by decide⟩).2.2
  have stack : Memory.Block B sp 5232 := by
    have part := Memory.sub_block stable.stack (off := 60304) (m := 5232) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using part
  have matchedFlag : b.get 10=1#32 := by simpa only [route,ite_true] using b10
  obtain ⟨a,ta,pa,a13,a10,a12,a6,ar,ac⟩ := RelayMethodRefusal.contract B b mid tag stable.sp stable.fp matchedFlag stable.one stack
    router request tagByte routeTag tagNotPut pb
  have a2 := (ar 2 (by decide) (by decide) (by decide) (by decide)).trans stable.sp
  have a8 := (ar 8 (by decide) (by decide) (by decide) (by decide)).trans stable.fp
  obtain ⟨d,td,pd,d10,d11,d20,d13,d12,d9,d24,d6,dr,dc⟩ := RelayWrongSetup.contract B a mid a2 a8 stack pa
  let after := MainWriteFlags.memory mid fp
  have keep (r : Reg) (member : r∈[2,8,18,19,22,23,26]) : d.get r=c.get r := by
    have safe : ∀ r : Reg,r∈[2,8,18,19,22,23,26] → r≠11 ∧ r≠20 ∧ r≠13 ∧ r≠9 ∧ r≠12 ∧ r≠10 ∧ r≠24 ∧ r≠6 := by decide
    obtain ⟨n11,n20,n13,n9,n12,n10,n24,n6⟩ := safe r member
    exact (dr r n11 n20 n13 n9 n12 n10 n24 n6).trans ((ar r n13 n10 n12 n6).trans (abi r (by
      have subset : ∀ r : Reg,r∈[2,8,18,19,22,23,26] → r∈[1,2,3,4,5,6,7,8,9,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] := by decide
      exact subset r member)))
  have poll (off len : Nat) (fits : off+len≤3312) : ViewFrame.Region mid after (sp+BitVec.ofNat 32 off) len := LoopSharedFrame.write_flags mid off len fits
  have fpFrame : ViewFrame.Region ram mid fp 92 := by
    simpa only [show sp+3204#32=fp by decide +kernel] using region 3204 92 (by decide)
  have pollFp : ViewFrame.Region mid after fp 532 := MainWriteFlags.low mid fp
  have serve := MainServeLayout.preserve (MainServeLayout.region (ViewFrame.shrink pollFp (by decide)))
    (MainServeLayout.preserve (MainServeLayout.region fpFrame) h.live.serve)
  have stableD : MainTransactionStable.At d after input s := by
    refine ⟨(keep 2 (by decide)).trans h.live.stable.sp,(keep 8 (by decide)).trans h.live.stable.fp,
      (keep 19 (by decide)).trans h.live.stable.uart,(keep 22 (by decide)).trans h.live.stable.one,stable.bound,
      (ViewFrame.word pollFp 84 (by decide)).trans stable.filled,?_,?_,stable.invariant,stable.stack,?_⟩
    · intro i
      have byte := poll 132 2048 (by decide) ⟨i.val,by have := i.isLt;have := stable.bound;omega⟩
      simpa only [show sp+132#32=RuntimeRouteEnvelope.rx by decide +kernel] using byte.trans (stable.bytes i)
    · apply AppState.preserve mid after s stable.app
      simpa only [ViewFrame.Region,show sp+44#32=0x80ffebbc#32 by decide +kernel] using poll 44 25 (by decide)
    · exact (congrArg Prod.fst (dc.trans (ac.trans bc))).trans h.live.stable.masked
  have metadataD := LoopTransactionMemory.caller
    (LoopTransactionMemory.caller metadata (by simpa only [BitVec.add_zero] using region 0 3304 (by decide)))
    (by simpa only [BitVec.add_zero] using poll 0 3304 (by decide))
  have capacity : ramRead after 0x80fff9fc#32 .w=832#32 := by
    have w := word 36 (by decide)
    have cap : ramRead mid 0x80fff9fc#32 .w=832#32 := by
      simpa only [BitVec.add_assoc,show 3656#32+36#32=3692#32 by decide +kernel,show sp+3692#32=0x80fff9fc#32 by decide +kernel] using w.trans h.live.replyCapacity
    have w' := ViewFrame.word pollFp 488 (by decide)
    simpa only [show fp+BitVec.ofNat 32 488=0x80fff9fc#32 by decide +kernel] using w'.trans cap
  have flag : after 0x80fff878#32=Encoding.boolByte close := by
    have old := low ⟨3304,by decide⟩
    have eq : mid 0x80fff878#32=Encoding.boolByte close := by
      simpa only [show sp+BitVec.ofNat 32 3304=0x80fff878#32 by decide +kernel] using old.trans h.live.closeByte
    have byte := pollFp ⟨100,by decide⟩
    simpa only [show fp+BitVec.ofNat 32 100=0x80fff878#32 by decide +kernel] using byte.trans eq
  have room : close=false → served<100 := by
    intro kept
    by_cases reached : 100≤served
    · have forced := MainCloseSpec.limit head.minor served reached (RuntimeRequestSpans.raw input rawUsed) (RuntimeRequestInputs.entries head)
      have contradiction := h.live.closeSpec.trans forced
      rw [kept] at contradiction;cases contradiction
    · omega
  obtain ⟨e,final,te,done⟩ := PreparedRefusalPrepare.contract 405 stableD metadataD serve pd (by decide) (by decide)
    d10 d11 d20 d13 d12 d9 d24 ((keep 23 (by decide)).trans h.live.future) ((keep 26 (by decide)).trans h.live.three)
    ((keep 18 (by decide)).trans h.live.two) capacity flag room
  exact ⟨nm+11+10+26,e,final,_,((matched.trans ta).trans td).trans te,done⟩

theorem route_miss {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool} {used : Word}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close)
    (pc : c.pc=0x800013d2#32)
    (result : c.get 10=(if RuntimeRequestSpans.path input head=WireSpec.ascii "/state" then 1#32 else 0#32))
    (denied : ∀ kind : RouteLiteralInfo.Kind,RuntimeRequestSpans.path input head=RouteLiteralInfo.text kind →
      RouteSpec.allows (RouteLiteralInfo.route kind) (MainMethodSpec.decode (MainMethodBytes.token input head.method.2))=false)
    (missing : ¬RouteSpec.relayPath (RuntimeRequestSpans.path input head))
    (leading : ∃ ys,RuntimeRequestSpans.path input head=47#8::ys) (metadata : LoopTransactionMemory.At ram used)
    : ∃ n d after headOnly,Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      NormalSendPhase.Ready d after ⟨s,RouteRefusalSpec.status (RuntimeRequestSpans.path input head),[],[]⟩ served used false close headOnly := by
  obtain ⟨na,a,mid,_,ta,entry,flag,metadataA,_⟩ := RuntimeRelayEntry.contract h pc result denied leading metadata
  have flagWord : a.get 9=(if decide (RuntimeRelayEntry.known (RuntimeRequestSpans.path input head)) then 2#32 else 3#32) := by
    by_cases yes : RuntimeRelayEntry.known (RuntimeRequestSpans.path input head) <;> simpa only [yes,decide_true,decide_false,ite_true,Bool.false_eq_true,ite_false] using flag
  obtain ⟨nb,d,after,headOnly,tb,ready⟩ := relay_miss (decide (RuntimeRelayEntry.known (RuntimeRequestSpans.path input head))) entry flagWord leading missing metadataA
  exact ⟨na+nb,d,after,headOnly,ta.trans tb,by simpa only [RuntimeRouteRefusal.status_eq] using ready⟩

theorem route_wrong_method {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool} {used : Word}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close)
    (pc : c.pc=0x800013d2#32)
    (result : c.get 10=(if RuntimeRequestSpans.path input head=WireSpec.ascii "/state" then 1#32 else 0#32))
    (route : RouteSpec.relayPath (RuntimeRequestSpans.path input head))
    (method : MainMethodSpec.decode (MainMethodBytes.token input head.method.2)≠.put)
    (leading : ∃ ys,RuntimeRequestSpans.path input head=47#8::ys) (metadata : LoopTransactionMemory.At ram used)
    : ∃ n d after headOnly,Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      NormalSendPhase.Ready d after ⟨s,405,[],[]⟩ served used false close headOnly := by
  have denied (kind : RouteLiteralInfo.Kind) (selected : RuntimeRequestSpans.path input head=RouteLiteralInfo.text kind) :
      RouteSpec.allows (RouteLiteralInfo.route kind) (MainMethodSpec.decode (MainMethodBytes.token input head.method.2))=false := by
    have headPrefix := route.1
    rw [selected] at headPrefix
    have different : (RouteLiteralInfo.text kind).take 7≠WireSpec.ascii "/relay/" := by cases kind <;> decide +kernel
    exact False.elim (different headPrefix)
  obtain ⟨na,a,mid,_,ta,entry,_,metadataA,_⟩ := RuntimeRelayEntry.contract h pc result denied leading metadata
  obtain ⟨nb,d,after,headOnly,tb,done⟩ := relay_wrong_method entry leading route method metadataA
  exact ⟨na+nb,d,after,headOnly,ta.trans tb,done⟩
end E5R.Thermostat.RouteRefusalPrepare
