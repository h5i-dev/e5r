import Projects.thermostat.RuntimeRelayMatch
import Projects.thermostat.RelayMethodRefusal
import Projects.thermostat.RelayWrongSetup
import Projects.thermostat.RuntimePreparedRefusalNext
set_option autoImplicit false
namespace E5R.Thermostat.RuntimeRelayWrongMethod
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
abbrev sp := RuntimeRouteEnvelope.sp
abbrev fp := 0x80fff814#32

theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool} {used : Word}
    (h : RuntimeLiteralInput.At c ram input s head amount rawUsed served lowValue close 0x80005b9c#32 10#32 0x80001856#32)
    (leading : ∃ ys,RuntimeRequestSpans.path input head=47#8::ys)
    (route : RouteSpec.relayPath (RuntimeRequestSpans.path input head))
    (method : MainMethodSpec.decode (MainMethodBytes.token input head.method.2)≠.put)
    (metadata : LoopTransactionMemory.At ram used) (slots : List UartTxLoop.Slot)
    (length : slots.length=(ResponseHeadSpec.bytes 405 [] 0 close).length) :
    ∃ n d after,Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads slots)
      (UartTxLoop.events (ResponseHeadSpec.bytes 405 [] 0 close)) ∧ LoopReady.At d after s (if close then 0 else served) := by
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
  obtain ⟨ne,e,final,te,done⟩ := RuntimePreparedRefusalNext.contract 405 stableD metadataD serve pd (by decide) (by decide)
    d10 d11 d20 d13 d12 d9 d24 ((keep 23 (by decide)).trans h.live.future) ((keep 26 (by decide)).trans h.live.three)
    ((keep 18 (by decide)).trans h.live.two) capacity flag room slots length
  refine ⟨nm+11+10+ne,e,final,?_,done⟩
  simpa only [List.nil_append] using (((matched.observed.trans ta.observed).trans td.observed).trans te)
end E5R.Thermostat.RuntimeRelayWrongMethod
