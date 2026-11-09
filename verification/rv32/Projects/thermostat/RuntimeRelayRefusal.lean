import Projects.thermostat.RuntimeRelayMatch
import Projects.thermostat.RuntimeRefusalNext
set_option autoImplicit false
namespace E5R.Thermostat.RuntimeRelayRefusal
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
abbrev sp := RuntimeRouteEnvelope.sp

/-- Generic received Request reaches its real final refusal and next request.
    A failed capture may write params; live metadata comes from disjoint RAM. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool} {used : Word}
    (known : Bool)
    (h : RuntimeLiteralInput.At c ram input s head amount rawUsed served lowValue close 0x80005b9c#32 10#32 0x80001856#32)
    (flag : c.get 9=(if known then 2#32 else 3#32)) (leading : ∃ ys,RuntimeRequestSpans.path input head=47#8::ys)
    (missing : ¬RouteSpec.relayPath (RuntimeRequestSpans.path input head)) (metadata : LoopTransactionMemory.At ram used)
    (slots : List UartTxLoop.Slot) (length : slots.length=(ResponseHeadSpec.bytes (RuntimeRefusalNext.status known) [] 0 close).length) :
    ∃ n d after,Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads slots)
      (UartTxLoop.events (ResponseHeadSpec.bytes (RuntimeRefusalNext.status known) [] 0 close)) ∧ LoopReady.At d after s (if close then 0 else served) := by
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
  have tested : taken .ne (b.get 10) (b.get 22)=true := by rw [b10,if_neg missing,stable.one];decide
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
  obtain ⟨nr,d,final,response,ready⟩ := RuntimeRefusalNext.contract known stableA metadataB serve ap
    ((ar 9).trans ((abi 9 (by decide)).trans flag))
    ((ar 23).trans ((abi 23 (by decide)).trans h.live.future)) ((ar 26).trans ((abi 26 (by decide)).trans h.live.three))
    ((ar 18).trans ((abi 18 (by decide)).trans h.live.two)) cap closeByte room slots length
  refine ⟨nm+1+nr,d,final,?_,ready⟩
  simpa only [List.nil_append] using (matched.observed.trans ta.observed).trans response
end E5R.Thermostat.RuntimeRelayRefusal
