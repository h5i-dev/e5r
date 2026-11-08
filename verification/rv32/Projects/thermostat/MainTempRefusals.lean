import Projects.thermostat.MainTempWriteInput
import Projects.thermostat.MainFutureAuthHandler
import Projects.thermostat.MainFutureDecodeHandler
import Projects.thermostat.MainStatusReturnJoin
set_option autoImplicit false
set_option maxRecDepth 6000
namespace E5R.Thermostat.MainTempRefusals
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
abbrev future := MainTempWriteInput.future
abbrev fp : Word := 0x80fff814#32

def Case (input : List (BitVec 8)) (head : Head) (amount status : Nat) : Prop :=
  (AuthSpec.authorized (HeaderSpec.lookup (MainRequestSpans.raw input head amount) (WireSpec.ascii "authorization") (MainRequestInputs.entries head)) (WireSpec.ascii "dev-key")=false ∧ status=401) ∨
  (AuthSpec.authorized (HeaderSpec.lookup (MainRequestSpans.raw input head amount) (WireSpec.ascii "authorization") (MainRequestInputs.entries head)) (WireSpec.ascii "dev-key")=true ∧
    WireSpec.decode (WireSpec.ascii "/temp") (MainRequestSpans.body input head amount) none=.error status)

theorem handler {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat} {close : Bool}
    (h : MainTempWriteInput.Ready c ram input s head amount served close) (status : Nat) (outcome : Case input head amount status) :
    ∃ d n after, n≤212*(MainRequestInputs.entries head).length+18*(MainRequestSpans.body input head amount).length+514 ∧
      Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧ WriteRefusal.Returned c d ∧ StatusMemory.At after 0x80fffd38#32 (BitVec.ofNat 32 status) ∧
      Encoding.SnapshotAt after 0x80ffebc0#32 s ∧ ramRead after 0x80ffebbc#32 .w=0#32 ∧
      Engine.InvariantAt after 0x80ffebbc#32 ∧ MainFutureFrame.At future ram after := by
  have outBlock : Memory.Block B 0x80fffd38#32 15 := by
    have block := Memory.sub_block h.stack (off := 64824) (m := 15) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+64824#32=0x80fffd38#32 by decide +kernel] using block
  rcases outcome with ⟨denied,rfl⟩|⟨allowed,rejected⟩
  · obtain ⟨d,n,after,bound,trace,ret,response,snapshot,borrow,inv,_,_,frame⟩ := MainFutureAuthHandler.contract c ram future
      0x80fff880#32 0x80ffebbc#32 0x80ffec14#32 (0x80ffec14#32+BitVec.ofNat 32 head.target.1) (0x80ffec14#32+BitVec.ofNat 32 head.len)
      (MainRequestSpans.raw input head amount) (WireSpec.ascii "/temp") (MainRequestSpans.body input head amount) (MainRequestInputs.entries head) none true s
      h.pre denied h.invariant outBlock (by decide)
      (WordRegions.before _ _ _ _ (by decide) (by decide)) (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
      (WordRegions.before _ _ _ _ (by decide) (by decide))
    exact ⟨d,n,after,by omega,trace,ret,response,snapshot,borrow,inv,frame⟩
  · obtain ⟨d,n,after,bound,trace,ret,response,snapshot,borrow,inv,_,_,frame⟩ := MainFutureDecodeHandler.contract c ram future
      0x80fff880#32 0x80ffebbc#32 0x80ffec14#32 (0x80ffec14#32+BitVec.ofNat 32 head.target.1) (0x80ffec14#32+BitVec.ofNat 32 head.len)
      (MainRequestSpans.raw input head amount) (WireSpec.ascii "/temp") (MainRequestSpans.body input head amount) (MainRequestInputs.entries head) none true s status
      h.pre allowed rejected h.invariant outBlock (by decide)
      (WordRegions.before _ _ _ _ (by decide) (by decide)) (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
      (WordRegions.before _ _ _ _ (by decide) (by decide))
    exact ⟨d,n,after,bound,trace,ret,response,snapshot,borrow,inv,frame⟩

theorem contract_exact {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat} {close : Bool}
    (h : MainTempWriteInput.Ready c ram input s head amount served close) (status : Nat) (outcome : Case input head amount status)
    (hlo : 200≤status) (hst : status≤599) (hs : List UartTxLoop.Slot) (hhs : hs.length=(ResponseHeadSpec.bytes status [] 0 close).length) :
    ∃ d n after, n≤212*(MainRequestInputs.entries head).length+18*(MainRequestSpans.body input head amount).length+2964+
        UartWriteAll.time (ResponseHeadSpec.bytes status [] 0 close) hs+UartWriteAll.time [] [] ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads hs) (UartTxLoop.events (ResponseHeadSpec.bytes status [] 0 close)) ∧
      d.pc=(if close then 0x80000978#32 else 0x800017be#32) ∧ d.get 2=0x80ffeb90#32 ∧ d.get 8=fp ∧ d.sameCsr c ∧
      AppState.At after s ∧ Engine.InvariantAt after 0x80ffebbc#32 ∧ ViewFrame.Region ram after 0x80ffec14#32 2048 := by
  obtain ⟨a,na,mid,ba,ta,ret,response,state,borrow,inv,memory⟩ := handler h status outcome
  have keys : ViewFrame.Region ram mid 0x80ffebcc#32 9 := MainFutureFrame.region memory
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.before _ _ _ _ (by decide) (by decide)) (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.before _ _ _ _ (by decide) (by decide)) (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
  have app : AppState.At mid s := by
    refine ⟨state,borrow,?_,?_,(keys ⟨8,by decide⟩).trans h.app.principal⟩
    · have word := ViewFrame.word keys 0 (by decide)
      simpa only [BitVec.add_zero] using word.trans h.app.keyPtr
    · exact (ViewFrame.word keys 4 (by decide)).trans h.app.keyLen
  have metadata : ViewFrame.Region ram mid fp 532 := MainFutureFrame.region memory
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.before _ _ _ _ (by decide) (by decide)) (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
  have word (off : Nat) (bound : off+4≤532) := ViewFrame.word metadata off bound
  have cap : ramRead mid 0x80fff9fc#32 .w=832#32 := by
    have value := word 488 (by decide)
    simpa only [show fp+BitVec.ofNat 32 (488 : Nat)=0x80fff9fc#32 by decide +kernel] using value.trans h.replyCapacity
  have flag : mid 0x80fff878#32=Encoding.boolByte close := by
    have byte := metadata ⟨100,by decide⟩
    simpa only [show fp+100#32=0x80fff878#32 by decide +kernel] using byte.trans h.closeByte
  have pc : a.pc=MainWriteReturnJoin.entry 1 := by rw [ret.pc,h.ret];decide +kernel
  obtain ⟨d,nb,after,bb,tb,pd,d2,d8,dc,appAfter,invAfter,rx⟩ := MainStatusReturnJoin.contract_exact 1 a mid s (ramRead ram (fp+72#32) .w) status close
    pc (ret.sp.trans h.sp) (ret.x8.trans h.fp) (ret.x18.trans h.two) (ret.x22.trans h.one) h.stack app h.invariant hlo hst response cap
    ((word 64 (by decide)).trans h.serve.tx) ((word 68 (by decide)).trans h.serve.txCapacity) (word 72 (by decide)) flag hs hhs
  refine ⟨d,na+nb,after,by omega,?_,pd,d2,d8,dc.trans ret.csr,appAfter,invAfter,?_⟩
  · simpa only [List.nil_append] using ta.observed.trans tb
  · have beforeRx : ViewFrame.Region ram mid 0x80ffec14#32 2048 := MainFutureFrame.region memory
      (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
      (WordRegions.before _ _ _ _ (by decide) (by decide)) (WordRegions.before _ _ _ _ (by decide) (by decide))
      (WordRegions.before _ _ _ _ (by decide) (by decide)) (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    intro i
    exact (rx i).trans (beforeRx i)
end E5R.Thermostat.MainTempRefusals
