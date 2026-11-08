import Projects.thermostat.MainStatusAuthHandler
import Projects.thermostat.MainStatusReply
import Projects.thermostat.MainWriteInput
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.MainStatusPost
open E5R E5R.Thermostat

/-- The actual main handler-return cutpoint for an empty status response. This
    is the G5 counterpart of the existing JSON-specific MainWritePost.At. -/
structure At (c d : Core) (before after : Word → BitVec 8) (state : Spec.Snapshot) (status : Nat) : Prop where
  pc : d.pc=0x8000196c#32
  sp : d.get 2=0x80ffeb90#32
  fp : d.get 8=0x80fff814#32
  ready : d.get 18=1#32
  completion : d.get 22=1#32
  csr : d.sameCsr c
  app : AppState.At after state
  inv : Spec.Inv state
  response : StatusMemory.At after 0x80fffd38#32 (BitVec.ofNat 32 status)
  metadata : ViewFrame.Region before after 0x80fff814#32 532
  rx : ViewFrame.Region before after 0x80ffec14#32 2048
end E5R.Thermostat.MainStatusPost

namespace E5R.Thermostat.MainStatusAuth401
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

/-- Actual main call, auth lookup, absent/bad-credential refusal and handler
    RET. The decoder and engine are not run; the original App state remains. -/
theorem handler (c : Core) (ram : Word → BitVec 8) (req rawPtr pathPtr bodyPtr : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8))) (state : Spec.Snapshot)
    (hp : c.pc=0x8000195a#32) (h2 : c.get 2=0x80ffeb90#32) (h8 : c.get 8=0x80fff814#32)
    (h18 : c.get 18=1#32) (h22 : c.get 22=1#32) (h24 : c.get 24=0x80fffa2c#32)
    (stack : Memory.Block B 0x80ff0000#32 65536) (app : AppState.At ram state) (inv : Spec.Inv state)
    (input : MainWriteInput.Ready ram req rawPtr pathPtr bodyPtr raw path body entries first state)
    (denied : AuthSpec.authorized (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) (WireSpec.ascii "dev-key")=false) :
    ∃ d n after, n≤212*entries.length+208 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧ MainStatusPost.At c d ram after state 401 := by
  obtain ⟨a,call,returnPC,frame,csr,pre⟩ := MainWriteInput.establishes c ram req rawPtr pathPtr bodyPtr raw path body entries first state hp h2 h24 stack input
  have result : Memory.Block B 0x80fffd38#32 15 := by
    have region := Memory.sub_block stack (off := 64824) (m := 15) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+BitVec.ofNat 32 (64824 : Nat)=0x80fffd38#32 by decide +kernel] using region
  obtain ⟨d,n,after,bound,handled,ret,response,snapshot,borrow,_,_,_,memory⟩ := MainStatusAuthHandler.contract a ram req 0x80ffebbc#32 rawPtr pathPtr bodyPtr
    raw path body entries first true state pre denied inv result (by decide)
    (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
  have nextApp := MainWritePost.app memory app state
    (by simpa only [show 0x80ffebbc#32+4#32=0x80ffebc0#32 by decide +kernel] using snapshot) borrow
  refine ⟨d,6+n,after,by omega,call.trans handled,?_,?_,?_,?_,?_,ret.csr.trans csr,nextApp,inv,response,
    MainWritePost.metadata memory,MainWritePost.rx memory⟩
  · rw [ret.pc,returnPC]
    decide +kernel
  · exact ret.sp.trans ((frame 2 (by decide) (by decide) (by decide)).trans h2)
  · exact ret.x8.trans ((frame 8 (by decide) (by decide) (by decide)).trans h8)
  · exact ret.x18.trans ((frame 18 (by decide) (by decide) (by decide)).trans h18)
  · exact ret.x22.trans ((frame 22 (by decide) (by decide) (by decide)).trans h22)

/-- G5 auth-refusal edge closed locally: actual PC195a -> lookup/refusal/RET ->
    empty401 HTTP/UART response -> real keep/close transaction boundary. -/
theorem contract_exact (c : Core) (ram : Word → BitVec 8) (req rawPtr pathPtr bodyPtr : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8))) (state : Spec.Snapshot)
    (hp : c.pc=0x8000195a#32) (h2 : c.get 2=0x80ffeb90#32) (h8 : c.get 8=0x80fff814#32)
    (h18 : c.get 18=1#32) (h22 : c.get 22=1#32) (h24 : c.get 24=0x80fffa2c#32)
    (stack : Memory.Block B 0x80ff0000#32 65536) (app : AppState.At ram state) (inv : Spec.Inv state)
    (input : MainWriteInput.Ready ram req rawPtr pathPtr bodyPtr raw path body entries first state)
    (denied : AuthSpec.authorized (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) (WireSpec.ascii "dev-key")=false)
    (close : Bool) (capacity : ramRead ram 0x80fff9fc#32 .w=832#32)
    (tx : ramRead ram (0x80fff814#32+64#32) .w=0x80fff414#32)
    (txCapacity : ramRead ram (0x80fff814#32+68#32) .w=1024#32)
    (closeFlag : ram 0x80fff878#32=(if close then 1#8 else 0#8))
    (hs bs : List UartTxLoop.Slot) (hhs : hs.length=(ResponseHeadSpec.bytes 401 [] 0 close).length)
    (hbs : bs.length=(ResponseHeadSpec.body 401 (MainMethod.head (ram 0x80fff9f4#32)) []).length) :
    ∃ d n after, n≤212*entries.length+2657+UartWriteAll.time (ResponseHeadSpec.bytes 401 [] 0 close) hs+
        UartWriteAll.time (ResponseHeadSpec.body 401 (MainMethod.head (ram 0x80fff9f4#32)) []) bs ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads hs++UartTxLoop.reads bs)
        (UartTxLoop.events (ResponseHeadSpec.bytes 401 [] 0 close)++UartTxLoop.events (ResponseHeadSpec.body 401 (MainMethod.head (ram 0x80fff9f4#32)) [])) ∧
      d.pc=(if close then 0x80000978#32 else 0x800017be#32) ∧ d.get 2=0x80ffeb90#32 ∧ d.get 8=0x80fff814#32 ∧ d.sameCsr c ∧
      AppState.At after state ∧ Engine.InvariantAt after 0x80ffebbc#32 ∧ ViewFrame.Region ram after 0x80ffec14#32 2048 := by
  obtain ⟨a,n,mid,bound,handled,post⟩ := handler c ram req rawPtr pathPtr bodyPtr raw path body entries first state hp h2 h8 h18 h22 h24 stack app inv input denied
  have metadataWord (off : Nat) (small : off+4≤532) := ViewFrame.word post.metadata off small
  have capacityNow : ramRead mid 0x80fff9fc#32 .w=832#32 := by
    have actual := metadataWord 488 (by decide)
    rw [show 0x80fff814#32+BitVec.ofNat 32 (488 : Nat)=0x80fff9fc#32 by decide +kernel] at actual
    exact actual.trans capacity
  have closeNow : mid 0x80fff878#32=(if close then 1#8 else 0#8) := by
    have actual := post.metadata ⟨100,by decide⟩
    simpa only [show 0x80fff814#32+BitVec.ofNat 32 (100 : Nat)=0x80fff878#32 by decide +kernel] using actual.trans closeFlag
  have method : mid 0x80fff9f4#32=ram 0x80fff9f4#32 := by
    simpa only [show 0x80fff814#32+BitVec.ofNat 32 (480 : Nat)=0x80fff9f4#32 by decide +kernel] using post.metadata ⟨480,by decide⟩
  obtain ⟨d,k,after,kb,sent,pc,d2,d8,dc,appAfter,invAfter,_,_,rx⟩ := MainStatusReply.contract_exact a mid state
    (ramRead ram (0x80fff814#32+72#32) .w) 401 close post.pc post.sp post.fp post.ready post.completion stack post.app post.inv
    (by decide) (by decide) post.response capacityNow ((metadataWord 64 (by decide)).trans tx) ((metadataWord 68 (by decide)).trans txCapacity)
    (metadataWord 72 (by decide)) closeNow hs bs hhs (by rw [method];exact hbs)
  rw [method] at kb sent
  refine ⟨d,n+k,after,by omega,?_,pc,d2,d8,dc.trans post.csr,appAfter,invAfter,?_⟩
  · simpa only [List.nil_append] using handled.observed.trans sent
  · intro i
    exact (rx i).trans (post.rx i)
end E5R.Thermostat.MainStatusAuth401
