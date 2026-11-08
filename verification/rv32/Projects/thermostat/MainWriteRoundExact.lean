import Projects.thermostat.MainWriteRound
import Projects.thermostat.MainWriteReplyExact
import Projects.thermostat.MainWriteReply
import Projects.thermostat.MainWritePost
namespace E5R.Thermostat.MainWriteRound
open E5R E5R.Thermostat

/-- Compose a proved actual main Write handler execution with real HTTP/UART
    output and the close/keep-alive dispatch. This does not assume the handler
    postcondition: callers supply its complete instruction execution proof. -/
theorem contract_exact (c a : Core) (before ram : Word → BitVec 8) (n : Nat) (state : Spec.Snapshot)
    (payload : List (BitVec 8)) (status : Nat) (close : Bool)
    (tbefore : Quiet.Steps B img n ⟨c,before⟩ ⟨a,ram⟩) (post : MainWritePost.At c a before ram state payload status)
    (hm : Memory.Block B 0x80ff0000#32 65536) (hbody : payload.length≤832) (hlo : 200≤status) (hst : status≤599)
    (hcap : ramRead before 0x80fff9fc#32 .w=832#32)
    (htx : ramRead before (0x80fff814#32+64#32) .w=0x80fff414#32)
    (htxc : ramRead before (0x80fff814#32+68#32) .w=1024#32)
    (hclose : before 0x80fff878#32=(if close then 1#8 else 0#8))
    (hs bs : List UartTxLoop.Slot) (hhs : hs.length=(ResponseHeadSpec.bytes status (WireSpec.ascii "application/json") payload.length close).length)
    (hbs : bs.length=(ResponseHeadSpec.body status (MainMethod.head (before 0x80fff9f4#32)) payload).length) :
    ∃ d k after, k≤n+2449+UartWriteAll.time (ResponseHeadSpec.bytes status (WireSpec.ascii "application/json") payload.length close) hs+
        UartWriteAll.time (ResponseHeadSpec.body status (MainMethod.head (before 0x80fff9f4#32)) payload) bs ∧
      Observed.Steps B img k ⟨c,before⟩ ⟨d,after⟩ (UartTxLoop.reads hs++UartTxLoop.reads bs)
        (UartTxLoop.events (ResponseHeadSpec.bytes status (WireSpec.ascii "application/json") payload.length close)++
          UartTxLoop.events (ResponseHeadSpec.body status (MainMethod.head (before 0x80fff9f4#32)) payload)) ∧
      d.pc=(if close then 0x80000978#32 else 0x800017be#32) ∧ d.get 2=0x80ffeb90#32 ∧ d.get 8=0x80fff814#32 ∧ d.sameCsr c ∧
      AppState.At after state ∧ Engine.InvariantAt after 0x80ffebbc#32 ∧ d.get 24=0xfffffffe#32 ∧ d.get 21=0xffffffff#32 ∧
      ViewFrame.Region before after 0x80ffec14#32 2048 := by
  have metaWord (off : Nat) (ho : off+4≤532) := ViewFrame.word post.metadata off ho
  have cap : ramRead ram 0x80fff9fc#32 .w=832#32 := by
    have hh := metaWord 488 (by decide)
    rw [show 0x80fff814#32+BitVec.ofNat 32 488=0x80fff9fc#32 by decide +kernel] at hh
    exact hh.trans hcap
  have closeVal : ram 0x80fff878#32=(if close then 1#8 else 0#8) := by
    have hh := post.metadata ⟨100,by decide⟩
    rw [show 0x80fff814#32+BitVec.ofNat 32 100=0x80fff878#32 by decide +kernel] at hh
    exact hh.trans hclose
  have method : ram 0x80fff9f4#32=before 0x80fff9f4#32 := by
    have hh := post.metadata ⟨480,by decide⟩
    rw [show 0x80fff814#32+BitVec.ofNat 32 480=0x80fff9f4#32 by decide +kernel] at hh
    exact hh
  obtain ⟨d,k,after,bk,tk,pd,d2,d8,kd,app,inv,d24,d21,rx⟩ := MainWriteReply.contract_exact a ram state
    (ramRead before (0x80fff814#32+72#32) .w) payload status close post.pc post.sp post.fp post.ready post.completion hm
    post.app post.inv hbody hlo hst post.response post.body cap
    ((metaWord 64 (by decide)).trans htx) ((metaWord 68 (by decide)).trans htxc) (metaWord 72 (by decide)) closeVal
    hs bs hhs (by rw [method];exact hbs)
  rw [method] at bk tk
  have tp := tbefore.observed
  refine ⟨d,n+k,after,by omega,?_,pd,d2,d8,kd.trans post.csr,app,inv,d24,d21,?_⟩
  · simpa only [List.nil_append,List.append_assoc] using tp.trans tk
  · intro i;exact (rx i).trans (post.rx i)
end E5R.Thermostat.MainWriteRound
