import Projects.thermostat.NormalSendPhase
import Projects.thermostat.RefusalSendPhase
set_option autoImplicit false
namespace E5R.Thermostat.SenderEntry
open E5R E5R.Thermostat ProtocolStreamSpec
abbrev B := UartPlatform.board

/-- Every response has a nonempty real HTTP status line. Quiet entry code
    therefore reaches an active UART phase rather than silently returning. -/
theorem start (call : SendPhase.Call) {g : State} {p : ProtocolStreamSpec.Pending}
    (phase : g.phase=.reply p) (queue : p.remaining=SendPhase.header call++SendPhase.body call) :
    ReactiveEnvelope.Envelope (SendPhase.Active call) ⟨call.original,call.before⟩ g := by
  obtain ⟨mask,n,last,quiet,post⟩ := SendPhase.start call phase queue
  refine ⟨mask,n,last,quiet,?_⟩
  rcases post with active|returned
  · exact active
  · obtain ⟨ret,result,close,done,bytes,frame,q,phaseQ,empty⟩ := returned
    have same : q=p := Phase.reply.inj (phaseQ.symm.trans phase)
    subst q
    have noBytes : SendPhase.header call++SendPhase.body call=[] := queue.symm.trans empty
    have length := congrArg List.length noBytes
    simp only [SendPhase.header,ResponseHeadSpec.bytes,ResponseHeadSpec.statusLine,List.length_append,List.length_nil] at length
    have prefixLength : (WireSpec.ascii "HTTP/1.1 ").length=9 := by decide +kernel
    rw [prefixLength] at length
    omega

theorem masked {call : SendPhase.Call} {m g} (h : SendPhase.Active call m g) : m.core.mie_=false := by
  cases h with
  | head _ _ _ uart | body _ _ _ _ _ _ uart => exact UartTxPhase.masked uart.2.2.1

theorem normal {c ram g} (h : NormalSendPhase.Entry c ram g) :
    ReactiveEnvelope.Envelope NormalSendPhase.Active ⟨c,ram⟩ g := by
  obtain ⟨response,served,used,json,close,headOnly,ready,family,pending,phase,queue⟩ := h
  exact ReactiveEnvelope.map (start (NormalSendPhase.call ready) phase queue)
    (fun _ active => ⟨c,ram,response,served,used,json,close,headOnly,ready,active,family⟩)

theorem refusal {c ram g} (h : RefusalPhase.At c ram g) :
    ReactiveEnvelope.Envelope RefusalSendPhase.Active ⟨c,ram⟩ g := by
  obtain ⟨s,served,status,ready,ghost⟩ := h
  rw [ghost]
  let model := ProtocolStreamSpec.reject ⟨s,served,.head []⟩ status
  let pending : ProtocolStreamSpec.Pending :=
    ⟨⟨s,status,[],[]⟩,true,0,ResponseHeadSpec.bytes status [] 0 true++ResponseHeadSpec.body status false []⟩
  have phase : model.phase=.reply pending := rfl
  have queue : pending.remaining=SendPhase.header (RefusalSendPhase.call ready)++SendPhase.body (RefusalSendPhase.call ready) := rfl
  have family : RefusalSendPhase.Pending s served status model := ⟨rfl,rfl,pending,phase,rfl,rfl,rfl⟩
  exact ReactiveEnvelope.map (start (RefusalSendPhase.call ready) phase queue)
    (fun _ active => ⟨c,ram,s,served,status,ready,active,family⟩)
end E5R.Thermostat.SenderEntry
