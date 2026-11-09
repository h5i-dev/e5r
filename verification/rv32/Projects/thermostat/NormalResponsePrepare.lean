import Projects.thermostat.NormalSendPhase
import Projects.thermostat.LoopResponseExtracted
set_option autoImplicit false
namespace E5R.Thermostat.NormalResponsePrepare
open E5R E5R.Thermostat
abbrev B := UartPlatform.board
abbrev sp := 0x80ffeb90#32
abbrev fp := 0x80fff814#32

/-- Actual extracted handler reply at the common response entry. Every field
    is a caller obligation, discharged before the global firmware statement. -/
structure Ready (c : Core) (ram : Word → BitVec 8) (response : ApiWriteHttpSpec.Reply)
    (served : Nat) (used : Word) (json close headOnly : Bool) (entry : Word := 0x80001728#32) : Prop where
  pc : c.pc=entry
  spWord : c.get 2=sp
  fpWord : c.get 8=fp
  uart : c.get 19=0x10000000#32
  one : c.get 22=1#32
  two : c.get 18=2#32
  future : c.get 23=0x80fff9f0#32
  three : c.get 26=3#32
  masked : c.mie_=false
  stack : Memory.Block B 0x80ff0000#32 65536
  app : AppState.At ram response.state
  invariant : Spec.Inv response.state
  serve : MainServeLayout.At ram served
  room : close=false → served<100
  metadata : LoopTransactionMemory.At ram used
  mime : response.mime=MainResponseExtractedReply.mime json
  bodyBound : response.payload.length≤832
  statusLo : 200≤response.status
  statusHi : response.status≤599
  mimePointer : c.get 12=MainResponseExtractedReply.pointer json
  mimeLength : c.get 11=BitVec.ofNat 32 response.mime.length
  payloadLength : c.get 20=BitVec.ofNat 32 response.payload.length
  statusWord : c.get 10=BitVec.ofNat 32 response.status
  zero : c.get 13=0#32
  objectArg : c.get 9=0x80fff878#32
  minusTwo : c.get 24=0xfffffffe#32
  payload : Bytes.Span B ram 0x80fff4d4#32 response.payload
  replyCapacity : ramRead ram 0x80fff9fc#32 .w=832#32
  closeByte : ram 0x80fff878#32=(if close then 1#8 else 0#8)
  method : MainMethod.head (ram 0x80fff9f4#32)=headOnly

/-- Real response descriptor stores and the actual main Send call. No bytes,
    desired response, future PC or layout are assumed from the environment. -/
theorem prepare {c ram response served used json close headOnly}
    (h : Ready c ram response served used json close headOnly) :
    ∃ d after,Quiet.Steps B img 26 ⟨c,ram⟩ ⟨d,after⟩ ∧ NormalSendPhase.Ready d after response served used json close headOnly := by
  obtain ⟨a,after,tail,pc,spWord,fpWord,objectArg,minusTwo,csr,app,inv,bytes,descriptor,rxFrame,low,capFrame,routeFrame,uart,one,two,future,three⟩ :=
    RuntimeResponseTail.contract c ram response.state 0x80ffffc7#32 response.payload response.mime (MainResponseExtractedReply.pointer json) response.status close
      h.pc h.spWord h.fpWord h.one h.stack h.app h.invariant h.bodyBound h.statusHi h.mimePointer h.mimeLength h.payloadLength
      h.statusWord h.zero h.objectArg h.minusTwo h.payload h.replyCapacity h.serve.tx h.serve.txCapacity h.serve.uart h.closeByte
  obtain ⟨d,call,entry,resultArg,objArg,returnAddress,regs,csrD⟩ := SendCaller.contract B a after sp 0x80fff878#32 spWord objectArg pc
  have finalSp := (regs 2 (by decide) (by decide) (by decide)).trans spWord
  have result : d.get 10=0x80fffd38#32 := by simpa only [show sp+4520#32=0x80fffd38#32 by decide +kernel] using resultArg
  have source : ReadBytes.Span B img after (MainResponseExtractedReply.pointer json) response.mime := by
    rw [h.mime]
    cases json
    · exact ReadBytes.of_ram (Bytes.empty B after 1#32)
    · exact ResponseLiterals.json after
  have input := MainSend.input d after 0x80ffffc7#32 (MainResponseExtractedReply.pointer json) response.status response.mime response.payload close headOnly
    entry finalSp result objArg h.stack h.bodyBound h.statusLo h.statusHi
    (by rw [h.mime];cases json <;> decide +kernel)
    (by rw [h.mime];cases json;intro b hb;cases hb;exact ResponseHeadSpec.json_field)
    (by simpa only [h.method] using descriptor) bytes source
    (WordRegions.before _ _ _ _ (by rw [h.mime];cases json <;> decide +kernel) (by decide))
    (WordRegions.before _ _ _ _ (by rw [h.mime];cases json <;> decide +kernel) (by decide))
    (WordRegions.before _ _ _ _ (by rw [h.mime];cases json <;> decide +kernel) (by decide))
  have memory := LoopTransactionMemory.preserve h.metadata low capFrame routeFrame
  have serve := MainServeLayout.preserve (MainServeLayout.region (ViewFrame.shrink low (by decide))) h.serve
  exact ⟨d,after,tail.trans call,input,finalSp,(regs 8 (by decide) (by decide) (by decide)).trans fpWord,
    (regs 19 (by decide) (by decide) (by decide)).trans (uart.trans h.uart),
    (regs 22 (by decide) (by decide) (by decide)).trans (one.trans h.one),
    (regs 18 (by decide) (by decide) (by decide)).trans (two.trans h.two),
    (regs 24 (by decide) (by decide) (by decide)).trans minusTwo,
    (regs 23 (by decide) (by decide) (by decide)).trans (future.trans h.future),
    (regs 26 (by decide) (by decide) (by decide)).trans (three.trans h.three),returnAddress,
    (congrArg Prod.fst (csrD.trans csr)).trans h.masked,app,h.invariant,h.stack,serve,h.room,memory⟩
/-- The actual write return enters three instructions before the common
    response tail; its flag store and capacity guard are included. -/
theorem prepare_extracted {c ram response served used json close headOnly}
    (h : Ready c ram response served used json close headOnly 0x80001710#32) :
    ∃ d after,Quiet.Steps B img 29 ⟨c,ram⟩ ⟨d,after⟩ ∧ NormalSendPhase.Ready d after response served used json close headOnly := by
  obtain ⟨a,after,tail,pc,spWord,fpWord,objectArg,minusTwo,csr,app,inv,bytes,descriptor,rxFrame,low,capFrame,routeFrame,uart,one,two,future,three⟩ :=
    LoopResponseExtracted.contract c ram response.state 0x80ffffc7#32 response.payload response.mime (MainResponseExtractedReply.pointer json) response.status close
      h.pc h.spWord h.fpWord h.one h.stack h.app h.invariant h.bodyBound h.statusHi h.mimePointer h.mimeLength h.payloadLength
      h.statusWord h.zero h.objectArg h.minusTwo h.payload h.replyCapacity h.serve.tx h.serve.txCapacity h.serve.uart h.closeByte
  obtain ⟨d,call,entry,resultArg,objArg,returnAddress,regs,csrD⟩ := SendCaller.contract B a after sp 0x80fff878#32 spWord objectArg pc
  have finalSp := (regs 2 (by decide) (by decide) (by decide)).trans spWord
  have result : d.get 10=0x80fffd38#32 := by simpa only [show sp+4520#32=0x80fffd38#32 by decide +kernel] using resultArg
  have source : ReadBytes.Span B img after (MainResponseExtractedReply.pointer json) response.mime := by
    rw [h.mime]
    cases json
    · exact ReadBytes.of_ram (Bytes.empty B after 1#32)
    · exact ResponseLiterals.json after
  have input := MainSend.input d after 0x80ffffc7#32 (MainResponseExtractedReply.pointer json) response.status response.mime response.payload close headOnly
    entry finalSp result objArg h.stack h.bodyBound h.statusLo h.statusHi
    (by rw [h.mime];cases json <;> decide +kernel)
    (by rw [h.mime];cases json;intro b hb;cases hb;exact ResponseHeadSpec.json_field)
    (by simpa only [h.method] using descriptor) bytes source
    (WordRegions.before _ _ _ _ (by rw [h.mime];cases json <;> decide +kernel) (by decide))
    (WordRegions.before _ _ _ _ (by rw [h.mime];cases json <;> decide +kernel) (by decide))
    (WordRegions.before _ _ _ _ (by rw [h.mime];cases json <;> decide +kernel) (by decide))
  have memory := LoopTransactionMemory.preserve h.metadata low capFrame routeFrame
  have serve := MainServeLayout.preserve (MainServeLayout.region (ViewFrame.shrink low (by decide))) h.serve
  exact ⟨d,after,tail.trans call,input,finalSp,(regs 8 (by decide) (by decide) (by decide)).trans fpWord,
    (regs 19 (by decide) (by decide) (by decide)).trans (uart.trans h.uart),
    (regs 22 (by decide) (by decide) (by decide)).trans (one.trans h.one),
    (regs 18 (by decide) (by decide) (by decide)).trans (two.trans h.two),
    (regs 24 (by decide) (by decide) (by decide)).trans minusTwo,
    (regs 23 (by decide) (by decide) (by decide)).trans (future.trans h.future),
    (regs 26 (by decide) (by decide) (by decide)).trans (three.trans h.three),returnAddress,
    (congrArg Prod.fst (csrD.trans csr)).trans h.masked,app,h.invariant,h.stack,serve,h.room,memory⟩
/-- Independent response correspondence and exact queued bytes remain
    explicit until the exhaustive router/handler preparation proves them. -/
def At (c : Core) (ram : Word → BitVec 8) (g : ProtocolStreamSpec.State) : Prop :=
  ∃ response served used json close headOnly,Ready c ram response served used json close headOnly ∧
    NormalSendPhase.Pending response served close g ∧ ∃ p,g.phase=.reply p ∧
      p.remaining=ResponseHeadSpec.bytes response.status response.mime response.payload.length close++
        ResponseHeadSpec.body response.status headOnly response.payload

theorem enter {c ram g} (h : At c ram g) :
    ReactiveEnvelope.Envelope (fun m ghost => NormalSendPhase.Entry m.core m.ram ghost) ⟨c,ram⟩ g := by
  obtain ⟨response,served,used,json,close,headOnly,ready,family,pending,phase,queue⟩ := h
  obtain ⟨d,after,quiet,post⟩ := prepare ready
  exact ⟨ready.masked,26,⟨d,after⟩,quiet,response,served,used,json,close,headOnly,post,family,pending,phase,queue⟩
end E5R.Thermostat.NormalResponsePrepare
