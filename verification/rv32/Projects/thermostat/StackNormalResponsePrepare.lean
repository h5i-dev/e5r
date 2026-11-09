import Projects.thermostat.NormalResponsePrepare
import Projects.thermostat.StackAccess
import Projects.thermostat.StackRuntimeResponseTail
import Projects.thermostat.StackLoopResponseExtracted
set_option autoImplicit false
namespace E5R.Thermostat.StackNormalResponsePrepare
open E5R E5R.Thermostat NormalResponsePrepare
abbrev B := StackBoard.board
theorem prepare {c ram response served used json close headOnly}
    (h : Ready c ram response served used json close headOnly) :
    ∃ d after,Quiet.Steps B img 26 ⟨c,ram⟩ ⟨d,after⟩ ∧ NormalSendPhase.Ready d after response served used json close headOnly := by
  obtain ⟨a,after,tail,pc,spWord,fpWord,objectArg,minusTwo,csr,app,inv,bytes,descriptor,rxFrame,low,capFrame,routeFrame,uart,one,two,future,three⟩ :=
    StackRuntimeResponseTail.contract c ram response.state 0x80ffffc7#32 response.payload response.mime (MainResponseExtractedReply.pointer json) response.status close
      h.pc h.spWord h.fpWord h.one StackBoard.available h.app h.invariant h.bodyBound h.statusHi h.mimePointer h.mimeLength h.payloadLength
      h.statusWord h.zero h.objectArg h.minusTwo h.payload h.replyCapacity h.serve.tx h.serve.txCapacity h.serve.uart h.closeByte
  obtain ⟨d,call,entry,resultArg,objArg,returnAddress,regs,csrD⟩ := SendCaller.contract B a after sp 0x80fff878#32 spWord objectArg pc
  have finalSp := (regs 2 (by decide) (by decide) (by decide)).trans spWord
  have result : d.get 10=0x80fffd38#32 := by simpa only [show sp+4520#32=0x80fffd38#32 by decide +kernel] using resultArg
  have source : ReadBytes.Span UartPlatform.board img after (MainResponseExtractedReply.pointer json) response.mime := by
    rw [h.mime]
    cases json
    · exact ReadBytes.of_ram (Bytes.empty UartPlatform.board after 1#32)
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
    StackLoopResponseExtracted.contract c ram response.state 0x80ffffc7#32 response.payload response.mime (MainResponseExtractedReply.pointer json) response.status close
      h.pc h.spWord h.fpWord h.one StackBoard.available h.app h.invariant h.bodyBound h.statusHi h.mimePointer h.mimeLength h.payloadLength
      h.statusWord h.zero h.objectArg h.minusTwo h.payload h.replyCapacity h.serve.tx h.serve.txCapacity h.serve.uart h.closeByte
  obtain ⟨d,call,entry,resultArg,objArg,returnAddress,regs,csrD⟩ := SendCaller.contract B a after sp 0x80fff878#32 spWord objectArg pc
  have finalSp := (regs 2 (by decide) (by decide) (by decide)).trans spWord
  have result : d.get 10=0x80fffd38#32 := by simpa only [show sp+4520#32=0x80fffd38#32 by decide +kernel] using resultArg
  have source : ReadBytes.Span UartPlatform.board img after (MainResponseExtractedReply.pointer json) response.mime := by
    rw [h.mime]
    cases json
    · exact ReadBytes.of_ram (Bytes.empty UartPlatform.board after 1#32)
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
end E5R.Thermostat.StackNormalResponsePrepare
