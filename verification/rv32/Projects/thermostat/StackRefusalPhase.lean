import Projects.thermostat.RefusalPhase
import Projects.thermostat.StackPhaseEnvelope
import Projects.thermostat.ChunkStackFrame
set_option autoImplicit false
namespace E5R.Thermostat.StackRefusalPhase
open E5R E5R.Thermostat HttpRequestSpec RefusalPhase
abbrev B := StackBoard.board
theorem setup {c ram s served status}
    (pc : c.pc=0x80001bbc#32) (spWord : c.get 2=sp) (fpWord : c.get 8=fp)
    (uart : c.get 19=0x10000000#32) (one : c.get 22=1#32) (tag : c.get 10=1#32)
    (error : c.get 27=BitVec.ofNat 32 status) (masked : c.mie_=false)
    (stack : Memory.Block UartPlatform.board 0x80ff0000#32 65536) (app : AppState.At ram s) (inv : Spec.Inv s)
    (caller : HeaderPhase.Caller c ram served) (lo : 200≤status) (hi : status≤599) :
    ∃ d after,Quiet.Steps B img 24 ⟨c,ram⟩ ⟨d,after⟩ ∧ Ready d after s served status := by
  have object : Memory.Block B fp 148 := by
    have part := Memory.sub_block StackBoard.available (off := 63508) (m := 148) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+63508#32=fp by decide +kernel] using part
  let mid := RejectResponseSetup.memory ram 0x80ffffc7#32 (BitVec.ofNat 32 status)
  obtain ⟨a,setup,apc,_,a24,a18,a10,a11,_,a1,ar,ac⟩ := RejectResponseSetup.contract B c ram 0x80ffffc7#32 (BitVec.ofNat 32 status)
    spWord fpWord one tag error caller.serve.tx caller.serve.txCapacity caller.serve.uart object pc
  have a2 := (ar 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans spWord
  have a8 := (ar 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans fpWord
  have a19 := (ar 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans uart
  have a22 := (ar 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans one
  have aBank : MainGprBank.At a := MainGprBank.preserve (fun r mem => by
    have ne : ∀ r : Reg, r∈[21,23,26] → r≠9 ∧ r≠24 ∧ r≠18 ∧ r≠10 ∧ r≠11 ∧ r≠12 ∧ r≠1 := by decide +kernel
    obtain ⟨n9,n24,n18,n10,n11,n12,n1⟩ := ne r mem
    exact ar r n9 n24 n18 n10 n11 n12 n1) caller.bank
  have desc := RejectResponseView.descriptor ram 0x80ffffc7#32 status hi
  have pre := MainSend.input a mid 0x80ffffc7#32 1#32 status [] [] true false apc a2 a10 a11 stack (by decide) lo hi
    (by decide) (by intro b mem;cases mem) desc (Bytes.empty UartPlatform.board mid _) (ReadBytes.of_ram (Bytes.empty UartPlatform.board mid _))
    (WordRegions.before _ _ _ _ (by decide) (by decide)) (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
  have low := RejectResponseView.caller_frame ram 0x80ffffc7#32 (BitVec.ofNat 32 status)
  have serveFrame : ViewFrame.Region ram mid fp 92 := by
    simpa only [show sp+3204#32=fp by decide +kernel] using HeadRegionFrame.sub low 3204 92 (by decide)
  have finalCaller : HeaderPhase.Caller a mid served :=
    HeaderPhase.preserve_caller caller (fun r mem => by
      have ne : ∀ r : Reg,r∈[21,23,26] → r≠9 ∧ r≠24 ∧ r≠18 ∧ r≠10 ∧ r≠11 ∧ r≠12 ∧ r≠1 := by decide +kernel
      obtain ⟨a,b,c,d,e,f,g⟩ := ne r mem
      exact ar r a b c d e f g) (MainServeLayout.region serveFrame) (ViewFrame.shrink low (by decide))
  have appAfter : AppState.At mid s := AppState.preserve ram mid s app (by
    simpa only [ViewFrame.Region,show sp+44#32=0x80ffebbc#32 by decide +kernel] using HeadRegionFrame.sub low 44 25 (by decide))
  exact ⟨a,mid,setup,pre,a2,a8,a19,a22,a18,a24,a1,(congrArg Prod.fst ac).trans masked,appAfter,inv,stack,finalCaller⟩

/-- Real rejected Next packaging followed by refusal response construction. -/
theorem prepare {c ram s served status}
    (cut : MainHeaderDispatchTwo.At c (.reject status)) (spWord : c.get 2=sp) (fpWord : c.get 8=fp)
    (uart : c.get 19=0x10000000#32) (one : c.get 22=1#32) (masked : c.mie_=false)
    (stackAll : Memory.Block UartPlatform.board 0x80ff0000#32 65536) (appBefore : AppState.At ram s) (invariant : Spec.Inv s)
    (caller : HeaderPhase.Caller c ram served) (lo : 200≤status) (hi : status≤599) :
    ∃ d after,Quiet.Steps B img 780 ⟨c,ram⟩ ⟨d,after⟩ ∧ Ready d after s served status := by
  obtain ⟨pc,zero,error,variant⟩ := cut
  have stack : Memory.Block B sp 5232 := by
    have part := Memory.sub_block StackBoard.available (off := 60304) (m := 5232) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using part
  obtain ⟨a,next,apc,tag,regs,csr,frame⟩ := RejectNextCore.contract B c ram sp pc spWord fpWord variant zero caller.bank.minusOne one stack (by decide)
  let mid := RejectNextCore.memory ram sp
  have bankFrame : MainGprBank.Frame c a := fun r mem => by
    have subset : ∀ r : Reg,r∈[21,23,26] → r∈MainSavedGpr.regs := by decide +kernel
    exact regs r (subset r mem)
  have serveFrame : ViewFrame.Region ram mid fp 92 := by
    simpa only [show sp+3204#32=fp by decide +kernel] using HeadRegionFrame.sub frame 3204 92 (by decide)
  have finalCaller := HeaderPhase.preserve_caller caller bankFrame (MainServeLayout.region serveFrame) (ViewFrame.shrink frame (by decide))
  have app : AppState.At mid s := AppState.preserve ram mid s appBefore (by
    simpa only [ViewFrame.Region,show sp+44#32=0x80ffebbc#32 by decide +kernel] using HeadRegionFrame.sub frame 44 25 (by decide))
  obtain ⟨d,after,last,ready⟩ := setup apc ((regs 2 (by decide)).trans spWord) ((regs 8 (by decide)).trans fpWord)
    ((regs 19 (by decide)).trans uart) ((regs 22 (by decide)).trans one) tag ((regs 27 (by decide)).trans error)
    ((congrArg Prod.fst csr).trans masked) stackAll app invariant finalCaller lo hi
  exact ⟨d,after,next.trans last,ready⟩

theorem from_header {c ram s served original status}
    (boundary : MainHeaderLoopTwo.Boundary c ram original s (.reject status))
    (parsed : HttpRequestBytes.parse original 1024 1024=.reject status) (caller : HeaderPhase.Caller c ram served) :
    StackPhaseEnvelope.Envelope (fun m g => At m.core m.ram g) ⟨c,ram⟩ (HeaderPhase.classify s served original) := by
  obtain ⟨cut,stable,view⟩ := boundary
  obtain ⟨lo,hi⟩ := RejectStatus.bounds (RejectStatus.parse original 1024 1024 status parsed)
  obtain ⟨d,after,quiet,ready⟩ := prepare cut stable.sp stable.fp stable.uart stable.one stable.masked stable.stack stable.app stable.invariant caller lo hi
  exact ⟨stable.masked,780,⟨d,after⟩,quiet,s,served,status,ready,by simp only [HeaderPhase.classify,parsed];rfl⟩
theorem from_chunk_reject {c ram s served original head r status}
    (context : ChunkPhase.Context c ram s served original head)
    (terminal : MainChunkBuffered.Terminal ram sp head.len r c) (reject : r.stop=.reject status) :
    StackPhaseEnvelope.Envelope (fun m g => At m.core m.ram g) ⟨c,ram⟩ (ChunkPhase.classify s served original head r) := by
  obtain ⟨pc,obj,inv,readWord,writeWord,layout,stackPtr,masked,result⟩ := terminal
  rw [reject] at result
  obtain ⟨allowed,error,tag⟩ := result
  have lo : 200≤status := by rcases allowed with rfl|rfl <;> decide
  have hi : status≤599 := by rcases allowed with rfl|rfl <;> decide
  obtain ⟨a,branch,apc,a18,a9,regs,csr⟩ := ChunkRejectBranch.contract B c ram tag context.two pc
  have cut : MainHeaderDispatchTwo.At a (.reject status) := ⟨apc,a18,(regs 27 (by decide) (by decide)).trans error,a9⟩
  have bankFrame : MainGprBank.Frame c a := fun r member => by
    have ne : ∀ r : Reg,r∈[21,23,26] → r≠18 ∧ r≠9 := by decide +kernel
    obtain ⟨a,b⟩ := ne r member
    exact regs r a b
  have caller := HeaderPhase.preserve_caller context.caller bankFrame (MainServeLayout.refl ram) (fun _ => rfl)
  obtain ⟨d,after,quiet,ready⟩ := prepare cut ((regs 2 (by decide) (by decide)).trans stackPtr)
    ((regs 8 (by decide) (by decide)).trans context.frame) ((regs 19 (by decide) (by decide)).trans context.uart)
    ((regs 22 (by decide) (by decide)).trans context.one) ((congrArg Prod.fst csr).trans masked)
    context.stack context.app context.invariant caller lo hi
  exact ⟨masked,4+780,⟨d,after⟩,branch.trans quiet,s,served,status,ready,by simp only [ChunkPhase.classify,reject,ChunkPhase.error] <;> rfl⟩

theorem from_chunk_capacity {c ram g} (h : ChunkPhase.Capacity c ram g) :
    StackPhaseEnvelope.Envelope (fun m ghost => At m.core m.ram ghost) ⟨c,ram⟩ g := by
  obtain ⟨s,served,original,head,decoder,body,context,loop,payload,ghost⟩ := h
  obtain ⟨a,refusal,pc,error,tag,zero,csr,regs⟩ := MainChunkCapacityRefusal.contract (ChunkStackFrame.loop loop ChunkStackFrame.stack) rfl rfl
  have cut : MainHeaderDispatchTwo.At a (.reject 413) := ⟨pc,zero,error,tag⟩
  have bankFrame : MainGprBank.Frame c a := fun r member => by
    have ne : ∀ r : Reg,r∈[21,23,26] → r≠10 ∧ r≠11 ∧ r≠27 ∧ r≠9 ∧ r≠18 := by decide +kernel
    obtain ⟨a,b,c,d,e⟩ := ne r member
    exact regs r a b c d e
  have caller := HeaderPhase.preserve_caller context.caller bankFrame (MainServeLayout.refl ram) (fun _ => rfl)
  obtain ⟨d,after,quiet,ready⟩ := prepare cut ((regs 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans loop.stackPtr)
    ((regs 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans context.frame)
    ((regs 19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans context.uart)
    ((regs 22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans context.one)
    ((congrArg Prod.fst csr).trans loop.masked) context.stack context.app context.invariant caller (by decide) (by decide)
  exact ⟨loop.masked,9+780,⟨d,after⟩,refusal.trans quiet,s,served,413,ready,ghost⟩

end E5R.Thermostat.StackRefusalPhase
