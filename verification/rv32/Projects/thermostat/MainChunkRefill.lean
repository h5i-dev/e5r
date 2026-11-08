import Projects.thermostat.MainChunkExhausted
import Projects.thermostat.MainChunkRefillFrame
import Projects.thermostat.MainChunkWait
import Projects.thermostat.MainChunkRbr
import Projects.thermostat.MainChunkLoopInvariant
import Projects.thermostat.MainChunkLoopStep
namespace E5R.Thermostat.MainChunkRefill
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

def reads (pending : List Word) (ready datum : Word) : List Observed.Read :=
  MainChunkWait.reads (pending++[ready])++[⟨0x10000000#32,.b,UartPoll.byte datum,0⟩]

/-- A finite readiness certificate advances an exhausted body buffer by one
    actual RBR byte and returns to the body-loop invariant. -/
theorem contract {c ram sp start read written filled s}
    (h : MainChunkLoopInvariant.At B c ram sp start read written filled s)
    (empty : read=filled) (space : filled<2048)
    (pending : List Word) (ready datum : Word)
    (hn : ∀ status ∈ pending, MainChunkPoll.mask status=0#32)
    (hr : MainChunkPoll.mask ready≠0#32) :
    ∃ d after, Observed.Steps B img (25+5*pending.length) ⟨c,ram⟩ ⟨d,after⟩
      (reads pending ready datum) [] ∧
      MainChunkLoopInvariant.At B d after sp start read written (filled+1) s ∧
      ViewFrame.Region ram after (sp+132#32) filled ∧
      after ((sp+132#32)+BitVec.ofNat 32 filled)=(UartPoll.byte datum).setWidth 8 ∧
      MainChunkLoopStep.AppFrame ram after sp := by
  let fw := BitVec.ofNat 32 filled
  let rw := BitVec.ofNat 32 read
  let io := ramRead ram (sp+3644#32) .w
  have fval : fw.toNat=filled := by change (BitVec.ofNat 32 filled).toNat=filled;rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have fbound : fw.toNat<2048 := by rw [fval];exact space
  obtain ⟨a,guard,pc1,val,frame1,csr1⟩ := MainChunkExhausted.contract B c ram sp fw
    h.framePtr (by simpa only [empty] using h.cursor) h.stack h.align h.layout.filledPtr h.filledWord h.pc
  obtain ⟨b,setup,pc2,cap2,rx2,io2,dst2,frame2,csr2⟩ := MainChunkReceiveSetup.contract B a ram sp fw io
    ((frame1 8 (by decide)).trans h.framePtr) val h.stack h.align h.layout.capacity h.layout.rx rfl fbound pc1
  let buf := MainChunkReceiveSetup.memory ram sp fw io
  have uart : b.get 19=0x10000000#32 :=
    (frame2 19 (by decide) (by decide) (by decide) (by decide)).trans ((frame1 19 (by decide)).trans h.uart)
  obtain ⟨e,wait,pc3,frame3,csr3⟩ := MainChunkWait.contract b buf pending ready pc2 uart hn hr
  let rbr := e.wr 11 (UartPoll.byte datum) 0x80000e84#32
  have uart3 : e.get 19=0x10000000#32 := (frame3 19 (by decide)).trans uart
  have input := MainChunkRbr.step e buf datum pc3 uart3
  have old8 : rbr.get 8=sp+3204#32 := by
    dsimp only [rbr]
    rw [Core.wr_get_ne _ _ _ _ _ (by decide)]
    exact (frame3 8 (by decide)).trans ((frame2 8 (by decide) (by decide) (by decide) (by decide)).trans ((frame1 8 (by decide)).trans h.framePtr))
  have old10 : rbr.get 10=(sp+132#32)+fw := by
    dsimp only [rbr]
    rw [Core.wr_get_ne _ _ _ _ _ (by decide)]
    exact ((frame3 10 (by decide)).trans dst2).trans (BitVec.add_comm _ _)
  have old22 : rbr.get 22=1#32 := by
    dsimp only [rbr]
    rw [Core.wr_get_ne _ _ _ _ _ (by decide)]
    exact (frame3 22 (by decide)).trans ((frame2 22 (by decide) (by decide) (by decide) (by decide)).trans ((frame1 22 (by decide)).trans h.one))
  have framed (off : Nat) (hb : off+4≤3664) :
      ramRead buf (sp+BitVec.ofNat 32 off) .w=ramRead ram (sp+BitVec.ofNat 32 off) .w :=
    MainChunkReceiveMemory.setup_word ram sp fw io off (by omega) (Or.inl hb)
  obtain ⟨d,tail,pc4,v10,v11,v24,frame4,csr4⟩ := MainChunkReceiveTail.contract B rbr buf sp fw rw (UartPoll.byte datum)
    old8 old10 (by simp [rbr,Core.wr_get]) old22 h.stack h.align fbound
    ((framed 3640 (by decide)).trans h.layout.filledPtr)
    ((framed 3288 (by decide)).trans h.filledWord)
    ((framed 3656 (by decide)).trans h.readWord) rfl
  let after := MainChunkRefillFrame.memory ram sp fw rw (UartPoll.byte datum) io
  have kept (r : Reg) (h10 : r≠10) (h11 : r≠11) (h12 : r≠12) (h13 : r≠13) (h24 : r≠24) : d.get r=c.get r := by
    exact (frame4 r h10 h11 h24).trans ((Core.wr_get_ne e 11 r (UartPoll.byte datum) 0x80000e84#32 h11).trans
      ((frame3 r h11).trans ((frame2 r h11 h12 h13 h10).trans (frame1 r h10))))
  have mask : d.mie_=false := MainChunkCoreFrame.masked (csr4.trans (show rbr.sameCsr e from rfl))
    (MainChunkCoreFrame.masked csr3 (MainChunkCoreFrame.masked csr2 (MainChunkCoreFrame.masked csr1 h.masked)))
  have trace := (((guard.observed.trans setup.observed).trans wait).trans (.single input)).trans tail.observed
  refine ⟨d,after,?_,?_,?_,?_,?_⟩
  · have count : ((3+11)+(5*pending.length+3)+1)+7=25+5*pending.length := by omega
    rw [count] at trace
    simpa only [reads,List.nil_append,List.append_nil,after,MainChunkRefillFrame.memory,buf] using trace
  · constructor
    · exact pc4
    · exact (kept 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.stackPtr
    · exact (kept 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.framePtr
    · exact (kept 23 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.statePtr
    · exact v24
    · exact (kept 22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.one
    · exact (kept 19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.uart
    · exact mask
    · exact h.stack
    · exact h.align
    · exact MainChunkRefillFrame.layout fbound h.layout
    · simpa only [BitVec.ofNat_add] using MainChunkRefillFrame.filled ram sp fw rw (UartPoll.byte datum) io
    · exact (MainChunkRefillFrame.word ram sp fw rw (UartPoll.byte datum) io 3656 fbound (by decide) (by decide) (by decide) (by decide)).trans h.readWord
    · exact (MainChunkRefillFrame.word ram sp fw rw (UartPoll.byte datum) io 3660 fbound (by decide) (by decide) (by decide) (by decide)).trans h.writeWord
    · exact MainChunkRefillFrame.state fbound h.object
    · exact h.decoder
    · exact h.startWritten
    · exact h.writtenRead
    · have := h.readFilled;omega
    · omega
  · simpa only [fval] using MainChunkRefillFrame.rx_before ram sp fw rw (UartPoll.byte datum) io fbound
  · exact (MainChunkRefillFrame.stored ram sp fw rw (UartPoll.byte datum) io fbound).trans (UartPoll.byteOf_zero _)
  · intro he state hs
    have actual : after=MainChunkRefillFrame.memory ram 0x80ffeb90#32 fw rw (UartPoll.byte datum) io := by
      unfold after;rw [he]
    rw [actual]
    exact MainChunkRefillFrame.app ram fw rw (UartPoll.byte datum) io state fbound hs
end E5R.Thermostat.MainChunkRefill
