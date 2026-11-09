import Projects.thermostat.ChunkCallerRefill
import Projects.thermostat.ChunkCallerBuffered
import Projects.thermostat.MainChunkWaitSafety
set_option autoImplicit false
namespace E5R.Thermostat.ChunkReactive
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board

/-- All real loop data, with the PC separated for the intervening UART phases.
    This does not identify filled/read/written or forget changing filledWord. -/
def Live (c : Core) (ram : Word → BitVec 8) (sp : Word) (start read written filled : Nat) (decoder : CState) :=
  MainChunkLoopInvariant.At B (c.goto 0x80000e9a#32) ram sp start read written filled decoder

structure Polling (c : Core) (ram : Word → BitVec 8) (sp : Word) (start read written filled : Nat) (decoder : CState) : Prop where
  waiting : MainChunkWaitSafety.Waiting c
  live : Live c ram sp start read written filled decoder
  dst : c.get 10=(sp+132#32)+BitVec.ofNat 32 filled
  empty : read=filled
  room : filled<2048

/-- Real exhausted-buffer guard and receive-descriptor stores up to the LSR
    load, retaining the caller object fragments, bank and immutable words. -/
theorem setup {c ram sp start read written filled decoder}
    (h : MainChunkLoopInvariant.At B c ram sp start read written filled decoder)
    (empty : read=filled) (room : filled<2048) :
    ∃ d after,Quiet.Steps B img 14 ⟨c,ram⟩ ⟨d,after⟩ ∧
      Polling d after sp start read written filled decoder ∧
      ViewFrame.Region ram after (sp+132#32) filled ∧ ChunkCallerFrame.At c d ram after sp := by
  let fw := BitVec.ofNat 32 filled
  let io := ramRead ram (sp+3644#32) .w
  have fval : fw.toNat=filled := by simp only [fw,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : filled<2^32)]
  have fbound : fw.toNat<2048 := by rw [fval];exact room
  obtain ⟨a,guard,pc1,val,regsA,csrA⟩ := MainChunkExhausted.contract B c ram sp fw h.framePtr (by simpa only [empty] using h.cursor)
    h.stack h.align h.layout.filledPtr h.filledWord h.pc
  obtain ⟨d,stores,pc2,cap,rx,ioWord,dst,regsD,csrD⟩ := MainChunkReceiveSetup.contract B a ram sp fw io
    ((regsA 8 (by decide)).trans h.framePtr) val h.stack h.align h.layout.capacity h.layout.rx rfl fbound pc1
  let after := MainChunkReceiveSetup.memory ram sp fw io
  have kept (r : Reg) (h10 : r≠10) (h11 : r≠11) (h12 : r≠12) (h13 : r≠13) : d.get r=c.get r :=
    (regsD r h11 h12 h13 h10).trans (regsA r h10)
  have word (off : Nat) (bound : off+4≤3664) : ramRead after (sp+BitVec.ofNat 32 off) .w=ramRead ram (sp+BitVec.ofNat 32 off) .w :=
    MainChunkReceiveMemory.setup_word ram sp fw io off (by omega) (Or.inl bound)
  have live : Live d after sp start read written filled decoder := by
    refine ⟨rfl,(kept 2 (by decide) (by decide) (by decide) (by decide)).trans h.stackPtr,
      (kept 8 (by decide) (by decide) (by decide) (by decide)).trans h.framePtr,
      (kept 23 (by decide) (by decide) (by decide) (by decide)).trans h.statePtr,
      (kept 24 (by decide) (by decide) (by decide) (by decide)).trans h.cursor,
      (kept 22 (by decide) (by decide) (by decide) (by decide)).trans h.one,
      (kept 19 (by decide) (by decide) (by decide) (by decide)).trans h.uart,
      (congrArg Prod.fst (csrD.trans csrA)).trans h.masked,h.stack,h.align,
      ⟨(word 3312 (by decide)).trans h.layout.rx,(word 3316 (by decide)).trans h.layout.capacity,
       (word 3636 (by decide)).trans h.layout.limits,(word 3284 (by decide)).trans h.layout.maxBody,(word 3640 (by decide)).trans h.layout.filledPtr⟩,
      (word 3288 (by decide)).trans h.filledWord,(word 3656 (by decide)).trans h.readWord,(word 3660 (by decide)).trans h.writeWord,
      ChunkStateFrame.preserve h.object (MainChunkReceiveMemory.setup_region ram sp fw io 3680 25 (by decide) (Or.inr (by decide))),
      h.decoder,h.startWritten,h.writtenRead,h.readFilled,h.capacity⟩
  have core : MainChunkCoreFrame.At c d := by
    intro r safe
    have ne : ∀ rr : Reg,MainChunkCoreFrame.Kept rr → rr≠10 ∧ rr≠11 ∧ rr≠12 ∧ rr≠13 := by decide +kernel
    obtain ⟨a,b,e,f⟩ := ne r safe
    exact kept r a b e f
  have frame : ChunkCallerFrame.At c d ram after sp := by
    refine ⟨core,?_,?_,?_,?_,csrD.trans csrA⟩
    · simpa only [BitVec.add_zero] using MainChunkReceiveMemory.setup_region ram sp fw io 0 132 (by decide) (Or.inl (by decide))
    · intro off member
      have bounds := MainServeLayout.bounds off member
      simpa only [BitVec.ofNat_add,BitVec.add_assoc] using word (3204+off) (by omega)
    · exact MainChunkReceiveMemory.setup_region ram sp fw io 3204 84 (by decide) (Or.inl (by decide))
    · exact MainChunkReceiveMemory.setup_region ram sp fw io 3292 364 (by decide) (Or.inl (by decide))
  refine ⟨d,after,guard.trans stores,⟨Or.inl pc2,live,dst.trans (BitVec.add_comm _ _),empty,room⟩,?_,frame⟩
  exact MainChunkReceiveMemory.setup_region ram sp fw io 132 filled (by omega) (Or.inl (by omega))


/-- LSR/RBR loads change a1 only, preserving every decoder/layout prerequisite. -/
theorem recore {c d ram sp start read written filled decoder} (h : Live c ram sp start read written filled decoder)
    (regs : ∀ r : Reg,r≠11 → d.get r=c.get r) (masked : d.mie_=false) : Live d ram sp start read written filled decoder :=
  ⟨rfl,(regs 2 (by decide)).trans h.stackPtr,(regs 8 (by decide)).trans h.framePtr,
    (regs 23 (by decide)).trans h.statePtr,(regs 24 (by decide)).trans h.cursor,
    (regs 22 (by decide)).trans h.one,(regs 19 (by decide)).trans h.uart,masked,h.stack,h.align,
    h.layout,h.filledWord,h.readWord,h.writeWord,h.object,h.decoder,h.startWritten,h.writtenRead,h.readFilled,h.capacity⟩

structure Rbr (c : Core) (ram : Word → BitVec 8) (sp : Word) (start read written filled : Nat) (decoder : CState) : Prop where
  pc : c.pc=0x80000e80#32
  live : Live c ram sp start read written filled decoder
  dst : c.get 10=(sp+132#32)+BitVec.ofNat 32 filled
  empty : read=filled
  room : filled<2048

structure AfterRbr (c : Core) (ram : Word → BitVec 8) (sp : Word) (start read written filled : Nat) (decoder : CState) : Prop where
  pc : c.pc=0x80000e84#32
  live : Live c ram sp start read written filled decoder
  dst : c.get 10=(sp+132#32)+BitVec.ofNat 32 filled
  empty : read=filled
  room : filled<2048

theorem polling_next {c ram sp start read written filled decoder} (h : Polling c ram sp start read written filled decoder) (o : Oracle) :
    ∃ d reads,Observed.stepInstr B img ⟨c,ram⟩ o=⟨.ok d ram [],reads⟩ ∧
      (Polling d ram sp start read written filled decoder ∨ Rbr d ram sp start read written filled decoder) ∧
      MainChunkWaitSafety.LsrOnly reads ∧ MainChunkCoreFrame.At c d ∧ d.sameCsr c := by
  obtain ⟨d,reads,step,post,only,regs,csr⟩ := MainChunkWaitSafety.next ram ⟨h.waiting,h.live.uart,h.live.masked⟩ o
  have live := recore h.live regs ((congrArg Prod.fst csr).trans h.live.masked)
  have dst := (regs 10 (by decide)).trans h.dst
  refine ⟨d,reads,step,?_,only,?_,csr⟩
  · rcases post with waiting|exit
    · exact Or.inl ⟨waiting.1,live,dst,h.empty,h.room⟩
    · exact Or.inr ⟨exit.1,live,dst,h.empty,h.room⟩
  · intro r kept
    have ne : ∀ rr : Reg,MainChunkCoreFrame.Kept rr → rr≠11 := by decide +kernel
    exact regs r (ne r kept)

theorem rbr_next {c ram sp start read written filled decoder} (h : Rbr c ram sp start read written filled decoder) (o : Oracle) :
    let d := c.wr 11 (UartPoll.byte (o 0)) 0x80000e84#32
    Observed.stepInstr B img ⟨c,ram⟩ o=⟨.ok d ram [],[⟨0x10000000#32,.b,UartPoll.byte (o 0),0⟩]⟩ ∧
      AfterRbr d ram sp start read written filled decoder ∧ MainChunkCoreFrame.At c d ∧ d.sameCsr c := by
  refine ⟨MainChunkRbr.load c ram o h.pc h.live.uart,⟨rfl,?_,?_,h.empty,h.room⟩,?_,rfl⟩
  · exact recore h.live (fun r ne => Core.wr_get_ne _ _ _ _ _ ne) h.live.masked
  · exact (Core.wr_get_ne _ _ _ _ _ (by decide : (10 : Reg)≠11)).trans h.dst
  · intro r kept
    have ne : ∀ rr : Reg,MainChunkCoreFrame.Kept rr → rr≠11 := by decide +kernel
    exact Core.wr_get_ne _ _ _ _ _ (ne r kept)

/-- Seven actual quiet instructions store the byte and update filled only.
    Read/write/decoder state stay distinct; caller framing omits filledWord. -/
theorem after_rbr {c ram sp start read written filled decoder} (h : AfterRbr c ram sp start read written filled decoder) :
    ∃ d after,Quiet.Steps B img 7 ⟨c,ram⟩ ⟨d,after⟩ ∧
      MainChunkLoopInvariant.At B d after sp start read written (filled+1) decoder ∧
      ViewFrame.Region ram after (sp+132#32) filled ∧
      after ((sp+132#32)+BitVec.ofNat 32 filled)=(c.get 11).setWidth 8 ∧ ChunkCallerFrame.At c d ram after sp := by
  let fw := BitVec.ofNat 32 filled
  let rw := BitVec.ofNat 32 read
  have room := h.room
  have fval : fw.toNat=filled := by simp only [fw,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : filled<2^32)]
  have fbound : fw.toNat<2048 := by rw [fval];exact room
  obtain ⟨d,tail,pc,v10,v11,v24,regs,csr⟩ := MainChunkReceiveTail.contract B c ram sp fw rw (c.get 11)
    h.live.framePtr h.dst rfl h.live.one h.live.stack h.live.align fbound h.live.layout.filledPtr h.live.filledWord h.live.readWord h.pc
  let after := MainChunkReceiveTail.memory ram sp fw rw (c.get 11)
  have word (off : Nat) (lo : 2180≤off) (hi : off+4≤3676) (apart : off+4≤3288 ∨ 3292≤off) :
      ramRead after (sp+BitVec.ofNat 32 off) .w=ramRead ram (sp+BitVec.ofNat 32 off) .w :=
    MainChunkReceiveMemory.tail_word ram sp fw rw (c.get 11) off fbound (by omega) lo (Or.inl hi) apart
  have live : MainChunkLoopInvariant.At B d after sp start read written (filled+1) decoder := by
    refine ⟨pc,(regs 2 (by decide) (by decide) (by decide)).trans h.live.stackPtr,
      (regs 8 (by decide) (by decide) (by decide)).trans h.live.framePtr,
      (regs 23 (by decide) (by decide) (by decide)).trans h.live.statePtr,v24,
      (regs 22 (by decide) (by decide) (by decide)).trans h.live.one,
      (regs 19 (by decide) (by decide) (by decide)).trans h.live.uart,
      (congrArg Prod.fst csr).trans h.live.masked,h.live.stack,h.live.align,
      ⟨(word 3312 (by decide) (by decide) (Or.inr (by decide))).trans h.live.layout.rx,
       (word 3316 (by decide) (by decide) (Or.inr (by decide))).trans h.live.layout.capacity,
       (word 3636 (by decide) (by decide) (Or.inr (by decide))).trans h.live.layout.limits,
       (word 3284 (by decide) (by decide) (Or.inl (by decide))).trans h.live.layout.maxBody,
       (word 3640 (by decide) (by decide) (Or.inr (by decide))).trans h.live.layout.filledPtr⟩,
      ?_,(word 3656 (by decide) (by decide) (Or.inr (by decide))).trans h.live.readWord,
      (word 3660 (by decide) (by decide) (Or.inr (by decide))).trans h.live.writeWord,
      ChunkStateFrame.preserve h.live.object (MainChunkReceiveMemory.tail_region ram sp fw rw (c.get 11) 3680 25 fbound
        (by decide) (by omega) (Or.inr (by decide)) (Or.inr (by decide))),
      h.live.decoder,h.live.startWritten,h.live.writtenRead,by have := h.live.readFilled;omega,by omega⟩
    simpa only [BitVec.ofNat_add] using MainChunkReceiveMemory.tail_filled ram sp fw rw (c.get 11)
  have core : MainChunkCoreFrame.At c d := by
    intro r kept
    have ne : ∀ rr : Reg,MainChunkCoreFrame.Kept rr → rr≠10 ∧ rr≠11 ∧ rr≠24 := by decide +kernel
    obtain ⟨a,b,e⟩ := ne r kept
    exact regs r a b e
  have frame : ChunkCallerFrame.At c d ram after sp := by
    refine ⟨core,?_,?_,?_,?_,csr⟩
    · simpa only [BitVec.add_zero] using MainChunkReceiveMemory.tail_region ram sp fw rw (c.get 11) 0 132 fbound
        (by decide) (Or.inl (by omega)) (Or.inl (by decide)) (Or.inl (by decide))
    · intro off member
      have bounds := MainServeLayout.bounds off member
      have apart : 3204+off+4≤3288 ∨ 3292≤3204+off := by rcases bounds.2 with a|a <;> omega
      simpa only [BitVec.ofNat_add,BitVec.add_assoc] using word (3204+off) (by omega) (by omega) apart
    · exact MainChunkReceiveMemory.tail_region ram sp fw rw (c.get 11) 3204 84 fbound (by decide) (by omega) (Or.inl (by decide)) (Or.inl (by decide))
    · exact MainChunkReceiveMemory.tail_region ram sp fw rw (c.get 11) 3292 364 fbound (by decide) (by omega) (Or.inl (by decide)) (Or.inr (by decide))
  refine ⟨d,after,tail,live,?_,?_,frame⟩
  · simpa only [fval] using MainChunkReceiveMemory.tail_region ram sp fw rw (c.get 11) 132 fw.toNat fbound
      (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
  · exact (MainChunkReceiveMemory.tail_stored ram sp fw rw (c.get 11) fbound).trans (UartPoll.byteOf_zero _)


/-- One actual arbitrary RBR byte, its real store, and in-place decoder refine
    exactly one pure byte step, including Nothing/Data/Done/Reject. This closes
    the phase join without assuming that the chunked request will complete. -/
theorem consume_byte {c ram sp start read written filled decoder body}
    (h : AfterRbr c ram sp start read written filled decoder)
    (hb : ChunkBufferView.Body ram sp start body) (length : written=start+body.length) :
    let byte := (c.get 11).setWidth 8
    let r := ChunkBufferSpec.consume (fun _ => byte) 1 read written decoder body
    ∃ n d after,n≤132 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      MainChunkBuffered.Boundary B d after sp start (filled+1) r ∧ ChunkBufferView.Body after sp start r.body ∧
      ViewFrame.Region ram after (sp+132#32) start ∧ d.get 24=BitVec.ofNat 32 r.read ∧
      ramRead after (sp+3288#32) .w=BitVec.ofNat 32 (filled+1) ∧ ChunkCallerFrame.At c d ram after sp := by
  obtain ⟨a,mid,store,live,rx,stored,firstFrame⟩ := after_rbr h
  have startBound : start≤filled := by
    have := h.live.writtenRead
    have := h.empty
    omega
  have body2 : ChunkBufferView.Body mid sp start body := by
    intro i
    rw [ChunkBufferView.address,rx ⟨start+i.val,by have := i.isLt;have := h.live.writtenRead;have := h.empty;omega⟩]
    simpa only [ChunkBufferView.address] using hb i
  have unread : ChunkBufferView.Unread (fun _ => (c.get 11).setWidth 8) mid sp read (filled+1) := by
    intro k lo hi
    have eq : k=filled := by have := h.empty;omega
    subst k
    exact stored
  obtain ⟨n,d,after,bound,decode,post,bodyAfter,unreadAfter,app,header,cursor,filledAfter,lastFrame⟩ :=
    ChunkCallerBuffered.contract (fun _ => (c.get 11).setWidth 8) 1 live (by have := h.empty;omega) unread body2 length
  exact ⟨7+n,d,after,by omega,store.trans decode,post,bodyAfter,
    HeadRegionFrame.trans (ViewFrame.shrink rx startBound) header,cursor,filledAfter,ChunkCallerFrame.trans firstFrame lastFrame⟩
end E5R.Thermostat.ChunkReactive
