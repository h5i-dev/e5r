import Projects.thermostat.HeaderByteStore
import Projects.thermostat.HeaderReparse
import Projects.thermostat.MainHeaderWaitSafety
set_option autoImplicit false
namespace E5R.Thermostat.HeaderReactive
open E5R E5R.Thermostat HttpRequestSpec MainHeaderLoopTwo
abbrev B := UartPlatform.board

structure AfterRbr (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (s : Spec.Snapshot) : Prop where
  pc : c.pc=0x80000bae#32
  stable : Stable c ram input s
  dst : c.get 12=rx+BitVec.ofNat 32 input.length
  room : input.length<2048
  two : c.get 18=2#32

/-- The quiet continuation of an arbitrary actual RBR byte reaches precisely
    the independent parser's boundary. Its whole strict instruction prefix is
    covered without assuming future readiness or parser success. -/
theorem after_rbr {c ram input s} (h : AfterRbr c ram input s) :
    let next := input++[(c.get 10).setWidth 8]
    ∃ n d after,Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      Boundary d after next s (HttpRequestBytes.parse next 1024 1024) ∧ d.sameCsr c ∧
      MainGprBank.Frame c d ∧ MainServeLayout.Frame ram after ∧ ViewFrame.Region ram after 0x80ffeb90#32 132 := by
  have room := h.room
  obtain ⟨a,mid,store,pc,count,layout,value,frame,regs,csr⟩ := HeaderByteStore.contract c ram input.length h.pc h.stable.fp h.stable.uart h.stable.one h.dst h.stable.layout h.room h.stable.stack
  have app : AppState.At mid s := AppState.preserve ram mid s h.stable.app (by
    intro i
    exact frame _ (WordZero.separated 0x80ffebbc#32 rx 25 2048 (by decide +kernel) (by decide +kernel) i ⟨input.length,h.room⟩)
      (fun j => WordZero.separated 0x80ffebbc#32 (fp+84#32) 25 4 (by decide +kernel) (by decide +kernel) i j)
      (by simpa only [BitVec.add_zero] using WordZero.separated 0x80ffebbc#32 (fp+464#32) 25 1 (by decide +kernel) (by decide +kernel) i ⟨0,by decide⟩))
  have bytes : Bytes.At mid rx (input++[(c.get 10).setWidth 8]) := MainHeaderAppend.bytes h.stable.bytes value (by
    intro i
    exact frame _ (Bytes.offset_ne rx i.val input.length (by have := i.isLt;omega) (by omega) (by have := i.isLt;omega))
      (fun j => WordZero.separated rx (fp+84#32) 2048 4 (by decide +kernel) (by decide +kernel) ⟨i.val,by have := i.isLt;omega⟩ j)
      (by simpa only [BitVec.add_zero] using WordZero.separated rx (fp+464#32) 2048 1 (by decide +kernel) (by decide +kernel) ⟨i.val,by have := i.isLt;omega⟩ ⟨0,by decide⟩))
  have stable : Stable a mid (input++[(c.get 10).setWidth 8]) s :=
    ⟨(regs 2 (by decide) (by decide) (by decide) (by decide)).trans h.stable.sp,
     (regs 8 (by decide) (by decide) (by decide) (by decide)).trans h.stable.fp,
     (regs 19 (by decide) (by decide) (by decide) (by decide)).trans h.stable.uart,
     (regs 22 (by decide) (by decide) (by decide) (by decide)).trans h.stable.one,
     by simpa only [List.length_append,List.length_singleton] using layout,bytes,app,h.stable.invariant,h.stable.stack,
     (congrArg Prod.fst csr).trans h.stable.masked⟩
  have ready : HeaderReparse.Ready a mid (input++[(c.get 10).setWidth 8]) s :=
    ⟨pc,stable,by simpa only [List.length_append,List.length_singleton] using count,(regs 18 (by decide) (by decide) (by decide) (by decide)).trans h.two⟩
  have bankA : MainGprBank.Frame c a := by
    intro rr member
    have casesReg : rr=21 ∨ rr=23 ∨ rr=26 := by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using member
    rcases casesReg with eq|eq|eq <;> subst rr <;> exact regs _ (by decide) (by decide) (by decide) (by decide)
  have region : ViewFrame.Region ram mid 0x80ffeb90#32 132 := by
    intro i
    exact frame _ (WordZero.separated 0x80ffeb90#32 rx 132 2048 (by decide +kernel) (by decide +kernel) i ⟨input.length,h.room⟩)
      (fun j => WordZero.separated 0x80ffeb90#32 (fp+84#32) 132 4 (by decide +kernel) (by decide +kernel) i j)
      (by simpa only [BitVec.add_zero] using WordZero.separated 0x80ffeb90#32 (fp+464#32) 132 1 (by decide +kernel) (by decide +kernel) i ⟨0,by decide⟩)
  obtain ⟨n,d,after,bound,parsed,post,csrD,bankD,serveD,regionD⟩ := HeaderReparse.contract ready
  exact ⟨10+n,d,after,store.trans parsed,post,csrD.trans csr,MainGprBank.trans bankA bankD,
    MainServeLayout.trans (MainServeMemoryFrames.received (flag := 464) h.room (by decide) (by decide) frame) serveD,
    HeadRegionFrame.trans region regionD⟩


structure Polling (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (s : Spec.Snapshot) : Prop where
  waiting : MainHeaderWaitSafety.Waiting c
  stable : Stable c ram input s
  dst : c.get 12=rx+BitVec.ofNat 32 input.length
  room : input.length<2048
  two : c.get 18=2#32

structure Rbr (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (s : Spec.Snapshot) : Prop where
  pc : c.pc=0x80000baa#32
  stable : Stable c ram input s
  dst : c.get 12=rx+BitVec.ofNat 32 input.length
  room : input.length<2048
  two : c.get 18=2#32

theorem enter {c ram input s} (h : MainHeaderLoopTwo.Ready c ram input s) : Polling c ram input s :=
  ⟨Or.inl h.pc,h.stable,h.dst,h.room,h.two⟩

/-- Every LSR oracle value preserves the full live receive prerequisites or
    reaches the real RBR instruction. No finite readiness schedule is assumed. -/
theorem polling_next {c ram input s} (h : Polling c ram input s) (o : Oracle) :
    ∃ d reads,Observed.stepInstr B img ⟨c,ram⟩ o=⟨.ok d ram [],reads⟩ ∧
      (Polling d ram input s ∨ Rbr d ram input s) ∧ MainHeaderWaitSafety.LsrOnly reads ∧ MainGprBank.Frame c d := by
  obtain ⟨d,reads,step,post,only,regs,csr⟩ := MainHeaderWaitSafety.next ram ⟨h.waiting,h.stable.uart,h.stable.masked⟩ o
  have stable : Stable d ram input s :=
    ⟨(regs 2 (by decide)).trans h.stable.sp,(regs 8 (by decide)).trans h.stable.fp,
     (regs 19 (by decide)).trans h.stable.uart,(regs 22 (by decide)).trans h.stable.one,
     h.stable.layout,h.stable.bytes,h.stable.app,h.stable.invariant,h.stable.stack,(congrArg Prod.fst csr).trans h.stable.masked⟩
  have dst := (regs 12 (by decide)).trans h.dst
  have two := (regs 18 (by decide)).trans h.two
  refine ⟨d,reads,step,?_,only,?_⟩
  · rcases post with waiting|exit
    · exact Or.inl ⟨waiting.1,stable,dst,h.room,two⟩
    · exact Or.inr ⟨exit.1,stable,dst,h.room,two⟩
  · intro rr member
    have casesReg : rr=21 ∨ rr=23 ∨ rr=26 := by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using member
    rcases casesReg with eq|eq|eq <;> subst rr <;> exact regs _ (by decide)

/-- The actual RBR instruction accepts an arbitrary byte, after which the
    quiet store/reparse theorem applies. No valid HTTP-byte premise is used. -/
theorem rbr_next {c ram input s} (h : Rbr c ram input s) (o : Oracle) :
    let d := c.wr 10 (UartPoll.byte (o 0)) 0x80000bae#32
    Observed.stepInstr B img ⟨c,ram⟩ o=⟨.ok d ram [],[⟨0x10000000#32,.b,UartPoll.byte (o 0),0⟩]⟩ ∧
      AfterRbr d ram input s ∧ MainGprBank.Frame c d := by
  refine ⟨UartPoll.rx_data_load c ram o h.pc h.stable.uart,⟨rfl,?_,?_,h.room,?_⟩,?_⟩
  · exact ⟨(Core.wr_get_ne _ _ _ _ _ (by decide : (2 : Reg)≠10)).trans h.stable.sp,
      (Core.wr_get_ne _ _ _ _ _ (by decide : (8 : Reg)≠10)).trans h.stable.fp,
      (Core.wr_get_ne _ _ _ _ _ (by decide : (19 : Reg)≠10)).trans h.stable.uart,
      (Core.wr_get_ne _ _ _ _ _ (by decide : (22 : Reg)≠10)).trans h.stable.one,
      h.stable.layout,h.stable.bytes,h.stable.app,h.stable.invariant,h.stable.stack,h.stable.masked⟩
  · exact (Core.wr_get_ne _ _ _ _ _ (by decide : (12 : Reg)≠10)).trans h.dst
  · exact (Core.wr_get_ne _ _ _ _ _ (by decide : (18 : Reg)≠10)).trans h.two
  · intro rr member
    have casesReg : rr=21 ∨ rr=23 ∨ rr=26 := by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using member
    rcases casesReg with eq|eq|eq <;> subst rr <;> exact Core.wr_get_ne _ _ _ _ _ (by decide)
end E5R.Thermostat.HeaderReactive
