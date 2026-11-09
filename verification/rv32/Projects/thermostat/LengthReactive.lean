import Projects.thermostat.LengthByteStore
import Projects.thermostat.MainLengthLoopRegs
import Projects.thermostat.MainLengthWaitSafety
set_option autoImplicit false
namespace E5R.Thermostat.LengthReactive
open E5R E5R.Thermostat HttpRequestSpec MainLengthState

structure AfterRbr (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (s : Spec.Snapshot) (head : Head) (amount : Nat) : Prop where
  pc : c.pc=0x80000c78#32
  state : MainLengthState.At c ram input s head amount
  dst : c.get 12=rx+BitVec.ofNat 32 input.length
  short : input.length<head.len+amount

/-- Quiet actual length-body continuation for any received byte, ending at
    either the next poll or actual complete-body boundary, with live layout. -/
theorem after_rbr {c ram input s head amount} (h : AfterRbr c ram input s head amount) :
    let next := input++[(c.get 10).setWidth 8]
    ∃ n d after,n≤21 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      Boundary d after next s head amount ∧ d.sameCsr c ∧ d.get 25=BitVec.ofNat 32 (head.len+amount) ∧
      MainGprBank.Frame c d ∧ MainServeLayout.Frame ram after ∧ ViewFrame.Region ram after 0x80ffeb90#32 132 := by
  let next := input++[(c.get 10).setWidth 8]
  have totalBound := total_bound h.state
  have room : input.length<2048 := Nat.lt_of_lt_of_le h.short totalBound
  obtain ⟨a,mid,receive,apc,a10,a25,layoutA,value,frame,ar,ac⟩ := LengthByteStore.contract c ram input.length (head.len+amount) h.pc
    h.state.stable.fp h.state.stable.uart h.state.stable.one h.dst h.state.stable.layout room totalBound h.state.total h.state.stable.stack
  have bytesA : Bytes.At mid rx next := MainLengthAppend.bytes h.state.stable.bytes value (by
    intro i
    exact frame _ (Bytes.offset_ne rx i.val input.length (by have := i.isLt;omega) (by omega) (by have := i.isLt;omega))
      (fun j => WordZero.separated rx (fp+84#32) 2048 4 (by decide +kernel) (by decide +kernel) ⟨i.val,by have := i.isLt;omega⟩ j)
      (by simpa only [BitVec.add_zero] using WordZero.separated rx (fp+468#32) 2048 1 (by decide +kernel) (by decide +kernel) ⟨i.val,by have := i.isLt;omega⟩ ⟨0,by decide⟩))
  have appA (s' : Spec.Snapshot) (app : AppState.At ram s') : AppState.At mid s' := AppState.preserve ram mid s' app (by
    intro i
    exact frame _ (WordZero.separated 0x80ffebbc#32 rx 25 2048 (by decide +kernel) (by decide +kernel) i ⟨input.length,room⟩)
      (fun j => WordZero.separated 0x80ffebbc#32 (fp+84#32) 25 4 (by decide +kernel) (by decide +kernel) i j)
      (by simpa only [BitVec.add_zero] using WordZero.separated 0x80ffebbc#32 (fp+468#32) 25 1 (by decide +kernel) (by decide +kernel) i ⟨0,by decide⟩))
  have regionA : ViewFrame.Region ram mid 0x80ffeb90#32 132 := by
    intro i
    exact frame _ (WordZero.separated 0x80ffeb90#32 rx 132 2048 (by decide +kernel) (by decide +kernel) i ⟨input.length,room⟩)
      (fun j => WordZero.separated 0x80ffeb90#32 (fp+84#32) 132 4 (by decide +kernel) (by decide +kernel) i j)
      (by simpa only [BitVec.add_zero] using WordZero.separated 0x80ffeb90#32 (fp+468#32) 132 1 (by decide +kernel) (by decide +kernel) i ⟨0,by decide⟩)
  have stableA : MainHeaderLoopTwo.Stable a mid next s := by
    refine ⟨(ar 2 (by decide) (by decide) (by decide)).trans h.state.stable.sp,
      (ar 8 (by decide) (by decide) (by decide)).trans h.state.stable.fp,
      (ar 19 (by decide) (by decide) (by decide)).trans h.state.stable.uart,
      (ar 22 (by decide) (by decide) (by decide)).trans h.state.stable.one,
      by simpa only [next,List.length_append,List.length_singleton] using layoutA,bytesA,appA s h.state.stable.app,h.state.stable.invariant,h.state.stable.stack,?_⟩
    exact (congrArg Prod.fst ac).trans h.state.stable.masked
  have stateA : At a mid next s head amount := received h.state stableA frame room ar
  have length : next.length=input.length+1 := by simp only [next,List.length_append,List.length_cons,List.length_nil,Nat.zero_add]
  have serveA : MainServeLayout.Frame ram mid := MainServeMemoryFrames.received (flag := 468) room (by decide) (by decide) frame
  have bankFirst : MainGprBank.Frame c a := by
    intro rr safe
    have ne : ∀ r : Reg, r∈[21,23,26] → r≠10 ∧ r≠11 ∧ r≠25 := by decide +kernel
    obtain ⟨h10,h11,h25⟩ := ne rr safe
    exact ar rr h10 h11 h25
  by_cases more : next.length<head.len+amount
  · have branch : decide (input.length+1<head.len+amount)=true := decide_eq_true (by rw [←length];exact more)
    have pc : a.pc=0x80000c3a#32 := by simpa only [branch,ite_true] using apc
    obtain ⟨d,finish,dpc,d12,layoutD,future,rxFrame,appD,dr,dc⟩ := MainLengthReadSetup.contract B a mid next.length pc stableA.fp (by simpa only [length] using a10) stableA.layout (by omega) stableA.stack
    have stableD : MainHeaderLoopTwo.Stable d (MainLengthReadSetup.memory mid next.length) next s := by
      refine ⟨(dr 2 (by decide)).trans stableA.sp,(dr 8 (by decide)).trans stableA.fp,
        (dr 19 (by decide)).trans stableA.uart,(dr 22 (by decide)).trans stableA.one,layoutD,?_,appD s stableA.app,stableA.invariant,stableA.stack,?_⟩
      · intro i;exact (rxFrame ⟨i.val,by have := i.isLt;have := stableA.layout.bound;omega⟩).trans (stableA.bytes i)
      · exact (congrArg Prod.fst dc).trans stableA.masked
    have stateD := prepared stateA stableD future dr
    refine ⟨10+11,d,MainLengthReadSetup.memory mid next.length,by omega,?_,?_,dc.trans ac,(dr 25 (by decide)).trans a25,?_,MainServeLayout.trans serveA (MainServeMemoryFrames.whole future (by decide)),?low⟩
    case low =>
      intro i
      exact (MainLengthReadSetup.frame mid next.length _ (WordZero.separated 0x80ffeb90#32 (MainLengthReadSetup.fp+456#32) 132 13 (by decide +kernel) (by decide +kernel) i)).trans (regionA i)
    · simpa only [List.append_nil] using receive.trans finish
    · change Boundary d (MainLengthReadSetup.memory mid next.length) next s head amount
      rw [Boundary,if_pos more]
      exact ⟨dpc,stateD,d12,more⟩
    · intro rr safe
      have ne : ∀ r : Reg, r∈[21,23,26] → r∉MainLengthReadSetup.writes := by decide +kernel
      exact (dr rr (ne rr safe)).trans (bankFirst rr safe)
  · have branch : decide (input.length+1<head.len+amount)=false := decide_eq_false (by rw [←length];exact more)
    have pc : a.pc=0x80000c98#32 := by simpa only [branch,Bool.false_eq_true,ite_false] using apc
    exact ⟨10,a,mid,by omega,receive,(if_neg more).mpr ⟨pc,stateA⟩,ac,a25,bankFirst,serveA,regionA⟩


/-- Poll/data loads change only a0; the copied Head and body target survive. -/
theorem recore {c d ram input s head amount} (h : MainLengthState.At c ram input s head amount)
    (regs : ∀ r : Reg,r≠10 → d.get r=c.get r) (masked : d.mie_=false) : MainLengthState.At d ram input s head amount := by
  refine ⟨⟨(regs 2 (by decide)).trans h.stable.sp,(regs 8 (by decide)).trans h.stable.fp,
    (regs 19 (by decide)).trans h.stable.uart,(regs 22 (by decide)).trans h.stable.one,
    h.stable.layout,h.stable.bytes,h.stable.app,h.stable.invariant,h.stable.stack,masked⟩,
    h.view,h.consumed,(regs 18 (by decide)).trans h.two,(regs 20 (by decide)).trans h.length,
    (regs 9 (by decide)).trans h.tag,h.bounds,h.kind,h.total⟩

structure Polling (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (s : Spec.Snapshot) (head : Head) (amount : Nat) : Prop where
  waiting : MainLengthWaitSafety.Waiting c
  state : MainLengthState.At c ram input s head amount
  dst : c.get 12=rx+BitVec.ofNat 32 input.length
  short : input.length<head.len+amount

structure Rbr (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (s : Spec.Snapshot) (head : Head) (amount : Nat) : Prop where
  pc : c.pc=0x80000c74#32
  state : MainLengthState.At c ram input s head amount
  dst : c.get 12=rx+BitVec.ofNat 32 input.length
  short : input.length<head.len+amount

theorem enter {c ram input s head amount} (h : MainLengthState.Ready c ram input s head amount) : Polling c ram input s head amount :=
  ⟨Or.inl h.pc,h.state,h.dst,h.short⟩

theorem polling_next {c ram input s head amount} (h : Polling c ram input s head amount) (o : Oracle) :
    ∃ d reads,Observed.stepInstr B img ⟨c,ram⟩ o=⟨.ok d ram [],reads⟩ ∧
      (Polling d ram input s head amount ∨ Rbr d ram input s head amount) ∧
      MainLengthWaitSafety.LsrOnly reads ∧ MainGprBank.Frame c d := by
  obtain ⟨d,reads,step,post,only,regs,csr⟩ := MainLengthWaitSafety.next ram ⟨h.waiting,h.state.stable.uart,h.state.stable.masked⟩ o
  have state := recore h.state regs ((congrArg Prod.fst csr).trans h.state.stable.masked)
  have dst := (regs 12 (by decide)).trans h.dst
  refine ⟨d,reads,step,?_,only,?_⟩
  · rcases post with waiting|exit
    · exact Or.inl ⟨waiting.1,state,dst,h.short⟩
    · exact Or.inr ⟨exit.1,state,dst,h.short⟩
  · intro rr member
    have casesReg : rr=21 ∨ rr=23 ∨ rr=26 := by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using member
    rcases casesReg with eq|eq|eq <;> subst rr <;> exact regs _ (by decide)

theorem rbr_next {c ram input s head amount} (h : Rbr c ram input s head amount) (o : Oracle) :
    let d := c.wr 10 (MainLengthUart.byte (o 0)) 0x80000c78#32
    Observed.stepInstr B img ⟨c,ram⟩ o=⟨.ok d ram [],[⟨0x10000000#32,.b,MainLengthUart.byte (o 0),0⟩]⟩ ∧
      AfterRbr d ram input s head amount ∧ MainGprBank.Frame c d := by
  refine ⟨MainLengthUart.rx_data_load c ram o h.pc h.state.stable.uart,⟨rfl,?_,?_,h.short⟩,?_⟩
  · exact recore h.state (fun r ne => Core.wr_get_ne _ _ _ _ _ ne) h.state.stable.masked
  · exact (Core.wr_get_ne _ _ _ _ _ (by decide : (12 : Reg)≠10)).trans h.dst
  · intro rr member
    have casesReg : rr=21 ∨ rr=23 ∨ rr=26 := by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using member
    rcases casesReg with eq|eq|eq <;> subst rr <;> exact Core.wr_get_ne _ _ _ _ _ (by decide)
end E5R.Thermostat.LengthReactive
