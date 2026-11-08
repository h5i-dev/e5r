-- G3: retain bank/serve/body-end metadata and initialized route contents.
import Projects.thermostat.MainRouterBankHeaderFrames
import Projects.thermostat.MainLengthResetBank
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.MainLengthEnterRegs
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec MainLengthState
theorem contract_routes {c ram input s head} (h : MainHeaderToBody.Ready c ram input s head)
    (amount : Nat) (kind : head.framing=.length amount) :
    ∃ n d after, 6≤n ∧ n≤17 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      Boundary d after input s head amount ∧ d.sameCsr c ∧ d.get 25=BitVec.ofNat 32 (head.len+amount) ∧ MainGprBank.Frame c d ∧ MainServeLayout.Frame ram after ∧ ViewFrame.Region ram after 0x80ffeb90#32 132 := by
  have amountBound := h.bounds.content amount kind
  have lenBound : head.len≤1024 := Nat.le_trans h.bounds.length.2 (Nat.min_le_right _ _)
  have totalBound : head.len+amount≤2048 := by omega
  have filledBound := h.stable.layout.bound
  have pc : c.pc=0x80000c26#32 := by simpa only [kind,MainBodyHeadDispatch.At] using h.cut
  have object : Memory.Block B fp 456 := by
    have block := Memory.sub_block (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 63508) (m := 456) h.stable.stack (by decide) (by decide)
    simpa only [show 0x80ff0000#32+63508#32=fp by decide +kernel] using block
  have payload : ramRead ram (fp+124#32) .w=BitVec.ofNat 32 amount := by
    simpa only [BitVec.add_assoc,show 116#32+8#32=124#32 by decide +kernel] using (h.view.framing amount kind).1
  let mid := MainLengthStart.memory ram fp (BitVec.ofNat 32 amount) (BitVec.ofNat 32 head.len) (BitVec.ofNat 32 input.length)
  obtain ⟨a,ta,apc,a25,a10,ar,ac⟩ := MainLengthStart.contract B c ram fp _ _ _ h.stable.fp h.length payload h.stable.layout.filledPtr h.stable.layout.filled object (by decide +kernel) pc
  have sum : BitVec.ofNat 32 amount+BitVec.ofNat 32 head.len=BitVec.ofNat 32 (head.len+amount) := by rw [←BitVec.ofNat_add,Nat.add_comm]
  have test : taken .geu (BitVec.ofNat 32 input.length) (BitVec.ofNat 32 amount+BitVec.ofNat 32 head.len)=decide (head.len+amount≤input.length) := by
    rw [sum]
    exact HeadTargetMath.geu input.length (head.len+amount) filledBound totalBound
  obtain ⟨b,tb,bpc,br,bc⟩ := MainLengthEnoughBranch.contract B a mid _ _ (decide (head.len+amount≤input.length)) apc a10 a25 test
  have kept (rr : Reg) (h25 : rr≠25) (h10 : rr≠10) : b.get rr=c.get rr := (br rr).trans (ar rr h25 h10)
  have csr : b.sameCsr c := bc.trans ac
  have future : ViewFrame.Region ram mid fp 449 := by
    simpa only [BitVec.add_zero] using MainLengthStartMemory.region ram fp _ _ (BitVec.ofNat 32 input.length) 0 449 (Or.inl (by decide)) (by decide)
  have stable : MainHeaderLoopTwo.Stable b mid input s := by
    refine ⟨(kept 2 (by decide) (by decide)).trans h.stable.sp,(kept 8 (by decide) (by decide)).trans h.stable.fp,
      (kept 19 (by decide) (by decide)).trans h.stable.uart,(kept 22 (by decide) (by decide)).trans h.stable.one,
      MainHeaderLayout.preserve h.stable.layout future,?_,?_,h.stable.invariant,h.stable.stack,?_⟩
    · intro i
      apply Eq.trans (MainLengthStartMemory.frame ram fp _ _ _ _ (fun j => WordZero.separated rx (fp+452#32) 2048 4 (by decide +kernel) (by decide +kernel) ⟨i.val,by have := i.isLt;omega⟩ j))
      exact h.stable.bytes i
    · apply AppState.preserve ram mid s h.stable.app
      intro i
      exact MainLengthStartMemory.frame ram fp _ _ _ _ (fun j => WordZero.separated 0x80ffebbc#32 (fp+452#32) 25 4 (by decide +kernel) (by decide +kernel) i j)
    · exact (congrArg Prod.fst csr).trans h.stable.masked
  have view : HeadCompletedView.At mid (fp+116#32) head := MainCopyView.head
    (MainLengthStartMemory.region ram fp _ _ (BitVec.ofNat 32 input.length) 116 304 (Or.inl (by decide)) (by decide)) head h.view
  have consumed : ramRead mid (fp+444#32) .w=BitVec.ofNat 32 head.len := (ViewFrame.word future 444 (by decide)).trans h.consumed
  have total : ramRead mid (fp+452#32) .w=BitVec.ofNat 32 (head.len+amount) :=
    (MainLengthStartMemory.total ram fp _ _ (BitVec.ofNat 32 input.length)).trans sum
  have state : At b mid input s head amount := ⟨stable,view,consumed,(kept 18 (by decide) (by decide)).trans h.two,
    (kept 20 (by decide) (by decide)).trans h.length,(kept 9 (by decide) (by decide)).trans h.tag,widen h.bounds (Nat.min_le_right _ _),kind,total⟩
  have bankFirst : MainGprBank.Frame c b := by
    intro rr safe
    have ne : ∀ r : Reg, r∈[21,23,26] → r≠25 ∧ r≠10 := by decide +kernel
    obtain ⟨h25,h10⟩ := ne rr safe
    exact kept rr h25 h10
  have protectedStart : ViewFrame.Region ram mid 0x80ffeb90#32 132 := by
    intro i
    exact MainLengthStartMemory.frame ram fp _ _ _ _ (WordZero.separated 0x80ffeb90#32 (fp+452#32) 132 4 (by decide +kernel) (by decide +kernel) i)
  by_cases short : input.length<head.len+amount
  · have branch : decide (head.len+amount≤input.length)=false := decide_eq_false (by omega)
    have pc : b.pc=0x80000c3a#32 := by simpa only [branch,Bool.false_eq_true,ite_false] using bpc
    obtain ⟨d,td,ready,dc,dr,serveD⟩ := MainLengthPrepareRegs.contract state pc ((br 10).trans a10) short
    have protectedEnd : ViewFrame.Region ram (MainLengthReadSetup.memory mid input.length) 0x80ffeb90#32 132 := by
      intro i
      exact (MainLengthReadSetup.frame mid input.length _ (WordZero.separated 0x80ffeb90#32 (MainLengthReadSetup.fp+456#32) 132 13 (by decide +kernel) (by decide +kernel) i)).trans (protectedStart i)
    refine ⟨17,d,_,by decide,by decide,(ta.trans tb).trans td,?_,dc.trans csr,(dr 25 (by decide)).trans ((br 25).trans (a25.trans sum)),?_,MainServeLayout.trans (MainServeMemoryFrames.whole future (by decide)) serveD,protectedEnd⟩
    · simpa only [Boundary,short,ite_true] using ready
    · intro rr safe
      have ne : ∀ r : Reg, r∈[21,23,26] → r∉MainLengthReadSetup.writes := by decide +kernel
      exact (dr rr (ne rr safe)).trans (bankFirst rr safe)
  · have branch : decide (head.len+amount≤input.length)=true := decide_eq_true (by omega)
    have pc : b.pc=0x80000c98#32 := by simpa only [branch,ite_true] using bpc
    refine ⟨6,b,mid,by decide,by decide,ta.trans tb,?_,csr,(br 25).trans (a25.trans sum),bankFirst,MainServeMemoryFrames.whole future (by decide),protectedStart⟩
    simpa only [Boundary,short,ite_false] using (show b.pc=0x80000c98#32 ∧ At b mid input s head amount from ⟨pc,state⟩)

end E5R.Thermostat.MainLengthEnterRegs

namespace E5R.Thermostat.MainLengthLoopRegs
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec MainLengthState
theorem contract_routes {c ram input s head amount} (h : Ready c ram input s head amount)
    (pending : List Word) (ready datum : Word)
    (notReady : ∀ status∈pending, UartPoll.byte status &&& 1#32=0#32)
    (isReady : UartPoll.byte ready &&& 1#32≠0#32) :
    let next := input++[(UartPoll.byte datum).setWidth 8]
    ∃ n d after, n≤25+4*pending.length ∧ Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (MainLengthWait.reads pending ready datum) [] ∧
      Boundary d after next s head amount ∧ d.sameCsr c ∧ d.get 25=BitVec.ofNat 32 (head.len+amount) ∧ MainGprBank.Frame c d ∧ MainServeLayout.Frame ram after ∧ ViewFrame.Region ram after 0x80ffeb90#32 132 := by
  let next := input++[(UartPoll.byte datum).setWidth 8]
  change ∃ n d after, n≤25+4*pending.length ∧ Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (MainLengthWait.reads pending ready datum) [] ∧
    Boundary d after next s head amount ∧ d.sameCsr c ∧ d.get 25=BitVec.ofNat 32 (head.len+amount) ∧ MainGprBank.Frame c d ∧ MainServeLayout.Frame ram after ∧ ViewFrame.Region ram after 0x80ffeb90#32 132
  have totalBound := total_bound h.state
  have room : input.length<2048 := Nat.lt_of_lt_of_le h.short totalBound
  obtain ⟨a,mid,receive,apc,a25,a10,layoutA,bytesA,appA,ar,ac,frame⟩ := MainLengthAppend.contract c ram input (head.len+amount) pending ready datum h.pc
    h.state.stable.fp h.state.stable.uart h.state.stable.one h.dst h.state.stable.layout room h.state.stable.bytes totalBound h.state.total h.state.stable.stack notReady isReady
  have appendRegion : ViewFrame.Region ram mid 0x80ffeb90#32 132 := by
    intro i
    exact frame _
      (WordZero.separated 0x80ffeb90#32 MainLengthRefill.rx 132 2048 (by decide +kernel) (by decide +kernel) i ⟨input.length,room⟩)
      (WordZero.separated 0x80ffeb90#32 (MainLengthRefill.fp+84#32) 132 4 (by decide +kernel) (by decide +kernel) i)
      (by simpa only [BitVec.add_zero] using WordZero.separated 0x80ffeb90#32 (MainLengthRefill.fp+468#32) 132 1 (by decide +kernel) (by decide +kernel) i ⟨0,by decide⟩)
  have stableA : MainHeaderLoopTwo.Stable a mid next s := by
    refine ⟨(ar 2 (by decide) (by decide) (by decide)).trans h.state.stable.sp,
      (ar 8 (by decide) (by decide) (by decide)).trans h.state.stable.fp,
      (ar 19 (by decide) (by decide) (by decide)).trans h.state.stable.uart,
      (ar 22 (by decide) (by decide) (by decide)).trans h.state.stable.one,
      layoutA,bytesA,appA s h.state.stable.app,h.state.stable.invariant,h.state.stable.stack,?_⟩
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
    obtain ⟨d,finish,dpc,d12,layoutD,future,rxFrame,appD,dr,dc⟩ := MainLengthReadSetup.contract B a mid next.length pc stableA.fp a10 stableA.layout (by omega) stableA.stack
    have stableD : MainHeaderLoopTwo.Stable d (MainLengthReadSetup.memory mid next.length) next s := by
      refine ⟨(dr 2 (by decide)).trans stableA.sp,(dr 8 (by decide)).trans stableA.fp,
        (dr 19 (by decide)).trans stableA.uart,(dr 22 (by decide)).trans stableA.one,layoutD,?_,appD s stableA.app,stableA.invariant,stableA.stack,?_⟩
      · intro i;exact (rxFrame ⟨i.val,by have := i.isLt;have := stableA.layout.bound;omega⟩).trans (stableA.bytes i)
      · exact (congrArg Prod.fst dc).trans stableA.masked
    have stateD := prepared stateA stableD future dr
    have protectedEnd : ViewFrame.Region ram (MainLengthReadSetup.memory mid next.length) 0x80ffeb90#32 132 := by
      intro i
      exact (MainLengthReadSetup.frame mid next.length _ (WordZero.separated 0x80ffeb90#32 (MainLengthReadSetup.fp+456#32) 132 13 (by decide +kernel) (by decide +kernel) i)).trans (appendRegion i)
    refine ⟨(14+4*pending.length)+11,d,MainLengthReadSetup.memory mid next.length,by omega,?_,?_,dc.trans ac,(dr 25 (by decide)).trans a25,?_,MainServeLayout.trans serveA (MainServeMemoryFrames.whole future (by decide)),protectedEnd⟩
    · simpa only [List.append_nil] using receive.trans finish.observed
    · simpa only [Boundary,more,ite_true] using (show Ready d (MainLengthReadSetup.memory mid next.length) next s head amount from ⟨dpc,stateD,d12,more⟩)
    · intro rr safe
      have ne : ∀ r : Reg, r∈[21,23,26] → r∉MainLengthReadSetup.writes := by decide +kernel
      exact (dr rr (ne rr safe)).trans (bankFirst rr safe)
  · have branch : decide (input.length+1<head.len+amount)=false := decide_eq_false (by rw [←length];exact more)
    have pc : a.pc=0x80000c98#32 := by simpa only [branch,Bool.false_eq_true,ite_false] using apc
    exact ⟨14+4*pending.length,a,mid,by omega,receive,(if_neg more).mpr ⟨pc,stateA⟩,ac,a25,bankFirst,serveA,appendRegion⟩

end E5R.Thermostat.MainLengthLoopRegs

namespace E5R.Thermostat.MainLengthStreamRegs
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec MainLengthState
theorem contract_routes (wire : Nat → BitVec 8) (plan : MainLengthStreamPlan.Plan) (fuel : Nat)
    {c ram input s head amount} (h : Boundary c ram input s head amount) (h25 : c.get 25=BitVec.ofNat 32 (head.len+amount))
    (remaining : input.length+fuel=head.len+amount)
    (valid : MainLengthStreamPlan.Valid plan wire input.length fuel) :
    ∃ n d after, n≤MainLengthStreamPlan.cost plan input.length fuel ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (MainLengthStreamPlan.logs plan input.length fuel) [] ∧
      d.pc=0x80000c98#32 ∧ At d after (input++arrivals wire input.length fuel) s head amount ∧ d.sameCsr c ∧ d.get 25=BitVec.ofNat 32 (head.len+amount) ∧ MainGprBank.Frame c d ∧ MainServeLayout.Frame ram after ∧ ViewFrame.Region ram after 0x80ffeb90#32 132 := by
  induction fuel generalizing c ram input with
  | zero =>
    have full : ¬input.length<head.len+amount := by omega
    have post : c.pc=0x80000c98#32 ∧ At c ram input s head amount := by simpa only [Boundary,full,ite_false] using h
    refine ⟨0,c,ram,by simp only [MainLengthStreamPlan.cost];omega,?_,post.1,?_,rfl,h25,MainGprBank.refl c,MainServeLayout.refl ram,fun _ => rfl⟩
    · exact .refl _
    · simpa only [arrivals,List.range_zero,List.map_nil,List.append_nil] using post.2
  | succ fuel ih =>
    have short : input.length<head.len+amount := by omega
    have ready : Ready c ram input s head amount := by simpa only [Boundary,short,ite_true] using h
    obtain ⟨pendingOK,readyOK,datumOK⟩ := valid input.length (by omega) (by omega)
    change (UartPoll.byte (plan.datum input.length)).setWidth 8=wire input.length at datumOK
    let next := input++[wire input.length]
    have length : next.length=input.length+1 := by simp only [next,List.length_append,List.length_cons,List.length_nil,Nat.zero_add]
    have step := MainLengthLoopRegs.contract_routes ready (plan.pending input.length) (plan.ready input.length) (plan.datum input.length) pendingOK readyOK
    dsimp only at step
    rw [datumOK] at step
    obtain ⟨first,a,mid,firstBound,firstTrace,boundary,firstCsr,first25,firstRegs,firstServe,firstRegion⟩ := step
    have validNext : MainLengthStreamPlan.Valid plan wire next.length fuel := by rw [length];exact ChunkReceivePlan.valid_tail valid
    obtain ⟨rest,d,after,restBound,restTrace,pc,post,csr,last25,lastRegs,lastServe,lastRegion⟩ := ih boundary first25 (by rw [length];omega) validNext
    have bytes : next++arrivals wire next.length fuel=input++arrivals wire input.length (fuel+1) := by
      rw [length,arrivals_succ]
      simp only [next,List.append_assoc,List.singleton_append]
    rw [bytes] at post
    refine ⟨first+rest,d,after,?_,?_,pc,post,csr.trans firstCsr,last25,MainGprBank.trans firstRegs lastRegs,MainServeLayout.trans firstServe lastServe,HeadRegionFrame.trans firstRegion lastRegion⟩
    · rw [length] at restBound
      change first+rest≤25+4*(plan.pending input.length).length+MainLengthStreamPlan.cost plan (input.length+1) fuel
      omega
    · have trace := firstTrace.trans restTrace
      simpa only [MainLengthStreamPlan.logs,length,List.append_nil,List.length_append,List.length_cons,List.length_nil,Nat.zero_add] using trace

end E5R.Thermostat.MainLengthStreamRegs

namespace E5R.Thermostat.MainLengthBodyRegs
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec MainLengthState
theorem contract_routes {c ram input s head} (h : MainHeaderToBody.Ready c ram input s head)
    (amount : Nat) (kind : head.framing=.length amount) (wire : Nat → BitVec 8) (plan : MainLengthStreamPlan.Plan)
    (valid : MainLengthStreamPlan.Valid plan wire input.length (head.len+amount-input.length)) :
    ∃ n d after, n≤17+MainLengthStreamPlan.cost plan input.length (head.len+amount-input.length) ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (MainLengthStreamPlan.logs plan input.length (head.len+amount-input.length)) [] ∧
      d.pc=0x80000c98#32 ∧ At d after (input++arrivals wire input.length (head.len+amount-input.length)) s head amount ∧ d.sameCsr c ∧ d.get 25=BitVec.ofNat 32 (head.len+amount) ∧ MainGprBank.Frame c d ∧ MainServeLayout.Frame ram after ∧ ViewFrame.Region ram after 0x80ffeb90#32 132 := by
  obtain ⟨first,a,mid,lo,hi,start,boundary,firstCsr,first25,firstRegs,firstServe,firstRegion⟩ := MainLengthEnterRegs.contract_routes h amount kind
  by_cases within : input.length≤head.len+amount
  · obtain ⟨rest,d,after,bound,finish,pc,state,csr,last25,lastRegs,lastServe,lastRegion⟩ := MainLengthStreamRegs.contract_routes wire plan (head.len+amount-input.length) boundary first25 (by omega) valid
    refine ⟨first+rest,d,after,by omega,?_,pc,state,csr.trans firstCsr,last25,MainGprBank.trans firstRegs lastRegs,MainServeLayout.trans firstServe lastServe,HeadRegionFrame.trans firstRegion lastRegion⟩
    simpa only [List.nil_append] using start.observed.trans finish
  · have short : ¬input.length<head.len+amount := by omega
    have missing : head.len+amount-input.length=0 := by omega
    have post : a.pc=0x80000c98#32 ∧ At a mid input s head amount := by simpa only [Boundary,short,ite_false] using boundary
    refine ⟨first,a,mid,?_,?_,post.1,?_,firstCsr,first25,firstRegs,firstServe,firstRegion⟩
    · simp only [missing,MainLengthStreamPlan.cost];omega
    · simpa only [missing,MainLengthStreamPlan.logs] using start.observed
    · simpa only [missing,arrivals,List.range_zero,List.map_nil,List.append_nil] using post.2

end E5R.Thermostat.MainLengthBodyRegs

namespace E5R.Thermostat.MainHeaderResetBodyBank
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec MainLengthState
theorem contract_routes (c : Core) (ram : Word → BitVec 8) (wire : Nat → BitVec 8)
    (plan : MainHeaderStreamPlan.Plan) (fuel : Nat) (head : Head)
    (hp : c.pc=0x80000000#32) (mpp : c.mpp=0 ∨ c.mpp=3) (masked : c.mie_=false)
    (stack : Memory.Block B 0x80ff0000#32 65536) (space : fuel≤2048)
    (valid : MainHeaderStreamPlan.Valid plan wire 0 fuel)
    (accepted : (consume wire fuel []).result=.done head) :
    ∃ n d after, n≤2967+MainHeaderStreamPlan.cost plan 0 fuel ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (MainHeaderStreamPlan.logs plan 0 (consume wire fuel []).received) [] ∧
      MainHeaderToBody.Ready d after (consume wire fuel []).input Spec.initial head ∧
      Observed.input (MainHeaderStreamPlan.logs plan 0 (consume wire fuel []).received)=(consume wire fuel []).input ∧ MainGprBank.At d ∧ MainServeLayout.At after 0 ∧ InitRoutes.Layout after := by
  obtain ⟨hn,a,mid,bound,trace,boundary,bytes,exactResult,bank,serve,routes⟩ := MainHeaderResetBank.contract_routes c ram wire plan fuel hp mpp masked stack space valid
  try dsimp only at boundary exactResult bound trace bytes
  have doneBoundary : MainHeaderLoopTwo.Boundary a mid (consume wire fuel []).input Spec.initial (.done head) := by simpa only [accepted] using boundary
  have parsed : HttpRequestBytes.parse (consume wire fuel []).input 1024 1024=.done head := exactResult.symm.trans accepted
  obtain ⟨bn,d,lo,hi,finish,ready,_,regs,serveFrame⟩ := MainHeaderToBodyRegs.contract doneBoundary parsed
  refine ⟨hn+bn,d,_,by omega,?_,ready,bytes,MainGprBank.preserve regs bank,MainServeLayout.preserve serveFrame serve,?_⟩
  simpa only [List.append_nil] using trace.trans finish.observed
  · apply InitRoutes.layout_preserve mid _ routes
    · simpa only [ViewFrame.Region,show MainHeaderToBody.sp+72#32=0x80ffebd8#32 by decide +kernel] using MainBodyHeadMemory.frame mid MainHeaderToBody.sp head 72 60 (by decide) (Or.inl (by decide)) (Or.inl (by decide))
    · simpa only [ViewFrame.Region,show MainHeaderToBody.sp+16#32=0x80ffeba0#32 by decide +kernel] using MainBodyHeadMemory.frame mid MainHeaderToBody.sp head 16 4 (by decide) (Or.inl (by decide)) (Or.inl (by decide))

end E5R.Thermostat.MainHeaderResetBodyBank

namespace E5R.Thermostat.MainLengthResetBank
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec MainLengthState
theorem contract_routes (c : Core) (ram : Word → BitVec 8) (wire : Nat → BitVec 8)
    (headerPlan : MainHeaderStreamPlan.Plan) (fuel : Nat) (head : Head) (amount : Nat)
    (bodyPlan : MainLengthStreamPlan.Plan)
    (hp : c.pc=0x80000000#32) (mpp : c.mpp=0 ∨ c.mpp=3) (masked : c.mie_=false)
    (stack : Memory.Block B 0x80ff0000#32 65536) (space : fuel≤2048)
    (headerValid : MainHeaderStreamPlan.Valid headerPlan wire 0 fuel)
    (accepted : (consume wire fuel []).result=.done head) (kind : head.framing=.length amount)
    (bodyValid : MainLengthStreamPlan.Valid bodyPlan wire (consume wire fuel []).input.length
      (head.len+amount-(consume wire fuel []).input.length)) :
    let input := (consume wire fuel []).input
    let missing := head.len+amount-input.length
    let reads := MainHeaderStreamPlan.logs headerPlan 0 (consume wire fuel []).received++MainLengthStreamPlan.logs bodyPlan input.length missing
    ∃ n d after, n≤2984+MainHeaderStreamPlan.cost headerPlan 0 fuel+MainLengthStreamPlan.cost bodyPlan input.length missing ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ reads [] ∧ d.pc=0x80000c98#32 ∧
      MainLengthState.At d after (input++arrivals wire input.length missing) Spec.initial head amount ∧
      Observed.input reads=input++arrivals wire input.length missing ∧ d.get 25=BitVec.ofNat 32 (head.len+amount) ∧ MainGprBank.At d ∧ MainServeLayout.At after 0 ∧ InitRoutes.Layout after := by
  obtain ⟨hn,a,mid,headBound,headTrace,headReady,headBytes,bank,serve,routes⟩ := MainHeaderResetBodyBank.contract_routes c ram wire headerPlan fuel head hp mpp masked stack space headerValid accepted
  obtain ⟨bn,d,after,bodyBound,bodyTrace,pc,state,_,last25,regs,serveFrame,protectedRegion⟩ := MainLengthBodyRegs.contract_routes headReady amount kind wire bodyPlan bodyValid
  refine ⟨hn+bn,d,after,by omega,?_,pc,state,?_,last25,MainGprBank.preserve regs bank,MainServeLayout.preserve serveFrame serve,?_⟩
  · simpa only [List.append_nil] using headTrace.trans bodyTrace
  · rw [Observed.input_append,headBytes,MainLengthStreamPlan.logs_wire bodyPlan wire _ _ _ bodyValid (Nat.le_refl _)]
  · apply InitRoutes.layout_preserve mid after routes
    · simpa only [ViewFrame.Region,show 0x80ffeb90#32+72#32=0x80ffebd8#32 by decide +kernel] using HeadRegionFrame.sub protectedRegion 72 60 (by decide)
    · simpa only [ViewFrame.Region,show 0x80ffeb90#32+16#32=0x80ffeba0#32 by decide +kernel] using HeadRegionFrame.sub protectedRegion 16 4 (by decide)

end E5R.Thermostat.MainLengthResetBank
