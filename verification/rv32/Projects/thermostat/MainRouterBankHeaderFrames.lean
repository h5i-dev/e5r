-- G3: keep the existing strongest bank/serve metadata while framing routes.
import Projects.thermostat.MainRouterParserFrames
import Projects.thermostat.MainRouterResetFrame
import Projects.thermostat.MainHeaderResetBank
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.MainHeaderAppendServe
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec MainHeaderLoopTwo
theorem contract_routes (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (pending : List Word) (ready datum : Word)
    (hp : c.pc=0x80000ba2#32) (h8 : c.get 8=MainHeaderRefill.fp) (h19 : c.get 19=0x10000000#32) (h22 : c.get 22=1#32)
    (h12 : c.get 12=MainHeaderRefill.rx+BitVec.ofNat 32 input.length)
    (layout : MainHeaderLayout.At ram input.length) (room : input.length<2048) (inputAt : Bytes.At ram MainHeaderRefill.rx input)
    (stack : Memory.Block MainHeaderRefill.B 0x80ff0000#32 65536)
    (notReady : ∀ status ∈ pending, UartPoll.byte status &&& 1#32=0#32) (isReady : UartPoll.byte ready &&& 1#32≠0#32) :
    ∃ d after, Observed.Steps MainHeaderRefill.B img (14+4*pending.length) ⟨c,ram⟩ ⟨d,after⟩ (MainHeaderWait.reads pending ready datum) [] ∧
      d.pc=0x80000a10#32 ∧ d.get 12=BitVec.ofNat 32 (input++[(UartPoll.byte datum).setWidth 8]).length ∧
      MainHeaderLayout.At after (input++[(UartPoll.byte datum).setWidth 8]).length ∧
      Bytes.At after MainHeaderRefill.rx (input++[(UartPoll.byte datum).setWidth 8]) ∧
      (∀ state, AppState.At ram state → AppState.At after state) ∧
      (∀ r : Reg, r≠10 → r≠11 → r≠14 → r≠12 → d.get r=c.get r) ∧ d.sameCsr c ∧ MainServeLayout.Frame ram after ∧ ViewFrame.Region ram after 0x80ffeb90#32 132 := by
  obtain ⟨d,after,trace,pc,count,layoutAfter,value,frame,regs,csr⟩ := MainHeaderRefill.contract c ram input.length pending ready datum hp h8 h19 h22 h12 layout room stack notReady isReady
  have inputAfter : Bytes.At after MainHeaderRefill.rx (input++[(UartPoll.byte datum).setWidth 8]) := by
    apply bytes inputAt value
    intro i
    exact frame _ (Bytes.offset_ne MainHeaderRefill.rx i.val input.length (by have := i.isLt;omega) (by omega) (by have := i.isLt;omega))
      (fun j => WordZero.separated MainHeaderRefill.rx (MainHeaderRefill.fp+84#32) 2048 4 (by decide +kernel) (by decide +kernel) ⟨i.val,by have := i.isLt;omega⟩ j)
      (by simpa only [BitVec.add_zero] using WordZero.separated MainHeaderRefill.rx (MainHeaderRefill.fp+464#32) 2048 1 (by decide +kernel) (by decide +kernel) ⟨i.val,by have := i.isLt;omega⟩ ⟨0,by decide⟩)
  have appFrame : ∀ state, AppState.At ram state → AppState.At after state := by
    intro state app
    apply AppState.preserve ram after state app
    intro i
    exact frame _
      (WordZero.separated 0x80ffebbc#32 MainHeaderRefill.rx 25 2048 (by decide +kernel) (by decide +kernel) i ⟨input.length,room⟩)
      (fun j => WordZero.separated 0x80ffebbc#32 (MainHeaderRefill.fp+84#32) 25 4 (by decide +kernel) (by decide +kernel) i j)
      (by simpa only [BitVec.add_zero] using WordZero.separated 0x80ffebbc#32 (MainHeaderRefill.fp+464#32) 25 1 (by decide +kernel) (by decide +kernel) i ⟨0,by decide⟩)
  have protectedRegion : ViewFrame.Region ram after 0x80ffeb90#32 132 := by
    intro i
    exact frame _
      (WordZero.separated 0x80ffeb90#32 MainHeaderRefill.rx 132 2048 (by decide +kernel) (by decide +kernel) i ⟨input.length,room⟩)
      (fun j => WordZero.separated 0x80ffeb90#32 (MainHeaderRefill.fp+84#32) 132 4 (by decide +kernel) (by decide +kernel) i j)
      (by simpa only [BitVec.add_zero] using WordZero.separated 0x80ffeb90#32 (MainHeaderRefill.fp+464#32) 132 1 (by decide +kernel) (by decide +kernel) i ⟨0,by decide⟩)
  refine ⟨d,after,trace,pc,?_,?_,inputAfter,appFrame,regs,csr,MainServeMemoryFrames.received (flag := 464) room (by decide) (by decide) frame,protectedRegion⟩
  · simpa only [List.length_append,List.length_cons,List.length_nil,Nat.zero_add] using count
  · simpa only [List.length_append,List.length_cons,List.length_nil,Nat.zero_add] using layoutAfter

end E5R.Thermostat.MainHeaderAppendServe

namespace E5R.Thermostat.MainHeaderLoopRegs
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec MainHeaderLoopTwo
theorem contract_routes {c ram input s} (h : Ready c ram input s) (pending : List Word) (ready datum : Word)
    (notReady : ∀ status ∈ pending, UartPoll.byte status &&& 1#32=0#32) (isReady : UartPoll.byte ready &&& 1#32≠0#32) :
    let next := input++[(UartPoll.byte datum).setWidth 8]
    ∃ n d after, n≤47+4*pending.length+HeadColdFutureComplete.budget (min next.length 1024) ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (MainHeaderWait.reads pending ready datum) [] ∧
      Boundary d after next s (HttpRequestBytes.parse next 1024 1024) ∧ d.sameCsr c ∧ MainGprBank.Frame c d ∧ MainServeLayout.Frame ram after ∧ ViewFrame.Region ram after 0x80ffeb90#32 132 := by
  let next := input++[(UartPoll.byte datum).setWidth 8]
  change ∃ n d after, n≤47+4*pending.length+HeadColdFutureComplete.budget (min next.length 1024) ∧
    Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (MainHeaderWait.reads pending ready datum) [] ∧
    Boundary d after next s (HttpRequestBytes.parse next 1024 1024) ∧ d.sameCsr c ∧ MainGprBank.Frame c d ∧ MainServeLayout.Frame ram after ∧ ViewFrame.Region ram after 0x80ffeb90#32 132
  have room0 := h.room
  obtain ⟨a,mid,receive,apc,a12,layoutA,bytesA,appA,ar,ac,serveA,appendRegion⟩ := MainHeaderAppendServe.contract_routes c ram input pending ready datum h.pc h.stable.fp h.stable.uart h.stable.one h.dst
    h.stable.layout h.room h.stable.bytes h.stable.stack notReady isReady
  have asp : a.get 2=0x80ffeb90#32 := (ar 2 (by decide) (by decide) (by decide) (by decide)).trans h.stable.sp
  have afp : a.get 8=fp := (ar 8 (by decide) (by decide) (by decide) (by decide)).trans h.stable.fp
  have auart : a.get 19=0x10000000#32 := (ar 19 (by decide) (by decide) (by decide) (by decide)).trans h.stable.uart
  have aone : a.get 22=1#32 := (ar 22 (by decide) (by decide) (by decide) (by decide)).trans h.stable.one
  have a18 : a.get 18=2#32 := (ar 18 (by decide) (by decide) (by decide) (by decide)).trans h.two
  have nextBound : next.length≤2048 := by simp only [next,List.length_append,List.length_cons,List.length_nil,Nat.zero_add];omega
  have parserStack : Memory.Block B 0x80ffea10#32 5312 := by
    have block := Memory.sub_block (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 59920) (m := 5312) h.stable.stack (by decide) (by decide)
    simpa only [show 0x80ff0000#32+59920#32=0x80ffea10#32 by decide +kernel] using block
  have object : Memory.Block B fp 1326 := by
    have block := Memory.sub_block (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 63508) (m := 1326) h.stable.stack (by decide) (by decide)
    simpa only [show 0x80ff0000#32+63508#32=fp by decide +kernel] using block
  have clOutside : ∀ q : Fin 14, B.inRam (BitVec.ofNat 32 (0x80005de0+q.val)) 1=false := by decide +kernel
  have teOutside : ∀ q : Fin 17, B.inRam (BitVec.ofNat 32 (0x80005dee+q.val)) 1=false := by decide +kernel
  obtain ⟨pn,b,parsed,plo,phi,parse,bpc,bsp,saved,view,rxFrame,future,_,parserRegion,bc⟩ := MainHeadParser.contract_routes B a mid next apc asp afp a12 layoutA.head bytesA nextBound parserStack clOutside teOutside
  have bfp : b.get 8=fp := saved.x8.trans afp
  have buart : b.get 19=0x10000000#32 := saved.x19.trans auart
  have bone : b.get 22=1#32 := saved.x22.trans aone
  have b18 : b.get 18=2#32 := saved.x18.trans a18
  obtain ⟨dn,d,dlo,dhi,dispatch,cut,dr,dc,keep⟩ := MainHeaderDispatchTwo.contract B b parsed fp (HttpRequestBytes.parse next 1024 1024) bpc bfp bone view object (by decide +kernel)
  have layoutB : MainHeaderLayout.At parsed next.length := MainHeaderLayout.preserve layoutA future
  have bytesB : Bytes.At parsed rx next := by intro i;exact (rxFrame ⟨i.val,by have := i.isLt;omega⟩).trans (bytesA i)
  have source : Stable d parsed next s := by
    refine ⟨(dr 2 (by decide)).trans bsp,(dr 8 (by decide)).trans bfp,(dr 19 (by decide)).trans buart,(dr 22 (by decide)).trans bone,
      layoutB,bytesB,AppState.preserve mid parsed s (appA s h.stable.app) (by simpa only [ViewFrame.Region,show 0x80ffeb90#32+44#32=0x80ffebbc#32 by decide +kernel] using HeadRegionFrame.sub parserRegion 44 25 (by decide)),h.stable.invariant,h.stable.stack,?_⟩
    exact (congrArg Prod.fst ((dc.trans bc).trans ac)).trans h.stable.masked
  have prefixRun := (receive.trans parse.observed).trans dispatch.observed
  have prefixRegion := HeadRegionFrame.trans appendRegion parserRegion
  have prefixCsr := (dc.trans bc).trans ac
  have serveD : MainServeLayout.Frame ram parsed := MainServeLayout.trans serveA (MainServeMemoryFrames.whole future (by decide))
  have bankD : MainGprBank.Frame c d := by
    intro rr safe
    have casesReg : rr=21 ∨ rr=23 ∨ rr=26 := by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using safe
    rcases casesReg with h|h|h <;> subst rr
    · exact (dr 21 (by decide)).trans (saved.x21.trans (ar 21 (by decide) (by decide) (by decide) (by decide)))
    · exact (dr 23 (by decide)).trans (saved.x23.trans (ar 23 (by decide) (by decide) (by decide) (by decide)))
    · exact (dr 26 (by decide)).trans (saved.x26.trans (ar 26 (by decide) (by decide) (by decide) (by decide)))
  cases result : HttpRequestBytes.parse next 1024 1024 with
  | incomplete =>
    have pc : d.pc=0x80000a50#32 := by simpa only [result,MainHeaderDispatchTwo.At] using cut
    have d18 : d.get 18=2#32 := (show d.get 18=b.get 18 from by simpa only [result,MainHeaderDispatchTwo.Keeps18] using keep).trans b18
    have room : next.length<2048 := by have := MainHeaderIncompleteBound.bound next result;omega
    obtain ⟨e,finish,epc,e12,layoutE,futureE,rxE,appE,er,ec⟩ := MainHeaderReadSetup.contract B d parsed next.length pc source.fp source.layout room source.stack
    have stable : Stable e (MainHeaderReadSetup.memory parsed next.length) next s := by
      refine ⟨(er 2 (by decide)).trans source.sp,(er 8 (by decide)).trans source.fp,(er 19 (by decide)).trans source.uart,(er 22 (by decide)).trans source.one,
        layoutE,?_,appE s source.app,source.invariant,source.stack,?_⟩
      · intro i;exact (rxE ⟨i.val,by have := i.isLt;omega⟩).trans (source.bytes i)
      · exact (congrArg Prod.fst ec).trans source.masked
    have finalRegion : ViewFrame.Region ram (MainHeaderReadSetup.memory parsed next.length) 0x80ffeb90#32 132 := by
      intro i
      exact (MainHeaderReadSetup.frame parsed next.length _ (WordZero.separated 0x80ffeb90#32 (MainHeaderReadSetup.fp+452#32) 132 13 (by decide +kernel) (by decide +kernel) i)).trans (prefixRegion i)
    refine ⟨(14+4*pending.length)+pn+dn+13,e,_,by omega,?_,⟨epc,stable,e12,room,(er 18 (by decide)).trans d18⟩,ec.trans prefixCsr,?_,MainServeLayout.trans serveD (MainServeMemoryFrames.whole futureE (by decide)),finalRegion⟩
    · simpa only [List.append_nil] using prefixRun.trans finish.observed
    · intro rr safe
      have ne : ∀ r : Reg, r∈[21,23,26] → r∉MainHeaderReadSetup.writes := by decide +kernel
      exact (er rr (ne rr safe)).trans (bankD rr safe)
  | reject status =>
    refine ⟨(14+4*pending.length)+pn+dn,d,parsed,by omega,?_,?_,prefixCsr,bankD,serveD,prefixRegion⟩
    · simpa only [List.append_nil] using prefixRun
    · exact ⟨by simpa only [result] using cut,source,by simpa only [result] using view⟩
  | done head =>
    have d18 : d.get 18=2#32 := (show d.get 18=b.get 18 from by simpa only [result,MainHeaderDispatchTwo.Keeps18] using keep).trans b18
    refine ⟨(14+4*pending.length)+pn+dn,d,parsed,by omega,?_,?_,prefixCsr,bankD,serveD,prefixRegion⟩
    · simpa only [List.append_nil] using prefixRun
    · exact ⟨by simpa only [result] using cut,source,by simpa only [result] using view,d18⟩

end E5R.Thermostat.MainHeaderLoopRegs

namespace E5R.Thermostat.MainHeaderStreamRegs
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec MainHeaderLoopTwo
theorem contract_routes (wire : Nat → BitVec 8) (plan : MainHeaderStreamPlan.Plan) (fuel : Nat)
    {c ram input s} (h : MainHeaderLoopTwo.Ready c ram input s)
    (space : input.length+fuel≤2048) (valid : MainHeaderStreamPlan.Valid plan wire input.length fuel) :
    let r := consume wire fuel input
    ∃ n d after, n≤MainHeaderStreamPlan.cost plan input.length fuel ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (MainHeaderStreamPlan.logs plan input.length r.received) [] ∧
      MainHeaderLoopTwo.Boundary d after r.input s r.result ∧ d.sameCsr c ∧ MainGprBank.Frame c d ∧ MainServeLayout.Frame ram after ∧ ViewFrame.Region ram after 0x80ffeb90#32 132 := by
  change ∃ n d after, n≤MainHeaderStreamPlan.cost plan input.length fuel ∧
    Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (MainHeaderStreamPlan.logs plan input.length (consume wire fuel input).received) [] ∧
    MainHeaderLoopTwo.Boundary d after (consume wire fuel input).input s (consume wire fuel input).result ∧ d.sameCsr c ∧ MainGprBank.Frame c d ∧ MainServeLayout.Frame ram after ∧ ViewFrame.Region ram after 0x80ffeb90#32 132
  induction fuel generalizing c ram input with
  | zero => exact ⟨0,c,ram,by simp only [MainHeaderStreamPlan.cost];omega,.refl _,h,rfl,MainGprBank.refl c,MainServeLayout.refl ram,fun _ => rfl⟩
  | succ fuel ih =>
    obtain ⟨pendingOK,readyOK,datumOK⟩ := valid input.length (by omega) (by omega)
    have byteEq : (UartPoll.byte (plan.datum input.length)).setWidth 8=wire input.length := datumOK
    let next := input++[wire input.length]
    have nextLength : next.length=input.length+1 := by simp only [next,List.length_append,List.length_cons,List.length_nil,Nat.zero_add]
    have step := MainHeaderLoopRegs.contract_routes h (plan.pending input.length) (plan.ready input.length) (plan.datum input.length) pendingOK readyOK
    dsimp only at step
    rw [byteEq] at step
    obtain ⟨first,a,mid,firstBound,firstTrace,boundary,firstCsr,firstRegs,firstServe,firstRegion⟩ := step
    change MainHeaderLoopTwo.Boundary a mid next s (HttpRequestBytes.parse next 1024 1024) at boundary
    have firstBound' : first≤47+4*(plan.pending input.length).length+HeadColdFutureComplete.budget 1024 :=
      Nat.le_trans firstBound (Nat.add_le_add_left (MainHeaderStreamPlan.parser_budget next.length) _)
    cases result : HttpRequestBytes.parse next 1024 1024 with
    | incomplete =>
      have nextReady : MainHeaderLoopTwo.Ready a mid next s := by simpa only [result,MainHeaderLoopTwo.Boundary] using boundary
      have validNext : MainHeaderStreamPlan.Valid plan wire next.length fuel := by
        rw [nextLength]
        exact ChunkReceivePlan.valid_tail valid
      obtain ⟨rest,d,after,restBound,restTrace,post,csr,lastRegs,lastServe,lastRegion⟩ := ih nextReady (by rw [nextLength];omega) validNext
      have runEq : consume wire (fuel+1) input={ consume wire fuel next with received := (consume wire fuel next).received+1 } := by
        rw [consume]
        change (match HttpRequestBytes.parse next 1024 1024 with | .incomplete => _ | .reject _ => _ | .done _ => _)=_
        rw [result]
      rw [runEq]
      dsimp only
      refine ⟨first+rest,d,after,?_,?_,post,csr.trans firstCsr,MainGprBank.trans firstRegs lastRegs,MainServeLayout.trans firstServe lastServe,HeadRegionFrame.trans firstRegion lastRegion⟩
      · rw [nextLength] at restBound
        change first+rest≤47+4*(plan.pending input.length).length+HeadColdFutureComplete.budget 1024+MainHeaderStreamPlan.cost plan (input.length+1) fuel
        omega
      · have trace := firstTrace.trans restTrace
        simpa only [MainHeaderStreamPlan.logs,nextLength,List.append_nil] using trace
    | reject status =>
      have runEq : consume wire (fuel+1) input=⟨1,next,.reject status⟩ := by
        rw [consume]
        change (match HttpRequestBytes.parse next 1024 1024 with | .incomplete => _ | .reject _ => _ | .done _ => _)=_
        rw [result]
      rw [runEq]
      dsimp only
      refine ⟨first,a,mid,?_,?_,?_,firstCsr,firstRegs,firstServe,firstRegion⟩
      · change first≤47+4*(plan.pending input.length).length+HeadColdFutureComplete.budget 1024+MainHeaderStreamPlan.cost plan (input.length+1) fuel
        omega
      · simpa only [MainHeaderStreamPlan.logs,List.append_nil] using firstTrace
      · simpa only [result] using boundary
    | done head =>
      have runEq : consume wire (fuel+1) input=⟨1,next,.done head⟩ := by
        rw [consume]
        change (match HttpRequestBytes.parse next 1024 1024 with | .incomplete => _ | .reject _ => _ | .done _ => _)=_
        rw [result]
      rw [runEq]
      dsimp only
      refine ⟨first,a,mid,?_,?_,?_,firstCsr,firstRegs,firstServe,firstRegion⟩
      · change first≤47+4*(plan.pending input.length).length+HeadColdFutureComplete.budget 1024+MainHeaderStreamPlan.cost plan (input.length+1) fuel
        omega
      · simpa only [MainHeaderStreamPlan.logs,List.append_nil] using firstTrace
      · simpa only [result] using boundary

end E5R.Thermostat.MainHeaderStreamRegs

namespace E5R.Thermostat.MainHeaderResetBank
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec MainHeaderLoopTwo
theorem contract_routes (c : Core) (ram : Word → BitVec 8) (wire : Nat → BitVec 8)
    (plan : MainHeaderStreamPlan.Plan) (fuel : Nat)
    (hp : c.pc=0x80000000#32) (mpp : c.mpp=0 ∨ c.mpp=3) (masked : c.mie_=false)
    (stack : Memory.Block B 0x80ff0000#32 65536) (space : fuel≤2048)
    (valid : MainHeaderStreamPlan.Valid plan wire 0 fuel) :
    let r := consume wire fuel []
    ∃ n d after, n≤2550+MainHeaderStreamPlan.cost plan 0 fuel ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (MainHeaderStreamPlan.logs plan 0 r.received) [] ∧
      MainHeaderLoopTwo.Boundary d after r.input Spec.initial r.result ∧
      Observed.input (MainHeaderStreamPlan.logs plan 0 r.received)=r.input ∧
      r.result=HttpRequestBytes.parse r.input 1024 1024 ∧ MainGprBank.At d ∧ MainServeLayout.At after 0 ∧ InitRoutes.Layout after := by
  obtain ⟨old,oldRam,quiet,_,routes⟩ := MainHeaderFirstPoll.reset_routes B c ram hp mpp stack
  obtain ⟨a,mid,det,extended,two,bank,serve⟩ := MainHeaderFirstBank.reset_contract B c ram hp mpp stack
  have equal := DetRunUnique.steps quiet.det det
  rw [equal] at quiet
  have memoryEqual : oldRam=mid := congrArg Machine.ram equal
  rw [memoryEqual] at routes
  have boot : Quiet.Steps B img 2550 ⟨c,ram⟩ ⟨a,mid⟩ := quiet
  have ready : MainHeaderFirstPoll.Ready B a mid := ⟨extended.pc,extended.sp,extended.fp,extended.uart,extended.one,extended.zero,extended.dst,extended.stack,extended.app,extended.future,extended.masked,extended.header⟩
  obtain ⟨n,d,after,bound,trace,post,_,regs,serveFrame,protectedRegion⟩ := MainHeaderStreamRegs.contract_routes wire plan fuel (MainHeaderLoopTwo.first ready two) (by simpa only [List.length_nil,Nat.zero_add] using space) valid
  have inputEq := input_bytes wire fuel []
  have logs := MainHeaderStreamPlan.logs_wire plan wire 0 (consume wire fuel []).received fuel valid (received_le wire fuel [])
  have exactResult := exact_result wire fuel [] (by decide +kernel)
  refine ⟨2550+n,d,after,by simpa only [List.length_nil] using Nat.add_le_add_left bound 2550,?_,post,?_,exactResult,MainGprBank.preserve regs bank,MainServeLayout.preserve serveFrame serve,?_⟩
  · simpa only [List.nil_append,List.length_nil] using boot.observed.trans trace
  · simpa only [List.nil_append,List.length_nil] using logs.trans inputEq.symm
  · apply InitRoutes.layout_preserve mid after routes
    · simpa only [ViewFrame.Region,show 0x80ffeb90#32+72#32=0x80ffebd8#32 by decide +kernel] using HeadRegionFrame.sub protectedRegion 72 60 (by decide)
    · simpa only [ViewFrame.Region,show 0x80ffeb90#32+16#32=0x80ffeba0#32 by decide +kernel] using HeadRegionFrame.sub protectedRegion 16 4 (by decide)

end E5R.Thermostat.MainHeaderResetBank
