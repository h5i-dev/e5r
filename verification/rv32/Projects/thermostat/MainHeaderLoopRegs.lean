import Projects.thermostat.MainHeaderLoopTwo
import Projects.thermostat.MainGprBank
import Projects.thermostat.MainHeaderAppendServe
namespace E5R.Thermostat.MainHeaderLoopRegs
open E5R E5R.Thermostat HttpRequestSpec MainHeaderLoopTwo
/-- One complete real header receive/reparse iteration, including actual main
    result dispatch and renewed receive-slice construction on Incomplete.
    A finite read schedule supplies progress; all command/header bytes remain
    derived from the actual RBR byte appended to the real receive buffer. -/
theorem contract {c ram input s} (h : Ready c ram input s) (pending : List Word) (ready datum : Word)
    (notReady : ∀ status ∈ pending, UartPoll.byte status &&& 1#32=0#32) (isReady : UartPoll.byte ready &&& 1#32≠0#32) :
    let next := input++[(UartPoll.byte datum).setWidth 8]
    ∃ n d after, n≤47+4*pending.length+HeadColdFutureComplete.budget (min next.length 1024) ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (MainHeaderWait.reads pending ready datum) [] ∧
      Boundary d after next s (HttpRequestBytes.parse next 1024 1024) ∧ d.sameCsr c ∧ MainGprBank.Frame c d ∧ MainServeLayout.Frame ram after := by
  let next := input++[(UartPoll.byte datum).setWidth 8]
  change ∃ n d after, n≤47+4*pending.length+HeadColdFutureComplete.budget (min next.length 1024) ∧
    Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (MainHeaderWait.reads pending ready datum) [] ∧
    Boundary d after next s (HttpRequestBytes.parse next 1024 1024) ∧ d.sameCsr c ∧ MainGprBank.Frame c d ∧ MainServeLayout.Frame ram after
  have room0 := h.room
  obtain ⟨a,mid,receive,apc,a12,layoutA,bytesA,appA,ar,ac,serveA⟩ := MainHeaderAppendServe.contract c ram input pending ready datum h.pc h.stable.fp h.stable.uart h.stable.one h.dst
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
  obtain ⟨pn,b,parsed,plo,phi,parse,bpc,bsp,saved,view,rxFrame,future,_,appB,bc⟩ := MainHeadParser.contract B a mid next apc asp afp a12 layoutA.head bytesA nextBound parserStack clOutside teOutside
  have bfp : b.get 8=fp := saved.x8.trans afp
  have buart : b.get 19=0x10000000#32 := saved.x19.trans auart
  have bone : b.get 22=1#32 := saved.x22.trans aone
  have b18 : b.get 18=2#32 := saved.x18.trans a18
  obtain ⟨dn,d,dlo,dhi,dispatch,cut,dr,dc,keep⟩ := MainHeaderDispatchTwo.contract B b parsed fp (HttpRequestBytes.parse next 1024 1024) bpc bfp bone view object (by decide +kernel)
  have layoutB : MainHeaderLayout.At parsed next.length := MainHeaderLayout.preserve layoutA future
  have bytesB : Bytes.At parsed rx next := by intro i;exact (rxFrame ⟨i.val,by have := i.isLt;omega⟩).trans (bytesA i)
  have source : Stable d parsed next s := by
    refine ⟨(dr 2 (by decide)).trans bsp,(dr 8 (by decide)).trans bfp,(dr 19 (by decide)).trans buart,(dr 22 (by decide)).trans bone,
      layoutB,bytesB,appB s (appA s h.stable.app),h.stable.invariant,h.stable.stack,?_⟩
    exact (congrArg Prod.fst ((dc.trans bc).trans ac)).trans h.stable.masked
  have prefixRun := (receive.trans parse.observed).trans dispatch.observed
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
    refine ⟨(14+4*pending.length)+pn+dn+13,e,_,by omega,?_,⟨epc,stable,e12,room,(er 18 (by decide)).trans d18⟩,ec.trans prefixCsr,?_,MainServeLayout.trans serveD (MainServeMemoryFrames.whole futureE (by decide))⟩
    · simpa only [List.append_nil] using prefixRun.trans finish.observed
    · intro rr safe
      have ne : ∀ r : Reg, r∈[21,23,26] → r∉MainHeaderReadSetup.writes := by decide +kernel
      exact (er rr (ne rr safe)).trans (bankD rr safe)
  | reject status =>
    refine ⟨(14+4*pending.length)+pn+dn,d,parsed,by omega,?_,?_,prefixCsr,bankD,serveD⟩
    · simpa only [List.append_nil] using prefixRun
    · exact ⟨by simpa only [result] using cut,source,by simpa only [result] using view⟩
  | done head =>
    have d18 : d.get 18=2#32 := (show d.get 18=b.get 18 from by simpa only [result,MainHeaderDispatchTwo.Keeps18] using keep).trans b18
    refine ⟨(14+4*pending.length)+pn+dn,d,parsed,by omega,?_,?_,prefixCsr,bankD,serveD⟩
    · simpa only [List.append_nil] using prefixRun
    · exact ⟨by simpa only [result] using cut,source,by simpa only [result] using view,d18⟩
end E5R.Thermostat.MainHeaderLoopRegs
