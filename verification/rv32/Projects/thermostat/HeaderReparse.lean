import Projects.thermostat.MainHeaderLoopRegs
import Projects.thermostat.MainRouterBankHeaderFrames
set_option autoImplicit false
namespace E5R.Thermostat.HeaderReparse
open E5R E5R.Thermostat HttpRequestSpec MainHeaderLoopTwo

/-- Actual quiet reparse boundary after the new RBR byte and real filled-word
    stores. It does not assume the parser result or a future input arrival. -/
structure Ready (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (s : Spec.Snapshot) : Prop where
  pc : c.pc=0x80000a10#32
  stable : MainHeaderLoopTwo.Stable c ram input s
  count : c.get 12=BitVec.ofNat 32 input.length
  two : c.get 18=2#32

/-- No MMIO occurs through the real parser/dispatch/renewed-slice path. This
    quiet suffix supplies safety for every intermediate instruction, including
    arbitrary incomplete or rejected prefixes; it stops at the next cutpoint. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot}
    (h : Ready c ram input s) :
    ∃ n d after,n≤47+HeadColdFutureComplete.budget (min input.length 1024) ∧
      Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      MainHeaderLoopTwo.Boundary d after input s (HttpRequestBytes.parse input 1024 1024) ∧
      d.sameCsr c ∧ MainGprBank.Frame c d ∧ MainServeLayout.Frame ram after ∧ ViewFrame.Region ram after 0x80ffeb90#32 132 := by
  let next := input
  have nextBound : next.length≤2048 := h.stable.layout.bound
  have parserStack : Memory.Block B 0x80ffea10#32 5312 := by
    have block := Memory.sub_block (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 59920) (m := 5312) h.stable.stack (by decide) (by decide)
    simpa only [show 0x80ff0000#32+59920#32=0x80ffea10#32 by decide +kernel] using block
  have object : Memory.Block B fp 1326 := by
    have block := Memory.sub_block (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 63508) (m := 1326) h.stable.stack (by decide) (by decide)
    simpa only [show 0x80ff0000#32+63508#32=fp by decide +kernel] using block
  have clOutside : ∀ q : Fin 14, B.inRam (BitVec.ofNat 32 (0x80005de0+q.val)) 1=false := by decide +kernel
  have teOutside : ∀ q : Fin 17, B.inRam (BitVec.ofNat 32 (0x80005dee+q.val)) 1=false := by decide +kernel
  obtain ⟨pn,b,parsed,plo,phi,parse,bpc,bsp,saved,view,rxFrame,future,_,parserRegion,bc⟩ := MainHeadParser.contract_routes B c ram next h.pc h.stable.sp h.stable.fp h.count h.stable.layout.head h.stable.bytes nextBound parserStack clOutside teOutside
  dsimp only [next] at phi
  have bfp : b.get 8=fp := saved.x8.trans h.stable.fp
  have buart : b.get 19=0x10000000#32 := saved.x19.trans h.stable.uart
  have bone : b.get 22=1#32 := saved.x22.trans h.stable.one
  have b18 : b.get 18=2#32 := saved.x18.trans h.two
  obtain ⟨dn,d,dlo,dhi,dispatch,cut,dr,dc,keep⟩ := MainHeaderDispatchTwo.contract B b parsed fp (HttpRequestBytes.parse next 1024 1024) bpc bfp bone view object (by decide +kernel)
  have layoutB : MainHeaderLayout.At parsed next.length := MainHeaderLayout.preserve h.stable.layout future
  have bytesB : Bytes.At parsed rx next := by intro i;exact (rxFrame ⟨i.val,by have := i.isLt;omega⟩).trans (h.stable.bytes i)
  have source : Stable d parsed next s := by
    refine ⟨(dr 2 (by decide)).trans bsp,(dr 8 (by decide)).trans bfp,(dr 19 (by decide)).trans buart,(dr 22 (by decide)).trans bone,
      layoutB,bytesB,AppState.preserve ram parsed s h.stable.app (by simpa only [ViewFrame.Region,show 0x80ffeb90#32+44#32=0x80ffebbc#32 by decide +kernel] using HeadRegionFrame.sub parserRegion 44 25 (by decide)),h.stable.invariant,h.stable.stack,?_⟩
    exact (congrArg Prod.fst (dc.trans bc)).trans h.stable.masked
  have prefixRun := parse.trans dispatch
  have prefixCsr := dc.trans bc
  have serveD : MainServeLayout.Frame ram parsed := MainServeMemoryFrames.whole future (by decide)
  have bankD : MainGprBank.Frame c d := by
    intro rr safe
    have casesReg : rr=21 ∨ rr=23 ∨ rr=26 := by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using safe
    rcases casesReg with h|h|h <;> subst rr
    · exact (dr 21 (by decide)).trans saved.x21
    · exact (dr 23 (by decide)).trans saved.x23
    · exact (dr 26 (by decide)).trans saved.x26
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
      exact (MainHeaderReadSetup.frame parsed next.length _ (WordZero.separated 0x80ffeb90#32 (MainHeaderReadSetup.fp+452#32) 132 13 (by decide +kernel) (by decide +kernel) i)).trans (parserRegion i)
    refine ⟨pn+dn+13,e,_,by omega,?_,⟨epc,stable,e12,room,(er 18 (by decide)).trans d18⟩,ec.trans prefixCsr,?_,MainServeLayout.trans serveD (MainServeMemoryFrames.whole futureE (by decide)),finalRegion⟩
    · simpa only [List.append_nil] using prefixRun.trans finish
    · intro rr safe
      have ne : ∀ r : Reg, r∈[21,23,26] → r∉MainHeaderReadSetup.writes := by decide +kernel
      exact (er rr (ne rr safe)).trans (bankD rr safe)
  | reject status =>
    refine ⟨pn+dn,d,parsed,by omega,?_,?_,prefixCsr,bankD,serveD,parserRegion⟩
    · simpa only [List.append_nil] using prefixRun
    · exact ⟨by simpa only [result] using cut,source,by simpa only [result] using view⟩
  | done head =>
    have d18 : d.get 18=2#32 := (show d.get 18=b.get 18 from by simpa only [result,MainHeaderDispatchTwo.Keeps18] using keep).trans b18
    refine ⟨pn+dn,d,parsed,by omega,?_,?_,prefixCsr,bankD,serveD,parserRegion⟩
    · simpa only [List.append_nil] using prefixRun
    · exact ⟨by simpa only [result] using cut,source,by simpa only [result] using view,d18⟩
end E5R.Thermostat.HeaderReparse
