import Projects.thermostat.LoopEmptyEntry
import Projects.thermostat.ResetHeadEmptyQuiet
import Projects.thermostat.ResetReadMoreQuiet
import Projects.thermostat.MainHeaderLoopTwo
import Projects.thermostat.MainServeLayout
import Projects.thermostat.MainRouterTable
import Projects.thermostat.MainGprBank
set_option autoImplicit false
namespace E5R.Thermostat.LoopPollEntry
open E5R E5R.Thermostat
abbrev B := UartPlatform.board
abbrev fp := 0x80fff814#32

/-- The rebuilt empty receive future is actually polled, parsed as incomplete,
    and returned to UART RX, for an arbitrary committed App state. -/
theorem parser (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot)
    (hp : c.pc=0x80002c46#32) (sp : c.get 2=0x80ffeb90#32) (frame : c.get 8=fp)
    (uart : c.get 19=0x10000000#32) (one : c.get 22=1#32) (two : c.get 18=2#32)
    (ret : c.get 1=0x80000a26#32) (out : c.get 10=0x80fffd38#32) (config : c.get 13=0x80fff860#32)
    (zero : c.get 12=0#32) (masked : c.mie_=false)
    (stack : Memory.Block B 0x80ff0000#32 65536)
    (app : AppState.At ram s) (inv : Spec.Inv s) (layout : MainHeaderLayout.At ram 0) :
    ∃ d after, Quiet.Steps B img 59 ⟨c,ram⟩ ⟨d,after⟩ ∧ MainHeaderLoopTwo.Ready d after [] s ∧
      ViewFrame.Region ram after fp 449 ∧ ViewFrame.Region ram after 0x80ffeba0#32 4 ∧
      ViewFrame.Region ram after 0x80ffebd8#32 60 ∧ MainGprBank.Frame c d := by
  let b := (HeadEmpty.execute c ram).core
  let mid := HeadEmpty.memory c ram
  have emptyRun : Quiet.Steps B img 38 ⟨c,ram⟩ ⟨b,mid⟩ :=
    HeadEmpty.execute_contract_quiet B c ram hp sp ret out zero config layout.head.headLimit stack
  obtain ⟨bpc,bsp,_,bcsr⟩ := HeadEmpty.fields c ram
  have b8 : b.get 8=fp := (show b.get 8=c.get 8 from by simpa only [HeadEmpty.reg] using HeadEmpty.saved c ram ⟨0,by decide⟩).trans frame
  have b19 : b.get 19=0x10000000#32 := (show b.get 19=c.get 19 from by simpa only [HeadEmpty.reg] using HeadEmpty.saved c ram ⟨3,by decide⟩).trans uart
  have b22 : b.get 22=1#32 := (show b.get 22=c.get 22 from by simpa only [HeadEmpty.reg] using HeadEmpty.saved c ram ⟨6,by decide⟩).trans one
  have b18 : b.get 18=2#32 := (show b.get 18=c.get 18 from by simpa only [HeadEmpty.reg] using HeadEmpty.saved c ram ⟨2,by decide⟩).trans two
  have headRegion (p : Word) (n : Nat)
      (awayStack : WordRegions.Disjoint p n 0x80ffea10#32 384)
      (awayResult : WordRegions.Disjoint p n 0x80fffd38#32 8) : ViewFrame.Region ram mid p n := by
    intro i
    exact HeadEmpty.frame c ram _ (awayStack i) (awayResult i)
  have headerRegion : ViewFrame.Region ram mid fp 449 := headRegion fp 449
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
  have midLayout := MainHeaderLayout.preserve layout headerRegion
  have incomplete := HeadEmpty.incomplete c ram
  let d := (ReadMore.execute b mid).core
  let after := ReadMore.memory mid
  have receiveRun : Quiet.Steps B img 21 ⟨b,mid⟩ ⟨d,after⟩ :=
    ReadMore.execute_contract_quiet B b mid bpc b8 incomplete.1 incomplete.2 midLayout.filledPtr
      midLayout.capacity midLayout.filled midLayout.head.rx midLayout.uartPtr stack
  obtain ⟨dpc,_,dst,dreg,dcsr⟩ := ReadMore.fields b mid
  have finalRegion (p : Word) (n : Nat)
      (awayStack : WordRegions.Disjoint p n 0x80ffea10#32 384)
      (awayResult : WordRegions.Disjoint p n 0x80fffd38#32 8)
      (awayReceive : WordRegions.Disjoint p n 0x80fff9d8#32 13) : ViewFrame.Region ram after p n := by
    intro i
    exact (ReadMore.frame mid _ (awayReceive i)).trans (headRegion p n awayStack awayResult i)
  have finalMeta : ViewFrame.Region ram after fp 449 := finalRegion fp 449
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
  have appRegion : ViewFrame.Region ram after 0x80ffebbc#32 25 := finalRegion _ _
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
  have allCsr := dcsr.trans bcsr
  have ready : MainHeaderLoopTwo.Ready d after [] s := by
    refine ⟨dpc,⟨(dreg 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans bsp,
      (dreg 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans b8,
      (dreg 19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans b19,
      (dreg 22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans b22,
      MainHeaderLayout.preserve layout finalMeta,fun i => Fin.elim0 i,
      AppState.preserve ram after s app appRegion,inv,stack,(congrArg Prod.fst allCsr).trans masked⟩,?_,by decide,?_⟩
    · simpa only [List.length_nil,BitVec.add_zero] using dst
    · exact (dreg 18 (by decide) (by decide) (by decide) (by decide) (by decide)).trans b18
  refine ⟨d,after,emptyRun.trans receiveRun,ready,finalMeta,?_,?_,?_⟩
  ·
    exact finalRegion _ _
      (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
      (WordRegions.before _ _ _ _ (by decide) (by decide))
      (WordRegions.before _ _ _ _ (by decide) (by decide))
  ·
    exact finalRegion _ _
      (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
      (WordRegions.before _ _ _ _ (by decide) (by decide))
      (WordRegions.before _ _ _ _ (by decide) (by decide))
  · intro rr safe
    have casesReg : rr=21 ∨ rr=23 ∨ rr=26 := by
      simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using safe
    rcases casesReg with eq|eq|eq <;> subst rr
    · exact (dreg 21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (show b.get 21=c.get 21 from by simpa only [HeadEmpty.reg] using HeadEmpty.saved c ram ⟨5,by decide⟩)
    · exact (dreg 23 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (show b.get 23=c.get 23 from by simpa only [HeadEmpty.reg] using HeadEmpty.saved c ram ⟨7,by decide⟩)
    · exact (dreg 26 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (show b.get 26=c.get 26 from by simpa only [HeadEmpty.reg] using HeadEmpty.saved c ram ⟨10,by decide⟩)


theorem contract (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot)
    (hp : c.pc=0x80000a10#32) (sp : c.get 2=0x80ffeb90#32) (frame : c.get 8=fp)
    (uart : c.get 19=0x10000000#32) (one : c.get 22=1#32) (two : c.get 18=2#32)
    (zero : c.get 12=0#32) (masked : c.mie_=false)
    (stack : Memory.Block B 0x80ff0000#32 65536)
    (app : AppState.At ram s) (inv : Spec.Inv s) (layout : MainHeaderLayout.At ram 0) :
    ∃ d after, Quiet.Steps B img 66 ⟨c,ram⟩ ⟨d,after⟩ ∧ MainHeaderLoopTwo.Ready d after [] s ∧
      ViewFrame.Region ram after fp 449 ∧ ViewFrame.Region ram after 0x80ffeba0#32 4 ∧
      ViewFrame.Region ram after 0x80ffebd8#32 60 ∧ MainGprBank.Frame c d := by
  have object : Memory.Block B fp 436 := by
    have part := Memory.sub_block stack (off := 63508) (m := 436) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+63508#32=fp by decide +kernel] using part
  obtain ⟨a,entry,pc,a11,a13,a10,a1,areg,acsr⟩ := LoopEmptyEntry.contract B c ram sp frame layout.head.rx layout.head.config object hp
  have a2 := (areg 2 (by decide) (by decide) (by decide) (by decide)).trans sp
  have a8 := (areg 8 (by decide) (by decide) (by decide) (by decide)).trans frame
  have a19 := (areg 19 (by decide) (by decide) (by decide) (by decide)).trans uart
  have a22 := (areg 22 (by decide) (by decide) (by decide) (by decide)).trans one
  have a18 := (areg 18 (by decide) (by decide) (by decide) (by decide)).trans two
  have a12 := (areg 12 (by decide) (by decide) (by decide) (by decide)).trans zero
  have maskA := (congrArg Prod.fst acsr).trans masked
  obtain ⟨d,after,poll,ready,region,capacity,routes,bank⟩ := parser a ram s pc a2 a8 a19 a22 a18 a1 a10 a13 a12 maskA stack app inv layout
  refine ⟨d,after,entry.trans poll,ready,region,capacity,routes,?_⟩
  intro rr safe
  have casesReg : rr=21 ∨ rr=23 ∨ rr=26 := by
    simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using safe
  apply (bank rr safe).trans
  rcases casesReg with eq|eq|eq <;> subst rr
  all_goals exact areg _ (by decide) (by decide) (by decide) (by decide)

end E5R.Thermostat.LoopPollEntry
