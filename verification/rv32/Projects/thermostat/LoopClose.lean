import Projects.thermostat.LoopPollEntry
import Projects.thermostat.ResetFutureSetupQuiet
set_option autoImplicit false
namespace E5R.Thermostat.LoopClose
open E5R E5R.Thermostat
abbrev B := UartPlatform.board
abbrev fp := 0x80fff814#32

/-- UART close is the actual outer serve restart: rebuild its future and
    receive storage, reset the request counter, retain the committed App, and
    reach the next UART poll. No TCP/FIFO flush or physical delivery is claimed. -/
theorem contract (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot)
    (hp : c.pc=0x80000978#32) (sp : c.get 2=0x80ffeb90#32) (frame : c.get 8=fp)
    (uart : c.get 19=0x10000000#32) (one : c.get 22=1#32) (two : c.get 18=2#32) (masked : c.mie_=false)
    (stack : Memory.Block B 0x80ff0000#32 65536) (app : AppState.At ram s) (inv : Spec.Inv s)
    (capacity : ramRead ram 0x80ffeba0#32 .w=2048#32) :
    ∃ d after, Quiet.Steps B img 118 ⟨c,ram⟩ ⟨d,after⟩ ∧ MainHeaderLoopTwo.Ready d after [] s ∧
      MainServeLayout.At after 0 ∧
      ViewFrame.Region ram after 0x80ffeba0#32 4 ∧ ViewFrame.Region ram after 0x80ffebd8#32 60 ∧ MainGprBank.Frame c d := by
  have main : Memory.Block B 0x80ffeb90#32 5232 := by
    have part := Memory.sub_block stack (off := 60304) (m := 5232) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=0x80ffeb90#32 by decide +kernel] using part
  let a := (FutureSetup.execute c ram).core
  let mid := FutureSetup.memory ram
  have setup : Quiet.Steps B img 59 ⟨c,ram⟩ ⟨a,mid⟩ := FutureSetup.contract_quiet B c ram hp sp frame main
  obtain ⟨pc,a1,a10,_,a12,a13,areg,acsr⟩ := FutureSetup.fields c ram
  have a2 : a.get 2=0x80ffeb90#32 := (areg 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans sp
  have a8 : a.get 8=fp := (areg 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans frame
  have a19 : a.get 19=0x10000000#32 := (areg 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans uart
  have a22 : a.get 22=1#32 := (areg 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans one
  have a18 : a.get 18=2#32 := (areg 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans two
  have region (p : Word) (n : Nat)
      (awayFuture : WordRegions.Disjoint p n fp 449)
      (awayCounter : WordRegions.Disjoint p n 0x80ffebb8#32 4) : ViewFrame.Region ram mid p n := by
    intro i
    exact FutureSetup.frame ram _ (awayFuture i) (awayCounter i)
  have appRegion := region 0x80ffebbc#32 25
    (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
  have appMid : AppState.At mid s := AppState.preserve ram mid s app appRegion
  have layout := MainHeaderLayout.initialized ram capacity
  have served := MainServeLayout.initialized ram capacity
  have maskA : a.mie_=false := (congrArg Prod.fst acsr).trans masked
  obtain ⟨d,after,poll,ready,metaRegion,capRegion,routeRegion,bankPoll⟩ := LoopPollEntry.parser a mid s pc a2 a8 a19 a22 a18 a1 a10 a13 a12 maskA stack appMid inv layout
  have serveAfter := MainServeLayout.preserve (MainServeLayout.region (ViewFrame.shrink metaRegion (by decide))) served
  refine ⟨d,after,setup.trans poll,ready,serveAfter,?_,?_,?_⟩
  · have first := region 0x80ffeba0#32 4
      (WordRegions.before _ _ _ _ (by decide) (by decide))
      (WordRegions.before _ _ _ _ (by decide) (by decide))
    exact fun i => (capRegion i).trans (first i)
  · have first := region 0x80ffebd8#32 60
      (WordRegions.before _ _ _ _ (by decide) (by decide))
      (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    exact fun i => (routeRegion i).trans (first i)

  · intro rr safe
    have casesReg : rr=21 ∨ rr=23 ∨ rr=26 := by
      simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using safe
    apply (bankPoll rr safe).trans
    rcases casesReg with eq|eq|eq <;> subst rr
    all_goals exact areg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
end E5R.Thermostat.LoopClose
