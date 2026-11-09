import Projects.thermostat.LoopKeepPrefix
import Projects.thermostat.LoopKeepFrames
import Projects.thermostat.LoopPollEntry
set_option autoImplicit false
namespace E5R.Thermostat.LoopKeep
open E5R E5R.Thermostat
abbrev B := UartPlatform.board
abbrev fp := 0x80fff814#32
abbrev rx := 0x80ffec14#32

/-- Real keep completion through checked zero memmove, twelve actual rebuild
    stores, empty parser poll and next UART RX. The zero-leftover word premises
    must be supplied by transaction reception and the handler/sender frames. -/
theorem contract (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot) (served : Nat) (used : Word)
    (hp : c.pc=0x800017be#32) (sp : c.get 2=0x80ffeb90#32) (frame : c.get 8=fp)
    (uart : c.get 19=0x10000000#32) (one : c.get 22=1#32) (two : c.get 18=2#32) (masked : c.mie_=false)
    (stack : Memory.Block B 0x80ff0000#32 65536) (app : AppState.At ram s) (inv : Spec.Inv s)
    (serve : MainServeLayout.At ram served)
    (headLimit : ramRead ram (fp+76#32) .w=1024#32) (bodyLimit : ramRead ram (fp+80#32) .w=1024#32)
    (filled : ramRead ram (fp+84#32) .w=used) (consumed : ramRead ram (fp+92#32) .w=used) (bound : used.toNat≤2048) :
    ∃ d after, Quiet.Steps B img 115 ⟨c,ram⟩ ⟨d,after⟩ ∧ MainHeaderLoopTwo.Ready d after [] s ∧
      MainServeLayout.At after served ∧
      ViewFrame.Region ram after 0x80ffeba0#32 4 ∧ ViewFrame.Region ram after 0x80ffebd8#32 60 ∧ MainGprBank.Frame c d := by
  have object : Memory.Block B fp 449 := by
    have part := Memory.sub_block stack (off := 63508) (m := 449) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+63508#32=fp by decide +kernel] using part
  obtain ⟨a,entry,pc,a12,a11,a10,_,a1,areg,acsr⟩ := LoopKeepPrefix.contract B c ram used frame serve.capacity filled consumed serve.rx bound
    (Memory.sub_block object (off := 0) (m := 96) (by decide) (by decide)) hp
  have a2 : a.get 2=0x80ffeb90#32 := (areg 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans sp
  have a8 : a.get 8=fp := (areg 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans frame
  have a19 : a.get 19=0x10000000#32 := (areg 19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans uart
  have a22 : a.get 22=1#32 := (areg 22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans one
  have a18 : a.get 18=2#32 := (areg 18 (by decide) (by decide) (by decide) (by decide) (by decide)).trans two
  have moveStack : Memory.Block B 0x80ffeb70#32 32 := by
    have part := Memory.sub_block stack (off := 60272) (m := 32) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60272#32=0x80ffeb70#32 by decide +kernel] using part
  obtain ⟨b,move,bpc,_,b2,_,_,b8,breg,bcsr⟩ := LoopMemmoveZero.contract B a ram rx (rx+used) fp a2 a8 a10 a11 a12 a1 moveStack pc
  let mid := LoopMemmoveZero.memory ram rx (rx+used) fp
  have moveRegion (p : Word) (n : Nat) (away : WordRegions.Disjoint p n 0x80ffeb8c#32 4) :
      ViewFrame.Region ram mid p n := LoopKeepFrames.move_region ram rx (rx+used) fp p n away
  have movedHeader : ViewFrame.Region ram mid fp 449 := moveRegion fp 449
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
  have movedServe := MainServeLayout.preserve (MainServeLayout.region (ViewFrame.shrink movedHeader (by decide))) serve
  have movedApp : AppState.At mid s := AppState.preserve ram mid s app (moveRegion _ _
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide))))
  obtain ⟨e,rebuild,epc,e10,e12,_,_,_,_,ereg,ecsr⟩ := LoopKeepRebuild.contract B b mid used b2 b8
    ((ViewFrame.word movedHeader 92 (by decide)).trans consumed)
    ((ViewFrame.word movedHeader 84 (by decide)).trans filled) movedServe.uart movedServe.rx movedServe.capacity object bpc
  let rebuilt := LoopKeepRebuild.memory mid used
  have rebuildRegion (p : Word) (n : Nat) (away : WordRegions.Disjoint p n fp 449) :
      ViewFrame.Region mid rebuilt p n := LoopKeepFrames.rebuild_region mid used p n away
  have rebuiltApp : AppState.At rebuilt s := AppState.preserve mid rebuilt s movedApp (rebuildRegion _ _
    (WordRegions.before _ _ _ _ (by decide) (by decide)))
  have rebuiltLayout := LoopKeepLayout.header mid used
    ((ViewFrame.word movedHeader 76 (by decide)).trans headLimit)
    ((ViewFrame.word movedHeader 80 (by decide)).trans bodyLimit)
  have rebuiltServe := LoopKeepLayout.serve used movedServe
  have b19 : b.get 19=0x10000000#32 := (breg 19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans a19
  have b22 : b.get 22=1#32 := (breg 22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans a22
  have b18 : b.get 18=2#32 := (breg 18 (by decide) (by decide) (by decide) (by decide) (by decide)).trans a18
  have e2 : e.get 2=0x80ffeb90#32 := (ereg 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b2
  have e8 : e.get 8=fp := (ereg 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b8
  have e19 : e.get 19=0x10000000#32 := (ereg 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b19
  have e22 : e.get 22=1#32 := (ereg 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b22
  have e18 : e.get 18=2#32 := (ereg 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b18
  have maskedE : e.mie_=false := (congrArg Prod.fst (ecsr.trans (bcsr.trans acsr))).trans masked
  obtain ⟨d,after,poll,ready,pollHeader,pollCap,pollRoutes,bankPoll⟩ := LoopPollEntry.contract e rebuilt s epc e2 e8 e19 e22 e18 e12 maskedE stack rebuiltApp inv rebuiltLayout
  have finalServe := MainServeLayout.preserve (MainServeLayout.region (ViewFrame.shrink pollHeader (by decide))) rebuiltServe
  refine ⟨d,after,((entry.trans move).trans rebuild).trans poll,ready,finalServe,?_,?_,?_⟩
  · have moved := moveRegion 0x80ffeba0#32 4 (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    have reset := rebuildRegion 0x80ffeba0#32 4 (WordRegions.before _ _ _ _ (by decide) (by decide))
    exact fun i => (pollCap i).trans ((reset i).trans (moved i))
  · have moved := moveRegion 0x80ffebd8#32 60 (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    have reset := rebuildRegion 0x80ffebd8#32 60 (WordRegions.before _ _ _ _ (by decide) (by decide))
    exact fun i => (pollRoutes i).trans ((reset i).trans (moved i))

  · intro rr safe
    have casesReg : rr=21 ∨ rr=23 ∨ rr=26 := by
      simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using safe
    apply (bankPoll rr safe).trans
    rcases casesReg with eq|eq|eq <;> subst rr
    all_goals
      exact (ereg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((breg _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          (areg _ (by decide) (by decide) (by decide) (by decide) (by decide)))
end E5R.Thermostat.LoopKeep
