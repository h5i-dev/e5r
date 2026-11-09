import Projects.thermostat.ChunkRejectBranch
import Projects.thermostat.RejectBodyResponse
set_option autoImplicit false
namespace E5R.Thermostat.ChunkRejectFinish
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

theorem contract (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot) (served status : Nat)
    (pc : c.pc=0x8000106c#32) (tag : c.get 10=3#32) (two : c.get 18=2#32)
    (error : c.get 27=BitVec.ofNat 32 status) (sp : c.get 2=0x80ffeb90#32) (fp : c.get 8=0x80fff814#32)
    (uart : c.get 19=0x10000000#32) (one : c.get 22=1#32) (masked : c.mie_=false)
    (stack : Memory.Block B 0x80ff0000#32 65536) (app : AppState.At ram s) (inv : Spec.Inv s)
    (bank : MainGprBank.At c) (serve : MainServeLayout.At ram served)
    (capacity : ramRead ram 0x80ffeba0#32 .w=2048#32) (routes : MainRouterTable.At ram)
    (lo : 200≤status) (hi : status≤599)
    (slots : List UartTxLoop.Slot) (length : slots.length=(ResponseHeadSpec.bytes status [] 0 true).length) :
    ∃ d n after, n≤3322+UartWriteAll.time (ResponseHeadSpec.bytes status [] 0 true) slots ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads slots)
        (UartTxLoop.events (ResponseHeadSpec.bytes status [] 0 true)) ∧ LoopReady.At d after s 0 := by
  obtain ⟨a,branch,apc,a18,a9,ar,ac⟩ := ChunkRejectBranch.contract B c ram tag two pc
  have cut : MainHeaderDispatchTwo.At a (.reject status) := ⟨apc,a18,(ar 27 (by decide) (by decide)).trans error,a9⟩
  have bankA := MainGprBank.preserve (fun r mem => by
    have ne : ∀ r : Reg, r∈[21,23,26] → r≠18 ∧ r≠9 := by decide +kernel
    obtain ⟨n18,n9⟩ := ne r mem
    exact ar r n18 n9) bank
  obtain ⟨d,n,after,bound,response,ready⟩ := RejectBodyResponse.contract a ram s served status cut
    ((ar 2 (by decide) (by decide)).trans sp) ((ar 8 (by decide) (by decide)).trans fp)
    ((ar 19 (by decide) (by decide)).trans uart) ((ar 22 (by decide) (by decide)).trans one)
    ((congrArg Prod.fst ac).trans masked) stack app inv bankA serve capacity routes lo hi slots length
  exact ⟨d,4+n,after,by omega,by simpa only [List.nil_append] using branch.observed.trans response,ready⟩
end E5R.Thermostat.ChunkRejectFinish
