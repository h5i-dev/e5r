import Projects.thermostat.LoopKeep
import Projects.thermostat.LoopClose
import Projects.thermostat.MainRouterResetFrame
import Projects.thermostat.MainHeaderFirstBank
set_option autoImplicit false
namespace E5R.Thermostat.LoopReady
open E5R E5R.Thermostat
abbrev B := UartPlatform.board
abbrev fp := 0x80fff814#32

/-- The reusable actual UART-receive boundary includes caller bank and static
    words required by the next real parser/router execution. -/
structure At (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot) (served : Nat) : Prop where
  receive : MainHeaderLoopTwo.Ready c ram [] s
  bank : MainGprBank.At c
  serve : MainServeLayout.At ram served
  room : served<100
  capacity : ramRead ram 0x80ffeba0#32 .w=2048#32
  routes : MainRouterTable.At ram

/-- Reset initializes the same reusable boundary, including all route bytes,
    the separate receive-capacity word, caller bank and zero request counter. -/
theorem reset (c : Core) (ram : Word → BitVec 8) (pc : c.pc=0x80000000#32)
    (mpp : c.mpp=0 ∨ c.mpp=3) (stack : Memory.Block B 0x80ff0000#32 65536) :
    ∃ d after, Quiet.Steps B img 2550 ⟨c,ram⟩ ⟨d,after⟩ ∧ At d after Spec.initial 0 := by
  obtain ⟨a,mid,trace,post,routes⟩ := MainHeaderFirstPoll.reset_routes B c ram pc mpp stack
  obtain ⟨d,after,det,_,two,bank,serve⟩ := MainHeaderFirstBank.reset_contract B c ram pc mpp stack
  have same := DetRunUnique.steps trace.det det
  have coreEq := congrArg Machine.core same
  have ramEq := congrArg Machine.ram same
  dsimp only at coreEq ramEq
  subst d
  subst after
  exact ⟨a,mid,trace,⟨MainHeaderLoopTwo.first post two,bank,serve,by decide,routes.2,MainRouterTable.initialized routes⟩⟩

/-- Actual completed transaction through keep/restart, including the zero
    unread-byte case derived by T1 reception. This is an interior join; upstream
    transaction proofs must supply every listed word and register fact. -/
theorem completed (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot) (served : Nat) (used : Word) (close : Bool)
    (pc : c.pc=(if close then 0x80000978#32 else 0x800017be#32))
    (sp : c.get 2=0x80ffeb90#32) (frame : c.get 8=fp) (uart : c.get 19=0x10000000#32)
    (one : c.get 22=1#32) (two : c.get 18=2#32) (masked : c.mie_=false)
    (stack : Memory.Block B 0x80ff0000#32 65536) (app : AppState.At ram s) (inv : Spec.Inv s)
    (bank : MainGprBank.At c) (serve : MainServeLayout.At ram served)
    (room : close=false → served<100) (capacity : ramRead ram 0x80ffeba0#32 .w=2048#32) (routes : MainRouterTable.At ram)
    (headLimit : ramRead ram (fp+76#32) .w=1024#32) (bodyLimit : ramRead ram (fp+80#32) .w=1024#32)
    (filled : ramRead ram (fp+84#32) .w=used) (consumed : ramRead ram (fp+92#32) .w=used) (bound : used.toNat≤2048) :
    ∃ n d after, n≤118 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧ At d after s (if close then 0 else served) := by
  cases close with
  | false =>
    obtain ⟨d,after,steps,ready,serveAfter,capFrame,routeFrame,bankFrame⟩ := LoopKeep.contract c ram s served used
      pc sp frame uart one two masked stack app inv serve headLimit bodyLimit filled consumed bound
    have capWord := ViewFrame.word capFrame 0 (by decide)
    simp only [BitVec.add_zero] at capWord
    exact ⟨115,d,after,by decide,steps,⟨ready,MainGprBank.preserve bankFrame bank,serveAfter,room rfl,
      capWord.trans capacity,MainRouterTable.preserve routes routeFrame⟩⟩
  | true =>
    obtain ⟨d,after,steps,ready,serveAfter,capFrame,routeFrame,bankFrame⟩ := LoopClose.contract c ram s
      pc sp frame uart one two masked stack app inv capacity
    have capWord := ViewFrame.word capFrame 0 (by decide)
    simp only [BitVec.add_zero] at capWord
    exact ⟨118,d,after,by decide,steps,⟨ready,MainGprBank.preserve bankFrame bank,serveAfter,(by change (0 : Nat)<100;decide),
      capWord.trans capacity,MainRouterTable.preserve routes routeFrame⟩⟩
end E5R.Thermostat.LoopReady
