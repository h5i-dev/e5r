import Projects.thermostat.LoopReady
import Projects.thermostat.StackAccess
import Projects.thermostat.StackLoopClose
import Projects.thermostat.StackLoopKeep
set_option autoImplicit false
namespace E5R.Thermostat.StackLoopReady
open E5R E5R.Thermostat LoopReady
abbrev B := StackBoard.board
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
    obtain ⟨d,after,steps,ready,serveAfter,capFrame,routeFrame,bankFrame⟩ := StackLoopKeep.contract c ram s served used
      pc sp frame uart one two masked stack app inv serve headLimit bodyLimit filled consumed bound
    have capWord := ViewFrame.word capFrame 0 (by decide)
    simp only [BitVec.add_zero] at capWord
    exact ⟨115,d,after,by decide,steps,⟨ready,MainGprBank.preserve bankFrame bank,serveAfter,room rfl,
      capWord.trans capacity,MainRouterTable.preserve routes routeFrame⟩⟩
  | true =>
    obtain ⟨d,after,steps,ready,serveAfter,capFrame,routeFrame,bankFrame⟩ := StackLoopClose.contract c ram s
      pc sp frame uart one two masked stack app inv capacity
    have capWord := ViewFrame.word capFrame 0 (by decide)
    simp only [BitVec.add_zero] at capWord
    exact ⟨118,d,after,by decide,steps,⟨ready,MainGprBank.preserve bankFrame bank,serveAfter,(by change (0 : Nat)<100;decide),
      capWord.trans capacity,MainRouterTable.preserve routes routeFrame⟩⟩
end E5R.Thermostat.StackLoopReady
