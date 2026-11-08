import Projects.thermostat.HeadDoneTeBranch
import Projects.thermostat.HeadDoneClTag
import Projects.thermostat.HeadDoneTeTag
import Projects.thermostat.HeadDoneMath
namespace E5R.Thermostat.HeadDoneTag
open E5R E5R.Thermostat

def tag (te hasCl : Bool) : Word := if te then 2#32 else if hasCl then 1#32 else 0#32

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (te hasCl : Bool)
    (hp : c.pc=0x80003470#32) (h2 : c.get 2=sp)
    (h10 : c.get 10=alu .and (if te then 1#32 else 0#32) 1#32)
    (h325 : ram (sp+325#32)=HeadFieldsView.flag hasCl) (stack : Memory.Block B sp 327) :
    ∃ n d, 2≤n ∧ n≤4 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80003486#32 ∧ d.get 20=tag te hasCl ∧
      (∀ r : Reg, r≠10 → r≠20 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,ta,apc,ar,ac⟩ := HeadDoneTeBranch.contract B c ram _ 0#32 te hp h10 (Core.get_zero _) (HeadDoneMath.te te)
  cases transfer : te with
  | true =>
    have pc : a.pc=0x80003484#32 := by simpa only [transfer,ite_true] using apc
    obtain ⟨d,td,dpc,d20,dr,dc⟩ := HeadDoneTeTag.contract B a ram pc
    refine ⟨2,d,by decide,by decide,ta.trans td,dpc,?_,?_,dc.trans ac⟩
    · simpa only [tag,transfer,ite_true] using d20
    · intro r h10 h20;exact (dr r h20).trans (ar r)
  | false =>
    have pc : a.pc=0x80003472#32 := by simpa only [transfer,Bool.false_eq_true,ite_false] using apc
    have input : ramRead ram (sp+325#32) .b=BitVec.ofNat 32 (HeadFieldsView.flag hasCl).toNat := by change BitVec.ofNat 32 (ram (sp+325#32)).toNat=_;rw [h325]
    obtain ⟨d,td,dpc,_,d20,dr,dc⟩ := HeadDoneClTag.contract B a ram sp _ ((ar 2).trans h2) input stack pc
    refine ⟨4,d,by decide,by decide,ta.trans td,dpc,?_,?_,dc.trans ac⟩
    · simpa only [tag,transfer,Bool.false_eq_true,ite_false,HeadDoneMath.cl] using d20
    · intro r h10 h20;exact (dr r h10 h20).trans (ar r)
end E5R.Thermostat.HeadDoneTag
