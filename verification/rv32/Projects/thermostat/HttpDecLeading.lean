import Projects.thermostat.HttpDecLeading0
import Projects.thermostat.HttpDecLeading1
namespace E5R.Thermostat.HttpDecLeading
open E5R E5R.Thermostat
abbrev memory := HttpDecLeading0.memory

/-- Actual prologue, initialized decimal scratch and all high-digit skip
    branches, through the hundreds decision, for every main body length. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (n : Nat)
    (hn : n≤832) (hp : c.pc=0x80004180#32) (h2 : c.get 2=sp+16#32)
    (h13 : c.get 13=BitVec.ofNat 32 n) (hm : Memory.Block B sp 16) (ha : sp.toNat%4=0) :
    ∃ d, Quiet.Steps B img 60 ⟨c,ram⟩ ⟨d,memory ram sp⟩ ∧ d.pc=0x800044e0#32 ∧
      d.get 2=sp ∧ d.get 14=BitVec.ofNat 32 (n/100) ∧ d.get 15=0#32 ∧ d.get 16=0#32 ∧ d.get 17=0#32 ∧
      (∀ r : Reg, r≠2 → r≠14 → r≠15 → r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,ta,pa,a2,a14,a15,a16,a17,ar,ac⟩ := HttpDecLeading0.contract B c ram sp n hn h2 h13 hm ha hp
  obtain ⟨d,td,pd,d14,d15,d16,d17,dr,dc⟩ := HttpDecLeading1.contract B a (memory ram sp) sp n hn a2
    ((ar 13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h13) a14 a15 a16 a17 hm ha pa
  refine ⟨d,ta.trans td,pd,(dr 2 (by decide) (by decide) (by decide) (by decide)).trans a2,d14,d15,d16,d17,?_,dc.trans ac⟩
  intro r h2 h14 h15 h16 h17
  exact (dr r h14 h15 h16 h17).trans (ar r h2 h14 h15 h16 h17)
end E5R.Thermostat.HttpDecLeading
