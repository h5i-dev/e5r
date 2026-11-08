import Projects.thermostat.WireCallerPrefix
import Projects.thermostat.WireCallerStore
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.WireCaller
open E5R E5R.Thermostat

theorem ok (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (cmd : Spec.Command)
    (hp : c.pc = 0x800005f4#32) (hsp : c.get 2 = p) (h : WireSpec.CommandWord (c.get 10) cmd)
    (hm : Memory.Block B p 16) (ha : p.toNat%2 = 0) :
    ∃ d, DetSteps B img 8 ⟨c,ram⟩ ⟨d,WireCallerBytes.memory ram p (c.get 10)⟩ ∧ d.pc = 0x80000614#32 ∧
      Encoding.CommandAt (WireCallerBytes.memory ram p (c.get 10)) (p+10#32) cmd ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 20 → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,ta,pca,a20,a10,ra,ca⟩ := WireCallerPrefix.contract B c ram (c.get 10) hp rfl
  have apc : a.pc = 0x80000604#32 := by simpa only [ite_eq_right (WireCallerPrefix.ok_tag _ cmd h)] using pca
  obtain ⟨d,td,pcd,rd,cd⟩ := WireCallerStore.contract B a ram p (c.get 10) apc
    ((ra 2 (by decide) (by decide) (by decide)).trans hsp) a10 a20 hm ha
  refine ⟨d,ta.trans td,pcd,WireCallerBytes.command ram p (c.get 10) cmd h,?_,cd.trans ca⟩
  intro r h1 h2 h3;exact (rd r h1).trans (ra r h1 h2 h3)

theorem error (B : Board) (c : Core) (ram : Word → BitVec 8) (status : Nat)
    (hp : c.pc = 0x800005f4#32) (h : WireSpec.ResultWord (c.get 10) (.error status)) :
    ∃ d, DetSteps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x800005a2#32 ∧
      (d.get 20).toNat = status ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 20 → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨d,td,pcd,v20,v10,rd,cd⟩ := WireCallerPrefix.contract B c ram (c.get 10) hp rfl
  exact ⟨d,td,by simpa only [ite_eq_left h.1] using pcd,by rw [v20];exact h.2,rd,cd⟩
end E5R.Thermostat.WireCaller
