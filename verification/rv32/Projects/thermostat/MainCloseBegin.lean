import Projects.thermostat.MainCloseCode
import Projects.thermostat.QuietBranch
import Projects.thermostat.MainMethodLengthMath
set_option autoImplicit false
namespace E5R.Thermostat.MainCloseBegin
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (minor : Nat) (bound : minor≤1)
    (hp : c.pc=0x80001246#32) (h9 : c.get 9=BitVec.ofNat 32 minor) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=(if minor=0 then 0x80001278#32 else 0x8000124a#32) ∧
      d.get 10=1#32 ∧ (∀ r : Reg, r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 10 1#32 0x80001248#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147488326) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok a ram [],[]⟩
    rw [exec_opimm,Core.get_zero,hp];rfl
  have a9 : a.get 9=BitVec.ofNat 32 minor := by simp [a,Core.wr_get_ne,h9]
  obtain ⟨d,t1,pd,dr,dc⟩ := QuietBranch.contract B img a ram 0x80001248#32 2#32 0x30#32 .eq 9 0 (decide (minor=0)) rfl (by decide) (by decide) re2147488328
    (by rw [a9,Core.get_zero];exact MainMethodLengthMath.eqTest minor 0 (by omega) (by decide))
  refine ⟨d,(Quiet.Steps.single t0).trans t1,?_,(dr 10).trans (by simp [a,Core.wr_get]),?_,dc⟩
  · simpa only [decide_eq_true_eq,show 0x80001248#32+0x30#32=0x80001278#32 by decide +kernel,show 0x80001248#32+2#32=0x8000124a#32 by decide +kernel] using pd
  · intro r neq;exact (dr r).trans (by simp [a,Core.wr_get_ne,neq])
end E5R.Thermostat.MainCloseBegin
