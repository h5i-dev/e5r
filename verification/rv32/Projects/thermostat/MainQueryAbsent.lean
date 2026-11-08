import Projects.thermostat.MainQueryCode
import Projects.thermostat.QuietRam
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainQueryAbsent
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word)
    (h10 : c.get 10=base) (hp : c.pc=0x80000bf0#32) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80000d50#32 ∧
      d.get 13=0#32 ∧ d.get 12=base ∧
      (∀ r : Reg, r≠13 → r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 13 0#32 0x80000bf2#32
  let b := a.wr 12 base 0x80000bf4#32
  let d := b.goto 0x80000d50#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147486704) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok a ram [],[]⟩
    rw [exec_opimm,Core.get_zero,hp];rfl
  have t1 : Quiet.Step B img ⟨a,ram⟩ ⟨b,ram⟩ := by
    refine Quiet.step_of (by change (0x80000bf2#32).getLsbD 0=false;decide) re2147486706 fun o => ?_
    change Observed.interp B img o (exec a _ _) ram 0 [] [] = ⟨.ok b ram [],[]⟩
    have h : a.get 10=base := by simpa [a,Core.wr_get_ne] using h10
    rw [exec_op,Core.get_zero,h]
    change Observed.interp B img o (Eff.done (a.wr 12 (0#32+base) _)) ram 0 [] [] = _
    rw [BitVec.zero_add];rfl
  have t2 : Quiet.Step B img ⟨b,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of (by change (0x80000bf4#32).getLsbD 0=false;decide) re2147486708 fun o => ?_
    change Observed.interp B img o (exec b _ _) ram 0 [] [] = ⟨.ok d ram [],[]⟩
    rw [exec_jal]
    change Observed.interp B img o (jump (b.wr 0 (b.pc+2#32) (b.pc+2#32)) 0x80000d50#32) ram 0 [] [] = _
    rw [jump_ok _ _ (by decide)]
    rfl
  refine ⟨d,.step t0 (.step t1 (.single t2)),rfl,?_,?_,?_,by rfl⟩
  · simp [d,b,a,Core.wr_get_ne,Core.wr_get]
  · simp [d,b,a,Core.wr_get_ne,Core.wr_get]
  · intro r h13 h12;simp [d,b,a,Core.wr_get_ne,Core.wr_get,h13,h12]
end E5R.Thermostat.MainQueryAbsent
