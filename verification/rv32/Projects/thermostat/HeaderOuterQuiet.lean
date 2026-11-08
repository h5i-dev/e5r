-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.HeaderOuter
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.HeaderOuter
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (n : Nat)
    (hn : 0 < n) (hb : n ≤ 16) (hp : c.pc = 0x800026e2#32)
    (h16 : c.get 16 = p) (h17 : c.get 17 = p+BitVec.ofNat 32 (16*n)) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if n = 1 then 0x8000274e#32 else 0x800026e8#32) ∧ d.get 16 = p+16#32 ∧
      (∀ r : Reg, r ≠ 16 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 16 (p+16#32) 0x800026e4#32
  let d := c1.goto (if n = 1 then 0x8000274e#32 else 0x800026e8#32)
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact hd2147493602) fun o => ?_
    rw [exec_opimm,h16,hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x800026e4#32).getLsbD 0 = false;decide) hd2147493604 fun o => ?_
    have v16 : c1.get 16 = p+16#32 := by simp [c1,Core.wr_get]
    have v17 : c1.get 17 = p+BitVec.ofNat 32 (16*n) := by simp [c1,Core.wr_get_ne,h17]
    rw [exec_branch,v16,v17,end_test p n hn hb]
    by_cases he : n = 1
    · rw [decide_eq_true he];simp only [ite_true,d,ite_eq_left he]
      change interp B img o (jump c1 (0x800026e4#32+0x6a#32)) ram 0 [] = _
      rw [show 0x800026e4#32+0x6a#32 = 0x8000274e#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
    · rw [decide_eq_false he];simp only [Bool.false_eq_true,ite_false,d,ite_eq_right he];rfl
  refine ⟨d,.step s0 (.single s1),rfl,?_,?_,by rfl⟩
  · simp [d,c1,Core.wr_get]
  · intro r hr;simp [d,c1,Core.wr_get_ne,hr]

end E5R.Thermostat.HeaderOuter
