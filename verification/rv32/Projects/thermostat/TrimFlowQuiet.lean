-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.TrimFlow
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.TrimFlow
theorem leftSetup_contract_quiet (B : Board) (c : Core) (p l : Word) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80001f80#32) (h11 : c.get 11 = p) (h12 : c.get 12 = l) :
    Quiet.Steps B img 6 ⟨c,ram⟩ ⟨leftSetup c p l,ram⟩ := by
  let c1 := c.wr 13 (p+l) 0x80001f84#32
  let c2 := c1.wr 15 (0x800000#32) 0x80001f88#32
  let c3 := c2.wr 14 (23#32) 0x80001f8a#32
  let c4 := c3.wr 15 (0x80001b#32) 0x80001f8c#32
  let c5 := c4.wr 8 (p) 0x80001f8e#32
  let c6 := c5.wr 9 (l) 0x80001f90#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact tr2147491712) fun o => ?_
    have hv0 : c.get 11 = p := by simp [Core.wr_get_ne,Core.wr_get,h11,h12]
    have hv1 : c.get 12 = l := by simp [Core.wr_get_ne,Core.wr_get,h11,h12]
    rw [exec_op,hv0,hv1,hp]
    rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001f84#32).getLsbD 0 = false;decide) tr2147491716 fun o => ?_
    rw [exec_lui]
    rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001f88#32).getLsbD 0 = false;decide) tr2147491720 fun o => ?_
    rw [exec_opimm,Core.get_zero]
    rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001f8a#32).getLsbD 0 = false;decide) tr2147491722 fun o => ?_
    have hv0 : c3.get 15 = 0x800000#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12]
    rw [exec_opimm,hv0]
    rfl
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001f8c#32).getLsbD 0 = false;decide) tr2147491724 fun o => ?_
    have hv1 : c4.get 11 = p := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12]
    rw [exec_op,Core.get_zero,hv1]
    simp only [alu]
    rw [show (0 : Word) = 0#32 from rfl,BitVec.zero_add];rfl
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001f8e#32).getLsbD 0 = false;decide) tr2147491726 fun o => ?_
    have hv1 : c5.get 12 = l := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12]
    rw [exec_op,Core.get_zero,hv1]
    simp only [alu]
    rw [show (0 : Word) = 0#32 from rfl,BitVec.zero_add];rfl
  exact .step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.single s5)))))

end E5R.Thermostat.TrimFlow
namespace E5R.Thermostat.TrimFlow
theorem rightSetup_contract_quiet (B : Board) (c : Core) (p l : Word) (ram : Word → BitVec 8)
    (hp : c.pc = 0x8000210e#32) (h11 : c.get 11 = p) (h12 : c.get 12 = l) :
    Quiet.Steps B img 5 ⟨c,ram⟩ ⟨rightSetup c p l,ram⟩ := by
  let c1 := c.wr 11 (p+l) 0x80002110#32
  let c2 := c1.wr 13 (0x800000#32) 0x80002114#32
  let c3 := c2.wr 11 ((p+l)+0xffffffff#32) 0x80002116#32
  let c4 := c3.wr 12 (23#32) 0x80002118#32
  let c5 := c4.wr 13 (0x80001b#32) 0x8000211a#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact tr2147492110) fun o => ?_
    have hv0 : c.get 11 = p := by simp [Core.wr_get_ne,Core.wr_get,h11,h12]
    have hv1 : c.get 12 = l := by simp [Core.wr_get_ne,Core.wr_get,h11,h12]
    rw [exec_op,hv0,hv1,hp]
    rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002110#32).getLsbD 0 = false;decide) tr2147492112 fun o => ?_
    rw [exec_lui]
    rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002114#32).getLsbD 0 = false;decide) tr2147492116 fun o => ?_
    have hv0 : c2.get 11 = p+l := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12]
    rw [exec_opimm,hv0]
    rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002116#32).getLsbD 0 = false;decide) tr2147492118 fun o => ?_
    rw [exec_opimm,Core.get_zero]
    rfl
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002118#32).getLsbD 0 = false;decide) tr2147492120 fun o => ?_
    have hv0 : c4.get 13 = 0x800000#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12]
    rw [exec_opimm,hv0]
    rfl
  exact .step s0 (.step s1 (.step s2 (.step s3 (.single s4))))

end E5R.Thermostat.TrimFlow
namespace E5R.Thermostat.TrimFlow
theorem empty_contract_quiet (B : Board) (c : Core) (p : Word) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80001fb0#32) (h11 : c.get 11 = p) :
    Quiet.Steps B img 2 ⟨c,ram⟩ ⟨empty c p,ram⟩ := by
  let c1 := c.wr 9 (0#32) 0x80001fb2#32
  let c2 := c1.wr 8 (p) 0x80001fb4#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact tr2147491760) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp]
    rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001fb2#32).getLsbD 0 = false;decide) tr2147491762 fun o => ?_
    have hv1 : c1.get 11 = p := by simp [c1,Core.wr_get_ne,Core.wr_get,h11]
    rw [exec_op,Core.get_zero,hv1]
    simp only [alu]
    rw [show (0 : Word) = 0#32 from rfl,BitVec.zero_add];rfl
  exact .step s0 (.single s1)

end E5R.Thermostat.TrimFlow
namespace E5R.Thermostat.TrimFlow
theorem leftEmpty_contract_quiet (B : Board) (c : Core) (p : Word) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80001fac#32) (h13 : c.get 13 = p) :
    Quiet.Steps B img 2 ⟨c,ram⟩ ⟨leftEmpty c p,ram⟩ := by
  let c1 := c.wr 8 (p) 0x80001fae#32
  let c2 := c1.goto 0x80001fb4#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact tr2147491756) fun o => ?_
    have hv1 : c.get 13 = p := by simp [Core.wr_get_ne,Core.wr_get,h13]
    rw [exec_op,Core.get_zero,hv1,hp]
    simp only [alu]
    rw [show (0 : Word) = 0#32 from rfl,BitVec.zero_add];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001fae#32).getLsbD 0 = false;decide) tr2147491758 fun o => ?_
    rw [exec_jal]
    have hp1 : c1.pc = 0x80001fae#32 := rfl
    rw [hp1]
    rw [show 0x80001fae#32+0x6#32 = 0x80001fb4#32 by decide +kernel,jump_ok _ _ (by decide)]
    rfl
  exact .step s0 (.single s1)

end E5R.Thermostat.TrimFlow
namespace E5R.Thermostat.TrimFlow
theorem rightEmpty_contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80002134#32) :
    Quiet.Steps B img 1 ⟨c,ram⟩ ⟨rightEmpty c,ram⟩ := by
  let c1 := c.goto 0x80001fb4#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact tr2147492148) fun o => ?_
    rw [exec_jal,hp]
    rw [show 0x80002134#32+0xfffffe80#32 = 0x80001fb4#32 by decide +kernel,jump_ok _ _ (by decide)]
    rfl
  exact .single s0

end E5R.Thermostat.TrimFlow
namespace E5R.Thermostat.TrimFlow
theorem entry_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (z : Word)
    (hp : c.pc = 0x80001f7e#32) (hz : c.get 12 = z) :
    Quiet.Step B img ⟨c,ram⟩ ⟨c.goto (if z = 0#32 then 0x80001fb0#32 else 0x80001f80#32),ram⟩ := by
  refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact tr2147491710) fun o => ?_
  rw [exec_branch,hz,Core.get_zero]
  have ht : taken .eq z (0 : Word) = decide (z = 0#32) := by rfl
  rw [ht]
  by_cases he : z = 0#32
  · simp only [ite_eq_left he,decide_eq_true he,ite_true]
    rw [hp,show 0x80001f7e#32+50#32 = 0x80001fb0#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  · simp only [ite_eq_right he,decide_eq_false he,Bool.false_eq_true,ite_false]
    rw [hp];rfl

end E5R.Thermostat.TrimFlow
