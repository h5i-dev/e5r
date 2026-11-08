-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.Errors
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.Errors
theorem forbidden_full_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x8000011c) (h0 : B.inRam (c.get 10) 1 = true)
    (h10 : B.inRam (c.get 10+10#32) 1 = true) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,result ram (c.get 10) .forbidden⟩ ∧
      d.pc = 0x800001ac ∧ d.get 2 = c.get 2 ∧ d.sameCsr c ∧ Upper.Frame c d := by
  let c1 := c.wr 11 2#32 0x8000011e
  let r1 := ramPut ram (c.get 10) (code .forbidden)
  let c2 := c1.goto 0x80000122
  let c3 := c2.goto 0x80000126
  let d := c3.goto 0x800001ac
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp]; decide)
      (by rw [hp]; exact d2147483932) fun o => ?_
    rw [exec_opimm]
    rw [hp]
    rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    have ha : c1.get 10 = c.get 10 := by simp [c1,Core.wr_get_ne]
    have hv : c1.get 11 = 2#32 := by simp [c1,Core.wr_get]
    refine QuietDet.step_of (by change (0x8000011e : Word).getLsbD 0 = false; decide) d2147483934 fun o => ?_
    rw [exec_store,ha,hv]
    rw [BitVec.add_zero]
    rw [interp_store_ram o (by simp only [Width.bytes,Nat.mod_one]) h0]
    rfl
  have s2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,result ram (c.get 10) .forbidden⟩ := by
    have ha : c2.get 10 = c.get 10 := by simp [c2,c1,Core.wr_get_ne]
    have hv : c2.get 11 = 2#32 := by simp [c2,c1,Core.wr_get]
    refine QuietDet.step_of (by change (0x80000122 : Word).getLsbD 0 = false; decide) d2147483938 fun o => ?_
    rw [exec_store,ha,hv]
    skip
    rw [interp_store_ram o (by simp only [Width.bytes,Nat.mod_one]) h10]
    rfl
  have s3 : Quiet.Step B img ⟨c3,result ram (c.get 10) .forbidden⟩ ⟨d,result ram (c.get 10) .forbidden⟩ := by
    refine QuietDet.step_of (by change (0x80000126 : Word).getLsbD 0 = false; decide) d2147483942 fun o => ?_
    rw [exec_jal,Core.set_zero,jump_ok _ _ (by change (0x800001ac : Word).getLsbD 0 = false; decide)]
    rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.single s3))),rfl,?_,?_,?_⟩
  · simp [d,c3,c2,c1,Core.wr_get_ne]
  · exact (Core.sameCsr_goto _ _).trans ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_wr _ _ _ _).trans (Core.sameCsr_refl c))))

  · intro r hr
    have hn0 := Upper.ne_low r hr 0 (by decide)
    have hn1 := Upper.ne_low r hr 1 (by decide)
    have hn2 := Upper.ne_low r hr 2 (by decide)
    have hn3 := Upper.ne_low r hr 3 (by decide)
    have hn4 := Upper.ne_low r hr 4 (by decide)
    have hn5 := Upper.ne_low r hr 5 (by decide)
    have hn6 := Upper.ne_low r hr 6 (by decide)
    have hn7 := Upper.ne_low r hr 7 (by decide)
    have hn8 := Upper.ne_low r hr 8 (by decide)
    have hn9 := Upper.ne_low r hr 9 (by decide)
    have hn10 := Upper.ne_low r hr 10 (by decide)
    have hn11 := Upper.ne_low r hr 11 (by decide)
    have hn12 := Upper.ne_low r hr 12 (by decide)
    have hn13 := Upper.ne_low r hr 13 (by decide)
    have hn14 := Upper.ne_low r hr 14 (by decide)
    have hn15 := Upper.ne_low r hr 15 (by decide)
    have hn16 := Upper.ne_low r hr 16 (by decide)
    have hn17 := Upper.ne_low r hr 17 (by decide)
    have hn18 := Upper.ne_low r hr 18 (by decide)
    have hn19 := Upper.ne_low r hr 19 (by decide)
    have hn20 := Upper.ne_low r hr 20 (by decide)
    have hn21 := Upper.ne_low r hr 21 (by decide)
    simp [d,c3,c2,c1,Core.wr_get_ne,hn0,hn1,hn2,hn3,hn4,hn5,hn6,hn7,hn8,hn9,hn10,hn11,hn12,hn13,hn14,hn15,hn16,hn17,hn18,hn19,hn20,hn21]

end E5R.Thermostat.Errors
namespace E5R.Thermostat.Errors
theorem forbidden_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x8000011c) (h0 : B.inRam (c.get 10) 1 = true)
    (h10 : B.inRam (c.get 10+10#32) 1 = true) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,result ram (c.get 10) .forbidden⟩ ∧
      d.pc = 0x800001ac ∧ d.get 2 = c.get 2 ∧ d.sameCsr c := by
  obtain ⟨d,hr,hpc,hsp,hcsr,_⟩ := E5R.Thermostat.Errors.forbidden_full_quiet B c ram hp h0 h10
  exact ⟨d,hr,hpc,hsp,hcsr⟩

end E5R.Thermostat.Errors
namespace E5R.Thermostat.Errors
theorem setpoint_range_full_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x800000f2) (h0 : B.inRam (c.get 10) 1 = true)
    (h10 : B.inRam (c.get 10+10#32) 1 = true) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,result ram (c.get 10) .setpointOutOfRange⟩ ∧
      d.pc = 0x800001ac ∧ d.get 2 = c.get 2 ∧ d.sameCsr c ∧ Upper.Frame c d := by
  let c1 := c.wr 11 2#32 0x800000f4
  let r1 := ramPut ram (c.get 10) (code .setpointOutOfRange)
  let c2 := c1.goto 0x800000f8
  let c3 := c2.goto 0x800000fc
  let d := c3.goto 0x800001ac
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp]; decide)
      (by rw [hp]; exact d2147483890) fun o => ?_
    rw [exec_opimm]
    rw [hp]
    rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    have ha : c1.get 10 = c.get 10 := by simp [c1,Core.wr_get_ne]
    have hv : c1.get 0 = 0#32 := by simp [c1,Core.wr_get]
    refine QuietDet.step_of (by change (0x800000f4 : Word).getLsbD 0 = false; decide) d2147483892 fun o => ?_
    rw [exec_store,ha,hv]
    rw [BitVec.add_zero]
    rw [interp_store_ram o (by simp only [Width.bytes,Nat.mod_one]) h0]
    rfl
  have s2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,result ram (c.get 10) .setpointOutOfRange⟩ := by
    have ha : c2.get 10 = c.get 10 := by simp [c2,c1,Core.wr_get_ne]
    have hv : c2.get 11 = 2#32 := by simp [c2,c1,Core.wr_get]
    refine QuietDet.step_of (by change (0x800000f8 : Word).getLsbD 0 = false; decide) d2147483896 fun o => ?_
    rw [exec_store,ha,hv]
    skip
    rw [interp_store_ram o (by simp only [Width.bytes,Nat.mod_one]) h10]
    rfl
  have s3 : Quiet.Step B img ⟨c3,result ram (c.get 10) .setpointOutOfRange⟩ ⟨d,result ram (c.get 10) .setpointOutOfRange⟩ := by
    refine QuietDet.step_of (by change (0x800000fc : Word).getLsbD 0 = false; decide) d2147483900 fun o => ?_
    rw [exec_jal,Core.set_zero,jump_ok _ _ (by change (0x800001ac : Word).getLsbD 0 = false; decide)]
    rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.single s3))),rfl,?_,?_,?_⟩
  · simp [d,c3,c2,c1,Core.wr_get_ne]
  · exact (Core.sameCsr_goto _ _).trans ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_wr _ _ _ _).trans (Core.sameCsr_refl c))))

  · intro r hr
    have hn0 := Upper.ne_low r hr 0 (by decide)
    have hn1 := Upper.ne_low r hr 1 (by decide)
    have hn2 := Upper.ne_low r hr 2 (by decide)
    have hn3 := Upper.ne_low r hr 3 (by decide)
    have hn4 := Upper.ne_low r hr 4 (by decide)
    have hn5 := Upper.ne_low r hr 5 (by decide)
    have hn6 := Upper.ne_low r hr 6 (by decide)
    have hn7 := Upper.ne_low r hr 7 (by decide)
    have hn8 := Upper.ne_low r hr 8 (by decide)
    have hn9 := Upper.ne_low r hr 9 (by decide)
    have hn10 := Upper.ne_low r hr 10 (by decide)
    have hn11 := Upper.ne_low r hr 11 (by decide)
    have hn12 := Upper.ne_low r hr 12 (by decide)
    have hn13 := Upper.ne_low r hr 13 (by decide)
    have hn14 := Upper.ne_low r hr 14 (by decide)
    have hn15 := Upper.ne_low r hr 15 (by decide)
    have hn16 := Upper.ne_low r hr 16 (by decide)
    have hn17 := Upper.ne_low r hr 17 (by decide)
    have hn18 := Upper.ne_low r hr 18 (by decide)
    have hn19 := Upper.ne_low r hr 19 (by decide)
    have hn20 := Upper.ne_low r hr 20 (by decide)
    have hn21 := Upper.ne_low r hr 21 (by decide)
    simp [d,c3,c2,c1,Core.wr_get_ne,hn0,hn1,hn2,hn3,hn4,hn5,hn6,hn7,hn8,hn9,hn10,hn11,hn12,hn13,hn14,hn15,hn16,hn17,hn18,hn19,hn20,hn21]

end E5R.Thermostat.Errors
namespace E5R.Thermostat.Errors
theorem relay_range_full_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x8000010e) (h0 : B.inRam (c.get 10) 1 = true)
    (h10 : B.inRam (c.get 10+10#32) 1 = true) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,result ram (c.get 10) .noSuchRelay⟩ ∧
      d.pc = 0x800001ac ∧ d.get 2 = c.get 2 ∧ d.sameCsr c ∧ Upper.Frame c d := by
  let c1 := c.wr 11 1#32 0x80000110
  let c2 := c1.wr 12 2#32 0x80000112
  let r1 := ramPut ram (c.get 10) (code .noSuchRelay)
  let c3 := c2.goto 0x80000116
  let c4 := c3.goto 0x8000011a
  let d := c4.goto 0x800001ac
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp]; decide)
      (by rw [hp]; exact d2147483918) fun o => ?_
    rw [exec_opimm]
    rw [hp]
    rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80000110 : Word).getLsbD 0 = false; decide)
      (by exact d2147483920) fun o => ?_
    rw [exec_opimm]
    skip
    rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,r1⟩ := by
    have ha : c2.get 10 = c.get 10 := by simp [c2,c1,Core.wr_get_ne]
    have hv : c2.get 11 = 1#32 := by simp [c2,c1,Core.wr_get]
    refine QuietDet.step_of (by change (0x80000112 : Word).getLsbD 0 = false; decide) d2147483922 fun o => ?_
    rw [exec_store,ha,hv]
    rw [BitVec.add_zero]
    rw [interp_store_ram o (by simp only [Width.bytes,Nat.mod_one]) h0]
    rfl
  have s3 : Quiet.Step B img ⟨c3,r1⟩ ⟨c4,result ram (c.get 10) .noSuchRelay⟩ := by
    have ha : c3.get 10 = c.get 10 := by simp [c3,c2,c1,Core.wr_get_ne]
    have hv : c3.get 12 = 2#32 := by simp [c3,c2,c1,Core.wr_get]
    refine QuietDet.step_of (by change (0x80000116 : Word).getLsbD 0 = false; decide) d2147483926 fun o => ?_
    rw [exec_store,ha,hv]
    skip
    rw [interp_store_ram o (by simp only [Width.bytes,Nat.mod_one]) h10]
    rfl
  have s4 : Quiet.Step B img ⟨c4,result ram (c.get 10) .noSuchRelay⟩ ⟨d,result ram (c.get 10) .noSuchRelay⟩ := by
    refine QuietDet.step_of (by change (0x8000011a : Word).getLsbD 0 = false; decide) d2147483930 fun o => ?_
    rw [exec_jal,Core.set_zero,jump_ok _ _ (by change (0x800001ac : Word).getLsbD 0 = false; decide)]
    rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.single s4)))),rfl,?_,?_,?_⟩
  · simp [d,c4,c3,c2,c1,Core.wr_get_ne]
  · exact (Core.sameCsr_goto _ _).trans ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans (Core.sameCsr_refl c)))))

  · intro r hr
    have hn0 := Upper.ne_low r hr 0 (by decide)
    have hn1 := Upper.ne_low r hr 1 (by decide)
    have hn2 := Upper.ne_low r hr 2 (by decide)
    have hn3 := Upper.ne_low r hr 3 (by decide)
    have hn4 := Upper.ne_low r hr 4 (by decide)
    have hn5 := Upper.ne_low r hr 5 (by decide)
    have hn6 := Upper.ne_low r hr 6 (by decide)
    have hn7 := Upper.ne_low r hr 7 (by decide)
    have hn8 := Upper.ne_low r hr 8 (by decide)
    have hn9 := Upper.ne_low r hr 9 (by decide)
    have hn10 := Upper.ne_low r hr 10 (by decide)
    have hn11 := Upper.ne_low r hr 11 (by decide)
    have hn12 := Upper.ne_low r hr 12 (by decide)
    have hn13 := Upper.ne_low r hr 13 (by decide)
    have hn14 := Upper.ne_low r hr 14 (by decide)
    have hn15 := Upper.ne_low r hr 15 (by decide)
    have hn16 := Upper.ne_low r hr 16 (by decide)
    have hn17 := Upper.ne_low r hr 17 (by decide)
    have hn18 := Upper.ne_low r hr 18 (by decide)
    have hn19 := Upper.ne_low r hr 19 (by decide)
    have hn20 := Upper.ne_low r hr 20 (by decide)
    have hn21 := Upper.ne_low r hr 21 (by decide)
    simp [d,c4,c3,c2,c1,Core.wr_get_ne,hn0,hn1,hn2,hn3,hn4,hn5,hn6,hn7,hn8,hn9,hn10,hn11,hn12,hn13,hn14,hn15,hn16,hn17,hn18,hn19,hn20,hn21]

end E5R.Thermostat.Errors
