-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.WriteSuccessReturn
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.WriteSuccessReturn
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (len : Word) (h10 : c.get 10 = 1#32) (h11 : c.get 11 = len)
    (hp : c.pc = 0x80000744#32) :
    ∃ d, Quiet.Steps B img 8 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x800005ac#32 ∧
      d.get 12 = 0x800056a8#32 ∧ d.get 18 = len ∧ d.get 10 = 16#32 ∧ d.get 20 = 200#32 ∧ (∀ r : Reg, r ≠ 12 → r ≠ 18 → r ≠ 10 → r ≠ 20 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 (1#32) 0x80000746#32
  let c2 := c1.goto 0x8000074a#32
  let c3 := c2.wr 18 (len) 0x8000074c#32
  let c4 := c3.wr 10 (16#32) 0x8000074e#32
  let c5 := c4.wr 12 (0x80005000#32) 0x80000752#32
  let c6 := c5.wr 12 (0x800056a8#32) 0x80000756#32
  let c7 := c6.wr 20 (200#32) 0x8000075a#32
  let c8 := c7.goto 0x800005ac#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact ws2147485508) fun o => ?_
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp]; rfl)
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80000746#32).getLsbD 0 = false;decide) ws2147485510 fun o => ?_
    have hv : c1.get 12 = 1#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    have hret : c1.get 10 = 1#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_branch,hret,hv,show E5R.taken .ne 1#32 1#32 = false by decide]
    simp only [ite_false];first | rfl | (rw [hp]; rfl)
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000074a#32).getLsbD 0 = false;decide) ws2147485514 fun o => ?_
    have hv : c2.get 11 = len := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000074c#32).getLsbD 0 = false;decide) ws2147485516 fun o => ?_
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp]; rfl)
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000074e#32).getLsbD 0 = false;decide) ws2147485518 fun o => ?_
    rw [exec_lui];first | rfl | (rw [hp]; rfl)
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (0x80000752#32).getLsbD 0 = false;decide) ws2147485522 fun o => ?_
    have hv : c5.get 12 = 0x80005000#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine QuietDet.step_of (by change (0x80000756#32).getLsbD 0 = false;decide) ws2147485526 fun o => ?_
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp]; rfl)
  have s7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000075a#32).getLsbD 0 = false;decide) ws2147485530 fun o => ?_
    rw [exec_jal]
    change interp B img o (jump c7 (0x8000075a#32+0xfffffe52#32)) ram 0 [] = _
    rw [show (0x8000075a#32+0xfffffe52#32)=0x800005ac#32 by decide +kernel]
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp]; rfl)
  refine ⟨c8,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.single s7))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
  · intro r h12 h18 h10 h20
    simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11,h12,h18,h10,h20]

end E5R.Thermostat.WriteSuccessReturn
