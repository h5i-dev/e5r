import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadClMulRaw
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (low ten : Word) (h14 : c.get 14=low) (h16 : c.get 16=ten)
    (hp : c.pc=0x8000321e#32) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000322a#32 ∧
      d.get 12=muldiv .mulhu low ten ∧ d.get 29=alu .add (alu .sll low 1#32) (alu .sll low 3#32) ∧ d.get 14=alu .sll low 3#32 ∧ (∀ r : Reg, r≠12 → r≠29 → r≠14 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 (muldiv .mulhu low ten) 0x80003222#32
  let c2 := c1.wr 29 (alu .sll low 1#32) 0x80003226#32
  let c3 := c2.wr 14 (alu .sll low 3#32) 0x80003228#32
  let c4 := c3.wr 29 (alu .add (alu .sll low 1#32) (alu .sll low 3#32)) 0x8000322a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496478) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    change Observed.interp B img o (.done (c.wr 12 (muldiv .mulhu (c.get 14) (c.get 16)) (c.pc+4#32))) ram 0 [] [] = _
    rw [h14,h16];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80003222#32).getLsbD 0=false;decide) hh2147496482 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v14 : c1.get 14=low := by simp [c1,Core.wr_get_ne,Core.wr_get,h14,h16]
    rw [exec_opimm,v14];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80003226#32).getLsbD 0=false;decide) hh2147496486 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v14 : c2.get 14=low := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h14,h16]
    rw [exec_opimm,v14];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80003228#32).getLsbD 0=false;decide) hh2147496488 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v29 : c3.get 29=alu .sll low 1#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14,h16]
    have v14 : c3.get 14=alu .sll low 3#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14,h16]
    rw [exec_op,v29,v14];first | rfl | (rw [hp];rfl)
  refine ⟨c4,.step t0 (.step t1 (.step t2 (.single t3))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14,h16]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14,h16]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14,h16]
  · intro reg h12 h29 h14;simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h14,h16,h12,h29,h14]
end E5R.Thermostat.HeadClMulRaw
