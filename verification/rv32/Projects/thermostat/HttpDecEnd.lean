import Projects.thermostat.HttpDecCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HttpDecEnd
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (k : Nat) (h2 : c.get 2=sp) (h11 : c.get 11=BitVec.ofNat 32 k)
    (hp : c.pc=0x800043fe#32) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=c.get 1 &&& ~~~1 ∧
      d.get 11=BitVec.ofNat 32 (k+1) ∧ d.get 14=1#32 ∧ d.get 10=1#32 ∧ d.get 2=sp+16#32 ∧ (∀ r : Reg, r≠11 → r≠14 → r≠10 → r≠2 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 11 (BitVec.ofNat 32 (k+1)) 0x80004400#32
  let c2 := c1.wr 14 (1#32) 0x80004402#32
  let c3 := c2.goto 0x8000444c#32
  let c4 := c3.wr 10 (1#32) 0x8000444e#32
  let c5 := c4.wr 2 (sp+16#32) 0x80004450#32
  let c6 := c5.goto (c.get 1 &&& ~~~1)
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact de2147501054) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,h11]
    change Observed.interp B img o (.done (c.wr 11 ((BitVec.ofNat 32 k)+1#32) (c.pc+2#32))) ram 0 [] [] = _
    rw [←BitVec.ofNat_add,hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80004400#32).getLsbD 0=false;decide) de2147501056 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80004402#32).getLsbD 0=false;decide) de2147501058 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_jal]
    change Observed.interp B img o (jump c2 (0x80004402#32+74#32)) ram 0 [] [] = _
    rw [show 0x80004402#32+74#32=0x8000444c#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x8000444c#32).getLsbD 0=false;decide) de2147501132 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v14 : c3.get 14=1#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11]
    rw [exec_op,Core.get_zero,v14];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x8000444e#32).getLsbD 0=false;decide) de2147501134 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v2 : c4.get 2=sp := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11]
    rw [exec_opimm,v2];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80004450#32).getLsbD 0=false;decide) de2147501136 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v1 : c5.get 1=c.get 1 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11]
    rw [exec_jalr,v1,BitVec.add_zero]
    change Observed.interp B img o (jump c5 (c.get 1 &&& ~~~1)) ram 0 [] [] = _
    rw [jump_ok _ _ (clear_bit0 _)];first | rfl | (rw [hp];rfl)
  refine ⟨c6,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.single t5))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11]
  · intro reg h11 h14 h10 h2;simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h11,h11,h14,h10,h2]
end E5R.Thermostat.HttpDecEnd
