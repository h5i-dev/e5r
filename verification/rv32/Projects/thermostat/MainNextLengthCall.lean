import Projects.thermostat.MainNextCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainNextLengthCall
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (h2 : c.get 2=sp)
    (hp : c.pc=0x80000cda#32) :
    ∃ d, Quiet.Steps B img 8 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80005182#32 ∧
      d.get 10=sp+4904#32 ∧ d.get 12=264#32 ∧ d.get 11=sp+3352#32 ∧ d.get 1=0x80000cf6#32 ∧ (∀ r : Reg, r≠10 → r≠12 → r≠11 → r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (4096#32) 0x80000cdc#32
  let c2 := c1.wr 10 (4904#32) 0x80000ce0#32
  let c3 := c2.wr 10 (sp+4904#32) 0x80000ce2#32
  let c4 := c3.wr 12 (264#32) 0x80000ce6#32
  let c5 := c4.wr 11 (sp+2047#32) 0x80000cea#32
  let c6 := c5.wr 11 (sp+3352#32) 0x80000cee#32
  let c7 := c6.wr 1 (0x80004cee#32) 0x80000cf2#32
  let c8 := c7.wr 1 (0x80000cf6#32) 0x80005182#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact nx2147486938) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000cdc#32).getLsbD 0=false;decide) nx2147486940 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v10 : c1.get 10=4096#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_opimm,v10];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80000ce0#32).getLsbD 0=false;decide) nx2147486944 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v2 : c2.get 2=sp := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have v10 : c2.get 10=4904#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_op,v10,v2]
    change Observed.interp B img o (Eff.done (c2.wr 10 (4904#32+sp) 0x80000ce2#32)) ram 0 [] []=⟨.ok c3 ram [],[]⟩
    rw [BitVec.add_comm 4904#32 sp]
    rfl
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80000ce2#32).getLsbD 0=false;decide) nx2147486946 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80000ce6#32).getLsbD 0=false;decide) nx2147486950 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v2 : c4.get 2=sp := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_opimm,v2];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80000cea#32).getLsbD 0=false;decide) nx2147486954 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v11 : c5.get 11=sp+2047#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_opimm,v11]
    change Observed.interp B img o (Eff.done (c5.wr 11 ((sp+2047#32)+1305#32) 0x80000cee#32)) ram 0 [] []=_
    rw [BitVec.add_assoc,show 2047#32+1305#32=3352#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80000cee#32).getLsbD 0=false;decide) nx2147486958 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    rw [exec_auipc];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x80000cf2#32).getLsbD 0=false;decide) nx2147486962 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v1 : c7.get 1=0x80004cee#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_jalr,v1]
    change Observed.interp B img o (jump (c7.set 1 0x80000cf6#32) ((0x80004cee#32+1172#32) &&& ~~~1)) ram 0 [] []=_
    rw [show (0x80004cee#32+1172#32) &&& ~~~1=0x80005182#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c8,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.single t7))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · intro reg h10 h12 h11 h1;simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h12,h11,h1]
end E5R.Thermostat.MainNextLengthCall
