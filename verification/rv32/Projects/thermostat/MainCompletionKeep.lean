import Projects.thermostat.MainCompletionCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainCompletionKeep
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (fp : Word) (h8 : c.get 8=fp) (h24 : c.get 24=0xfffffffe#32) (hm : Memory.Block B fp 1324) (ha : fp.toNat%4=0) (htag : ramRead ram (fp+1316#32) .w=0xffffffff#32) (hclose : ramRead ram (fp+1320#32) .w=0#32)
    (hp : c.pc=0x80001784#32) :
    ∃ d, Quiet.Steps B img 8 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800017be#32 ∧
      d.get 10=0#32 ∧ d.get 21=0xffffffff#32 ∧ (∀ r : Reg, r≠10 → r≠21 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (0xffffffff#32) 0x80001788#32
  let c2 := c1.goto 0x800017aa#32
  let c3 := c2.wr 10 (0xffffffff#32) 0x800017ae#32
  let c4 := c3.wr 21 (0xffffffff#32) 0x800017b0#32
  let c5 := c4.goto 0x800017b4#32
  let c6 := c5.wr 10 (0#32) 0x800017b8#32
  let c7 := c6.wr 10 (0#32) 0x800017ba#32
  let c8 := c7.goto 0x800017be#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact mcp2147489668) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v8 : c.get 8=fp := by simp [Core.wr_get_ne,Core.wr_get,h8,h24]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 329 ha) (Memory.block_access hm (off := 1316) (by decide) (by decide)),htag];first | rfl | (rw [hp]; rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80001788#32).getLsbD 0=false;decide) mcp2147489672 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v10 : c1.get 10=0xffffffff#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h24]
    have v24 : c1.get 24=0xfffffffe#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h24]
    rw [exec_branch,v10,v24,show taken .ne 0xffffffff#32 0xfffffffe#32=true by decide]
    simp only [ite_true]
    rw [show c1.pc=0x80001788#32 by rfl,show 0x80001788#32+34#32=0x800017aa#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800017aa#32).getLsbD 0=false;decide) mcp2147489706 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v8 : c2.get 8=fp := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h24]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 329 ha) (Memory.block_access hm (off := 1316) (by decide) (by decide)),htag];first | rfl | (rw [hp]; rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x800017ae#32).getLsbD 0=false;decide) mcp2147489710 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x800017b0#32).getLsbD 0=false;decide) mcp2147489712 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v10 : c4.get 10=0xffffffff#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h24]
    have v21 : c4.get 21=0xffffffff#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h24]
    rw [exec_branch,v10,v21,show taken .ne 0xffffffff#32 0xffffffff#32=false by decide];simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x800017b4#32).getLsbD 0=false;decide) mcp2147489716 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v8 : c5.get 8=fp := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h24]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 330 ha) (Memory.block_access hm (off := 1320) (by decide) (by decide)),hclose];first | rfl | (rw [hp]; rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x800017b8#32).getLsbD 0=false;decide) mcp2147489720 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v10 : c6.get 10=0#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h24]
    rw [exec_opimm,v10];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x800017ba#32).getLsbD 0=false;decide) mcp2147489722 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v10 : c7.get 10=0#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h24]
    rw [exec_branch,v10,Core.get_zero,show taken .ne 0#32 (0 : Word)=false by decide]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  refine ⟨c8,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.single t7))))))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h24]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h24]
  · intro reg h10 h21;simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h24,h10,h21]
end E5R.Thermostat.MainCompletionKeep
