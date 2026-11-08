import Projects.thermostat.MainHeaderCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainHeaderResultLoad
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (fp tag : Word) (h8 : c.get 8=fp) (h1316 : ramRead ram (fp+1316#32) .w=tag) (h1320 : ramRead ram (fp+1320#32) .w=0#32)
(object : Memory.Block B fp 1324) (aligned : fp.toNat%4=0)
    (hp : c.pc=0x80000a26#32) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80000a38#32 ∧
      d.get 10=tag ∧ d.get 11=alu .and 1#32 (alu .sltu tag 3#32) ∧ d.get 12=alu .sltu tag 3#32 ∧ (∀ r : Reg, r≠10 → r≠11 → r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (tag) 0x80000a2a#32
  let c2 := c1.wr 11 (0#32) 0x80000a2e#32
  let c3 := c2.wr 11 (1#32) 0x80000a32#32
  let c4 := c3.wr 12 (alu .sltu tag 3#32) 0x80000a36#32
  let c5 := c4.wr 11 (alu .and 1#32 (alu .sltu tag 3#32)) 0x80000a38#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact mh2147486246) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_load,h8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 329 aligned) (Memory.block_access object (off := 1316) (by decide) (by decide)),h1316];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000a2a#32).getLsbD 0=false;decide) mh2147486250 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v8 : c1.get 8=fp := by simp [c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 330 aligned) (Memory.block_access object (off := 1320) (by decide) (by decide)),h1320];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80000a2e#32).getLsbD 0=false;decide) mh2147486254 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v11 : c2.get 11=0#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_opimm,v11];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80000a32#32).getLsbD 0=false;decide) mh2147486258 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v10 : c3.get 10=tag := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_opimm,v10];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80000a36#32).getLsbD 0=false;decide) mh2147486262 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v11 : c4.get 11=1#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    have v12 : c4.get 12=alu .sltu tag 3#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_op,v11,v12];first | rfl | (rw [hp];rfl)
  refine ⟨c5,.step t0 (.step t1 (.step t2 (.step t3 (.single t4)))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · intro reg h10 h11 h12;simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h12]
end E5R.Thermostat.MainHeaderResultLoad
