import Projects.thermostat.RejectResponseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.RejectResponseComplete
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)  (frame : c.get 8=0x80fff814#32) (minus1 : c.get 21=0xffffffff#32) (minus2 : c.get 24=0xfffffffe#32) (tag : ramRead ram (0x80fff814#32+1316#32) .w=0xffffffff#32) (object : Memory.Block B 0x80fff814#32 1320)
    (hp : c.pc=0x80001c0a#32) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80000978#32 ∧
      d.get 10=0xffffffff#32 ∧ d.get 20=4#32 ∧ (∀ r : Reg, r≠10 → r≠20 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (0xffffffff#32) 0x80001c0e#32
  let c2 := c1.wr 20 (4#32) 0x80001c10#32
  let c3 := c2.goto 0x80001c14#32
  let c4 := c3.goto 0x80000964#32
  let c5 := c4.wr 10 (0xffffffff#32) 0x80000968#32
  let c6 := c5.goto 0x80000978#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact RejectResponseCode.rr2147490826) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v8 : c.get 8=0x80fff814#32 := by simp [Core.wr_get_ne,Core.wr_get,frame,minus1,minus2]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 329 (by decide))
      (Memory.block_access object (off := 1316) (by decide) (by decide)),tag];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80001c0e#32).getLsbD 0=false;decide) RejectResponseCode.rr2147490830 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80001c10#32).getLsbD 0=false;decide) RejectResponseCode.rr2147490832 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v10 : c2.get 10=0xffffffff#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,frame,minus1,minus2]
    have v24 : c2.get 24=0xfffffffe#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,frame,minus1,minus2]
    rw [exec_branch,v10,v24,show taken .eq 0xffffffff#32 0xfffffffe#32=false by decide +kernel]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80001c14#32).getLsbD 0=false;decide) RejectResponseCode.rr2147490836 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    rw [exec_jal,Core.set_zero,show c3.pc=0x80001c14#32 from rfl]
    rw [show 0x80001c14#32+0xffffed50#32=0x80000964#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80000964#32).getLsbD 0=false;decide) RejectResponseCode.rr2147486052 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v8 : c4.get 8=0x80fff814#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,frame,minus1,minus2]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 329 (by decide))
      (Memory.block_access object (off := 1316) (by decide) (by decide)),tag];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80000968#32).getLsbD 0=false;decide) RejectResponseCode.rr2147486056 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v10 : c5.get 10=0xffffffff#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,frame,minus1,minus2]
    have v21 : c5.get 21=0xffffffff#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,frame,minus1,minus2]
    rw [exec_branch,v10,v21,show taken .eq 0xffffffff#32 0xffffffff#32=true by decide +kernel]
    simp only [ite_true]
    rw [show c5.pc=0x80000968#32 from rfl,show 0x80000968#32+16#32=0x80000978#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c6,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.single t5))))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,frame,minus1,minus2]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,frame,minus1,minus2]
  · intro reg h10 h20;simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,frame,minus1,minus2,h10,h20]
end E5R.Thermostat.RejectResponseComplete
