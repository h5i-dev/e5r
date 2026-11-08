import Projects.thermostat.HttpPutCode
import Projects.thermostat.HttpPutMath
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HttpPutSetup
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src cap : Word) (pos n : Nat) (hc : pos+n≤cap.toNat) (hn : 0<n)
    (h12 : c.get 12=BitVec.ofNat 32 pos) (h13 : c.get 13=src)
    (h14 : c.get 14=BitVec.ofNat 32 n) (h15 : c.get 15=cap-BitVec.ofNat 32 pos)
    (hp : c.pc=0x8000413a#32) :
    ∃ d, Quiet.Steps B img 7 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000414e#32 ∧
      d.get 16=src+BitVec.ofNat 32 n ∧ d.get 15=BitVec.ofNat 32 pos ∧ (∀ r : Reg, r≠16 → r≠15 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x8000413c#32
  let c2 := c1.wr 16 (BitVec.ofNat 32 n+0xffffffff#32) 0x80004140#32
  let c3 := c2.goto 0x80004144#32
  let c4 := c3.wr 15 (BitVec.ofNat 32 n+0xffffffff#32) 0x80004146#32
  let c5 := c4.wr 15 ((BitVec.ofNat 32 n+0xffffffff#32)+src) 0x80004148#32
  let c6 := c5.wr 16 (src+BitVec.ofNat 32 n) 0x8000414c#32
  let c7 := c6.wr 15 (BitVec.ofNat 32 pos) 0x8000414e#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hp2147500346) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_branch,h14,Core.get_zero,HttpPutMath.zero_guard n hn (by have := cap.isLt;omega)]
    simp only [Bool.false_eq_true,ite_false];rw [hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x8000413c#32).getLsbD 0=false;decide) hp2147500348 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v14 : c1.get 14=BitVec.ofNat 32 n := by simp [c1,Core.wr_get_ne,Core.wr_get,h12,h13,h14,h15]
    rw [exec_opimm,v14];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80004140#32).getLsbD 0=false;decide) hp2147500352 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v15 : c2.get 15=cap-BitVec.ofNat 32 pos := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h12,h13,h14,h15]
    have v16 : c2.get 16=BitVec.ofNat 32 n+0xffffffff#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h12,h13,h14,h15]
    rw [exec_branch,v15,v16,HttpPutMath.setup_guard cap pos n hn hc]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80004144#32).getLsbD 0=false;decide) hp2147500356 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v16 : c3.get 16=BitVec.ofNat 32 n+0xffffffff#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h13,h14,h15]
    rw [exec_op,Core.get_zero,v16]
    simp only [alu,show (0 : Word)=0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80004146#32).getLsbD 0=false;decide) hp2147500358 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v15 : c4.get 15=BitVec.ofNat 32 n+0xffffffff#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h13,h14,h15]
    have v13 : c4.get 13=src := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h13,h14,h15]
    rw [exec_op,v15,v13];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80004148#32).getLsbD 0=false;decide) hp2147500360 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v15 : c5.get 15=(BitVec.ofNat 32 n+0xffffffff#32)+src := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h13,h14,h15]
    rw [exec_opimm,v15]
    change Observed.interp B img o (.done (c5.wr 16 (((BitVec.ofNat 32 n+0xffffffff#32)+src)+1#32) 0x8000414c#32)) ram 0 [] [] = _
    rw [ParamMath.decrement n hn,HttpPutMath.finish src n hn];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x8000414c#32).getLsbD 0=false;decide) hp2147500364 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v12 : c6.get 12=BitVec.ofNat 32 pos := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h13,h14,h15]
    rw [exec_op,Core.get_zero,v12]
    simp only [alu,show (0 : Word)=0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp];rfl)
  refine ⟨c7,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.single t6)))))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h13,h14,h15]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h13,h14,h15]
  · intro reg h16 h15;simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h12,h13,h14,h15,h16,h15]
end E5R.Thermostat.HttpPutSetup
