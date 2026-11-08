import Projects.thermostat.HttpPutCode
import Projects.thermostat.HttpPutMath
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HttpPutGuard
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (cap : Word) (pos n : Nat) (hc : pos+n≤cap.toNat)
    (h11 : c.get 11=cap) (h12 : c.get 12=BitVec.ofNat 32 pos) (h14 : c.get 14=BitVec.ofNat 32 n)
    (hp : c.pc=0x80004122#32) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000413a#32 ∧
      d.get 15=cap-BitVec.ofNat 32 pos ∧ d.get 16=0#32 ∧ d.get 17=0#32 ∧ (∀ r : Reg, r≠15 → r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 15 (cap-BitVec.ofNat 32 pos) 0x80004126#32
  let c2 := c1.wr 16 (0#32) 0x8000412a#32
  let c3 := c2.wr 17 (0#32) 0x8000412e#32
  let c4 := c3.wr 16 (0#32) 0x80004132#32
  let c5 := c4.goto 0x8000413a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hp2147500322) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_op,h11,h12];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80004126#32).getLsbD 0=false;decide) hp2147500326 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v11 : c1.get 11=cap := by simp [c1,Core.wr_get_ne,Core.wr_get,h11,h12,h14]
    have v12 : c1.get 12=BitVec.ofNat 32 pos := by simp [c1,Core.wr_get_ne,Core.wr_get,h11,h12,h14]
    rw [exec_op,v11,v12,HttpPutMath.first_guard cap pos n hc];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x8000412a#32).getLsbD 0=false;decide) hp2147500330 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v15 : c2.get 15=cap-BitVec.ofNat 32 pos := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h14]
    have v14 : c2.get 14=BitVec.ofNat 32 n := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h14]
    rw [exec_op,v15,v14,HttpPutMath.second_guard cap pos n hc];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x8000412e#32).getLsbD 0=false;decide) hp2147500334 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v16 : c3.get 16=0#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h14]
    have v17 : c3.get 17=0#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h14]
    rw [exec_op,v16,v17];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80004132#32).getLsbD 0=false;decide) hp2147500338 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v16 : c4.get 16=0#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h14]
    rw [exec_branch,v16,Core.get_zero,show taken .eq 0#32 (0 : Word)=true by decide]
    simp only [ite_true]
    change Observed.interp B img o (jump c4 0x8000413a#32) ram 0 [] [] = _
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c5,.step t0 (.step t1 (.step t2 (.step t3 (.single t4)))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h14]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h14]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h14]
  · intro reg h15 h16 h17;simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h14,h15,h16,h17]
end E5R.Thermostat.HttpPutGuard
