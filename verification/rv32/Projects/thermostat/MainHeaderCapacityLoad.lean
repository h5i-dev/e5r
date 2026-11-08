import Projects.thermostat.MainHeaderCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainHeaderCapacityLoad
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (fp filled : Word) (h8 : c.get 8=fp) (h436 : ramRead ram (fp+436#32) .w=fp+84#32)
(h112 : ramRead ram (fp+112#32) .w=2048#32) (h84 : ramRead ram (fp+84#32) .w=filled)
(object : Memory.Block B fp 465) (aligned : fp.toNat%4=0)
    (hp : c.pc=0x80000a50#32) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80000a58#32 ∧
      d.get 10=filled ∧ d.get 11=2048#32 ∧ (∀ r : Reg, r≠10 → r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (fp+84#32) 0x80000a54#32
  let c2 := c1.wr 11 (2048#32) 0x80000a56#32
  let c3 := c2.wr 10 (filled) 0x80000a58#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact mh2147486288) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v8 : c.get 8=fp := by simp [Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 109 aligned) (Memory.block_access object (off := 436) (by decide) (by decide)),h436];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000a54#32).getLsbD 0=false;decide) mh2147486292 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v8 : c1.get 8=fp := by simp [c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 28 aligned) (Memory.block_access object (off := 112) (by decide) (by decide)),h112];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80000a56#32).getLsbD 0=false;decide) mh2147486294 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v10 : c2.get 10=fp+84#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,v10,BitVec.add_zero,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 21 aligned) (Memory.block_access object (off := 84) (by decide) (by decide)),h84];first | rfl | (rw [hp];rfl)
  refine ⟨c3,.step t0 (.step t1 (.single t2)),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · intro reg h10 h11;simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11]
end E5R.Thermostat.MainHeaderCapacityLoad
