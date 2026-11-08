import Projects.thermostat.MainChunkCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainChunkExhausted
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp filled : Word) (h8 : c.get 8=sp+3204#32) (h24 : c.get 24=filled)
(hm : Memory.Block B sp 4928) (ha : sp.toNat%4=0)
(hfilledPtr : ramRead ram (sp+3640#32) .w=sp+3288#32)
(hfilled : ramRead ram (sp+3288#32) .w=filled)
    (hp : c.pc=0x80000e9a#32) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80000f8c#32 ∧
      d.get 10=filled ∧ (∀ r : Reg, r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (sp+3288#32) 0x80000e9e#32
  let c2 := c1.wr 10 (filled) 0x80000ea0#32
  let c3 := c2.goto 0x80000f8c#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact cc2147487386) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_load,h8,BitVec.add_assoc,show 3204#32+436#32=3640#32 by decide +kernel,
    Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 910 ha)
    (Memory.block_access hm (off := 3640) (by decide) (by decide)),hfilledPtr,hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000e9e#32).getLsbD 0=false;decide) cc2147487390 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v10 : c1.get 10=sp+3288#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h24]
    rw [exec_load,v10,BitVec.add_zero,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o
    (Memory.word_aligned sp 822 ha) (Memory.block_access hm (off := 3288) (by decide) (by decide)),hfilled];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80000ea0#32).getLsbD 0=false;decide) cc2147487392 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v10 : c2.get 10=filled := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h24]
    have v24 : c2.get 24=filled := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h24]
    have ht : taken .geu filled filled=true := by simp [taken,BitVec.ult]
    rw [exec_branch,v24,v10,ht];simp only [ite_true]
    rw [show c2.pc=0x80000ea0#32 from rfl]
    rw [show 0x80000ea0#32+0xec#32=0x80000f8c#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c3,.step t0 (.step t1 (.single t2)),rfl,?_ ,?_ ,by rfl⟩
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h24]
  · intro reg h10;simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h24,h10]
end E5R.Thermostat.MainChunkExhausted
