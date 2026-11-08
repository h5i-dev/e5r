import Projects.thermostat.MainChunkCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainChunkGuard
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp index filled : Word) (h8 : c.get 8=sp+3204#32) (h24 : c.get 24=index)
    (hm : Memory.Block B sp 4928) (ha : sp.toNat%4=0)
    (hfilledPtr : ramRead ram (sp+3640#32) .w=sp+3288#32)
    (hfilled : ramRead ram (sp+3288#32) .w=filled) (hcap : ramRead ram (sp+3316#32) .w=2048#32)
    (hinput : index.toNat<filled.toNat) (hbound : filled.toNat≤2048)
    (hp : c.pc=0x80000e9a#32) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80000eaa#32 ∧
      d.get 10=filled ∧ d.get 11=2048#32 ∧ (∀ r : Reg, r≠10 → r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (sp+3288#32) 0x80000e9e#32
  let c2 := c1.wr 10 (filled) 0x80000ea0#32
  let c3 := c2.goto 0x80000ea4#32
  let c4 := c3.wr 11 (2048#32) 0x80000ea6#32
  let c5 := c4.goto 0x80000eaa#32
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
    have v24 : c2.get 24=index := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h24]
    have ht : taken .geu index filled=false := by simp [taken,BitVec.ult,hinput]
    rw [exec_branch,v24,v10,ht];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80000ea4#32).getLsbD 0=false;decide) cc2147487396 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v8 : c3.get 8=sp+3204#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h24]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+112#32=3316#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 829 ha)
        (Memory.block_access hm (off := 3316) (by decide) (by decide)),hcap];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80000ea6#32).getLsbD 0=false;decide) cc2147487398 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v11 : c4.get 11=2048#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h24]
    have v24 : c4.get 24=index := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h24]
    have ht : taken .geu index 2048#32=false := by simp [taken,BitVec.ult,show index.toNat<2048 by omega]
    rw [exec_branch,v24,v11,ht];first | rfl | (rw [hp];rfl)
  refine ⟨c5,.step t0 (.step t1 (.step t2 (.step t3 (.single t4)))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h24]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h24]
  · intro reg h10 h11;simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h24,h10,h11]
end E5R.Thermostat.MainChunkGuard
