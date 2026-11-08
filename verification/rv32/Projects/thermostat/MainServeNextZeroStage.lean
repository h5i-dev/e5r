import Projects.thermostat.MainServeNextCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainServeNextZeroStage
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp : Word) :=
  ramWrite (ramWrite (ram) (sp+4512#32) (0#32) .w) (sp+4516#32) (0#32) .h

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (h8 : c.get 8=sp+3204#32) (stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0)
(hword : ramRead ram (sp+4232#32) .w=0#32) (hhalf : extend .h true (ramRead ram (sp+4236#32) .h)=0#32)
    (hp : c.pc=0x80000aee#32) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,memory ram sp⟩ ∧ d.pc=0x80000afe#32 ∧
      d.get 10=0#32 ∧ d.get 11=0#32 ∧ (∀ r : Reg, r≠10 → r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (0#32) 0x80000af2#32
  let c2 := c1.wr 11 (0#32) 0x80000af6#32
  let r1 := ramWrite ram (sp+4512#32) (0#32) .w
  let c3 := c2.goto 0x80000afa#32
  let r2 := ramWrite r1 (sp+4516#32) (0#32) .h
  let c4 := c3.goto 0x80000afe#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact sn2147486446) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v8 : c.get 8=sp+3204#32 := by simp [Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+1028#32=4232#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1058 aligned) (Memory.block_access stack (off := 4232) (by decide) (by decide)),hword];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000af2#32).getLsbD 0=false;decide) sn2147486450 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v8 : c1.get 8=sp+3204#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+1032#32=4236#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned sp 2118 (by omega)) (Memory.block_access stack (off := 4236) (by decide) (by decide)),hhalf];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,r1⟩ := by
    refine Quiet.step_of (by change (0x80000af6#32).getLsbD 0=false;decide) sn2147486454 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 r1 [],[]⟩
    have v8 : c2.get 8=sp+3204#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    have v10 : c2.get 10=0#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_store,v8,v10,BitVec.add_assoc,show 3204#32+1308#32=4512#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1128 aligned) (Memory.block_access stack (off := 4512) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r1⟩ ⟨c4,r2⟩ := by
    refine Quiet.step_of (by change (0x80000afa#32).getLsbD 0=false;decide) sn2147486458 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r1 0 [] [] = ⟨.ok c4 r2 [],[]⟩
    have v8 : c3.get 8=sp+3204#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    have v11 : c3.get 11=0#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
    rw [exec_store,v8,v11,BitVec.add_assoc,show 3204#32+1312#32=4516#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned sp 2258 (by omega)) (Memory.block_access stack (off := 4516) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c4,.step t0 (.step t1 (.step t2 (.single t3))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8]
  · intro reg h10 h11;simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11]
end E5R.Thermostat.MainServeNextZeroStage
