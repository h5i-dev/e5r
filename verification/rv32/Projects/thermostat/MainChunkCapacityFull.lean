import Projects.thermostat.MainChunkReceiveCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainChunkCapacityFull
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (h8 : c.get 8=sp+3204#32) (h10 : c.get 10=2048#32)
(hm : Memory.Block B sp 4928) (ha : sp.toNat%4=0)
(hcap : ramRead ram (sp+3316#32) .w=2048#32)
    (hp : c.pc=0x80000f8c#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001bb0#32 ∧
      d.get 11=2048#32 ∧ (∀ r : Reg, r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 11 (2048#32) 0x80000f8e#32
  let c2 := c1.goto 0x80001bb0#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact cr2147487628) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_load,h8,BitVec.add_assoc,show 3204#32+112#32=3316#32 by decide +kernel,
    Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 829 ha)
    (Memory.block_access hm (off := 3316) (by decide) (by decide)),hcap,hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000f8e#32).getLsbD 0=false;decide) cr2147487630 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v11 : c1.get 11=2048#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    have v10 : c1.get 10=2048#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    rw [exec_branch,v11,v10,show taken .eq 2048#32 2048#32=true by decide +kernel]
    simp only [ite_true]
    change Observed.interp B img o (jump c1 (0x80000f8e#32+0xc22#32)) ram 0 [] []=_
    rw [show 0x80000f8e#32+0xc22#32=0x80001bb0#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c2,.step t0 (.single t1),rfl,?_ ,?_ ,by rfl⟩
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
  · intro reg h11;simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11]
end E5R.Thermostat.MainChunkCapacityFull
