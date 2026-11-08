import Projects.thermostat.MainTargetEntryCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainRequestTargetLoad
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp start finish : Word) (h2 : c.get 2=sp) (hstart : ramRead ram (sp+36#32) .w=start) (hfinish : ramRead ram (sp+32#32) .w=finish)
(stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0)
    (hp : c.pc=0x80000b6e#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80000b72#32 ∧
      d.get 29=start ∧ d.get 30=finish ∧ (∀ r : Reg, r≠29 → r≠30 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 29 (start) 0x80000b70#32
  let c2 := c1.wr 30 (finish) 0x80000b72#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147486574) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_load,h2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 9 aligned) (Memory.block_access stack (off := 36) (by decide) (by decide)),hstart];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000b70#32).getLsbD 0=false;decide) re2147486576 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v2 : c1.get 2=sp := by simp [c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 8 aligned) (Memory.block_access stack (off := 32) (by decide) (by decide)),hfinish];first | rfl | (rw [hp];rfl)
  refine ⟨c2,.step t0 (.single t1),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · intro reg h29 h30;simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h29,h30]
end E5R.Thermostat.MainRequestTargetLoad
