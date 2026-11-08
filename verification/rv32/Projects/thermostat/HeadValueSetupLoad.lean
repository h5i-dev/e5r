import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadValueSetupLoad
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp k : Word) (h2 : c.get 2=sp) (hword : ramRead ram (sp+4#32) .w=k) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0)
    (hp : c.pc=0x80003068#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000306c#32 ∧
      d.get 15=k+1#32 ∧ (∀ r : Reg, r≠15 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 15 (k) 0x8000306a#32
  let c2 := c1.wr 15 (k+1#32) 0x8000306c#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496040) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_load,h2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1 ha)
     (Memory.block_access stack (off := 4) (by decide) (by decide)),hword];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x8000306a#32).getLsbD 0=false;decide) hh2147496042 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v15 : c1.get 15=k := by simp [c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_opimm,v15];first | rfl | (rw [hp];rfl)
  refine ⟨c2,.step t0 (.single t1),rfl,?_ ,?_ ,by rfl⟩
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · intro reg h15;simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h15]
end E5R.Thermostat.HeadValueSetupLoad
