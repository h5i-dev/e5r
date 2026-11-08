import Projects.thermostat.MainLengthCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainLengthCapacityLoad
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (fp : Word) (h8 : c.get 8=fp) (h112 : ramRead ram (fp+112#32) .w=2048#32) (object : Memory.Block B fp 469) (aligned : fp.toNat%4=0)
    (hp : c.pc=0x80000c3a#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80000c3c#32 ∧
      d.get 11=2048#32 ∧ (∀ r : Reg, r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 11 (2048#32) 0x80000c3c#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact ml2147486778) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_load,h8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned fp 28 aligned) (Memory.block_access object (off := 112) (by decide) (by decide)),h112];first | rfl | (rw [hp];rfl)
  refine ⟨c1,.single t0,rfl,?_ ,?_ ,by rfl⟩
  · simp [c1,Core.wr_get_ne,Core.wr_get,h8]
  · intro reg h11;simp [c1,Core.wr_get_ne,Core.wr_get,h8,h11]
end E5R.Thermostat.MainLengthCapacityLoad
