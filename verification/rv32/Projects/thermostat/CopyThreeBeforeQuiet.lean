-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.CopyThreeBefore
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.CopyThreeBefore
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (h7 : c.get 7=1#32) (h11 : c.get 11=0x80005bc7#32) (hro : B.inRam 0x80005bc7#32 1=false)
    (hp : c.pc = 0x800051e0#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80005228#32 ∧
      d.get 16 = 0x7b#32 ∧ (∀ r : Reg, r ≠ 16 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80005224#32
  let c2 := c1.wr 16 (0x7b#32) 0x80005228#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact cp2147504608) fun o => ?_
    have h0 : c.get 7=1#32 := by simp [Core.wr_get_ne,Core.wr_get,h7,h11]
    rw [exec_branch,h0,Core.get_zero,show E5R.taken .ne (1#32) (0)=true by decide]
    simp only [ite_true,ite_false]
    try simp only [hp]
    change interp B img o (jump c 0x80005224#32) ram 0 [] = _
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp]; rfl)
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80005224#32).getLsbD 0 = false;decide) cp2147504676 fun o => ?_
    have hv : c1.get 11=0x80005bc7#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h7,h11]
    rw [exec_load,hv,BitVec.add_zero,interp_load_rom (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) hro rfl CopyInitData.byte_rom];first | rfl | (rw [hp]; rfl)
  refine ⟨c2,.step s0 (.single s1),rfl,?_ ,?_ ,by rfl⟩
  · simp [c2,c1,Core.wr_get_ne,Core.wr_get,h7,h11]
  · intro r h16
    simp [c2,c1,Core.wr_get_ne,Core.wr_get,h7,h11,h16]

end E5R.Thermostat.CopyThreeBefore
