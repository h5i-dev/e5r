import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadValueCase03
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (v : Word) (h30 : c.get 30=v)
(h12 : c.get 12=9#32)
(hb0 : taken .eq (v) (9#32)=true)
    (hp : c.pc=0x80003086#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80003074#32 ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80003074#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496070) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v30 : c.get 30=v := by simp [Core.wr_get_ne,Core.wr_get,h30,h12]
    have v12 : c.get 12=9#32 := by simp [Core.wr_get_ne,Core.wr_get,h30,h12]
    rw [exec_branch,v30,v12,hb0]
    rw [hp]
    simp only [ite_true]
    change Observed.interp B img o (jump c (0x80003086#32+0xffffffee#32)) ram 0 [] []=_
    rw [show 0x80003086#32+0xffffffee#32=0x80003074#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c1,.single t0,rfl,?_ ,by rfl⟩
  · intro reg ;simp [c1,Core.wr_get_ne,Core.wr_get,h30,h12]
end E5R.Thermostat.HeadValueCase03
