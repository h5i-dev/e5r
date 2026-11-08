import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadNameCase14
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (v last count sp : Word) (h5 : c.get 5=33#32)
(h6 : c.get 6=48#32)
(h7 : c.get 7=14#32)
(h28 : c.get 28=58#32)
(h27 : c.get 27=91#32)
(h30 : c.get 30=v)
(h15 : c.get 15=last)
(h14 : c.get 14=count)
(h2 : c.get 2=sp)
(hmask : ramRead ram (sp+32#32) .w=9409#32) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0)
(hb0 : taken .ltu (v) (33#32)=true)
    (hp : c.pc=0x80002ff8#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000342c#32 ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x8000342c#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495928) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v30 : c.get 30=v := by simp [Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    have v5 : c.get 5=33#32 := by simp [Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
    rw [exec_branch,v30,v5,hb0]
    rw [hp]
    simp only [ite_true]
    change Observed.interp B img o (jump c (0x80002ff8#32+0x434#32)) ram 0 [] []=_
    rw [show 0x80002ff8#32+0x434#32=0x8000342c#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c1,.single t0,rfl,?_ ,by rfl⟩
  · intro reg ;simp [c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h28,h27,h30,h15,h14,h2]
end E5R.Thermostat.HeadNameCase14
