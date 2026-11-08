import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadMethodCase00
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (v : Word) (h5 : c.get 5=9409#32)
(h6 : c.get 6=33#32)
(h7 : c.get 7=48#32)
(h8 : c.get 8=91#32)
(h18 : c.get 18=94#32)
(h29 : c.get 29=14#32)
(h30 : c.get 30=58#32)
(h31 : c.get 31=65#32)
(h19 : c.get 19=v)
(hb0 : taken .ltu (v) (33#32)=true)
    (hp : c.pc=0x80002d06#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002da2#32 ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80002da2#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495174) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v19 : c.get 19=v := by simp [Core.wr_get_ne,Core.wr_get,h5,h6,h7,h8,h18,h29,h30,h31,h19]
    have v6 : c.get 6=33#32 := by simp [Core.wr_get_ne,Core.wr_get,h5,h6,h7,h8,h18,h29,h30,h31,h19]
    rw [exec_branch,v19,v6,hb0]
    simp only [ite_true]
    rw [hp]
    change Observed.interp B img o (jump c (0x80002d06#32+0x9c#32)) ram 0 [] []=_
    rw [show 0x80002d06#32+0x9c#32=0x80002da2#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c1,.single t0,rfl,?_ ,by rfl⟩
  · intro reg ;simp [c1,Core.wr_get_ne,Core.wr_get,h5,h6,h7,h8,h18,h29,h30,h31,h19]
end E5R.Thermostat.HeadMethodCase00
