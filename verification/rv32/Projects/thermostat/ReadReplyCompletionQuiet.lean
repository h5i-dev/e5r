-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ReadReplyCompletion
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.ReadReplyCompletion
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (hs : c.get 2=sp)
    (hp : c.pc = 0x80001b92#32) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80001ba2#32 ∧
      d.get 21 = 6#32 ∧ d.get 18 = 2#32 ∧ d.get 9 = sp+3304#32 ∧ d.get 24 = 0xfffffffe#32 ∧ d.get 13 = 0#32 ∧ (∀ r : Reg, r ≠ 21 → r ≠ 18 → r ≠ 9 → r ≠ 24 → r ≠ 13 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 21 (6#32) 0x80001b94#32
  let c2 := c1.wr 18 (2#32) 0x80001b96#32
  let c3 := c2.wr 9 (sp+2047#32) 0x80001b9a#32
  let c4 := c3.wr 9 (sp+3304#32) 0x80001b9e#32
  let c5 := c4.wr 24 (0xfffffffe#32) 0x80001ba0#32
  let c6 := c5.wr 13 (0#32) 0x80001ba2#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact rr2147490706) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp];first | rfl | (rw [hp]; rfl)
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001b94#32).getLsbD 0 = false;decide) rr2147490708 fun o => ?_
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp]; rfl)
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001b96#32).getLsbD 0 = false;decide) rr2147490710 fun o => ?_
    have hv : c2.get 2=sp := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,hs]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001b9a#32).getLsbD 0 = false;decide) rr2147490714 fun o => ?_
    have hv : c3.get 9=sp+2047#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs]
    rw [exec_opimm,hv]
    change interp B img o (.done (c3.wr 9 ((sp+2047#32)+1257#32) 0x80001b9e#32)) ram 0 [] = _
    rw [BitVec.add_assoc,show 2047#32+1257#32=3304#32 by decide +kernel];first | rfl | (rw [hp]; rfl)
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001b9e#32).getLsbD 0 = false;decide) rr2147490718 fun o => ?_
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp]; rfl)
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001ba0#32).getLsbD 0 = false;decide) rr2147490720 fun o => ?_
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp]; rfl)
  refine ⟨c6,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.single s5))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs]
  · intro r h21 h18 h9 h24 h13
    simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h21,h18,h9,h24,h13]

end E5R.Thermostat.ReadReplyCompletion
