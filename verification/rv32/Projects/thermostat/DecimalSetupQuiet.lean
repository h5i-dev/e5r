-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.DecimalSetup
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.DecimalSetup
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p s : Word) (n : Nat)
    (hn : 0 < n) (hb : n < 2^32) (hp : c.pc = 0x80001dcc#32)
    (h10 : c.get 10 = p) (h11 : c.get 11 = BitVec.ofNat 32 n) (h13 : c.get 13 = s) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80001dd8#32 ∧
      d.get 10 = (p+s)+BitVec.ofNat 32 n ∧ d.get 13 = p+s ∧ d.get 15 = p+s ∧ d.get 14 = 10#32 ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 13 → r ≠ 14 → r ≠ 15 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80001dce#32
  let c2 := c1.wr 13 (p+s) 0x80001dd0#32
  let c3 := c2.wr 10 ((p+s)+BitVec.ofNat 32 n) 0x80001dd4#32
  let c4 := c3.wr 14 10#32 0x80001dd6#32
  let d := c4.wr 15 (p+s) 0x80001dd8#32
  have hz : taken .eq (BitVec.ofNat 32 n) (0 : Word) = false := by
    have he : BitVec.ofNat 32 n ≠ (0 : Word) := by
      intro h
      have hh := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hb] at hh
      change n = 0 at hh;omega
    simpa [taken] using he
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact dc2147491276) fun o => ?_
    rw [exec_branch,h11,Core.get_zero,hz,hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001dce#32).getLsbD 0 = false;decide) dc2147491278 fun o => ?_
    have hv13 : c1.get 13 = s := h13
    have hv10 : c1.get 10 = p := h10
    rw [exec_op,hv13,hv10]
    simp only [alu,BitVec.add_comm s p];rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001dd0#32).getLsbD 0 = false;decide) dc2147491280 fun o => ?_
    have h3 : c2.get 13 = p+s := by simp [c2,Core.wr_get]
    have h1 : c2.get 11 = BitVec.ofNat 32 n := by simp [c2,c1,Core.wr_get_ne,h11]
    rw [exec_op,h3,h1];rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001dd4#32).getLsbD 0 = false;decide) dc2147491284 fun o => ?_
    rw [exec_opimm,Core.get_zero];rfl
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001dd6#32).getLsbD 0 = false;decide) dc2147491286 fun o => ?_
    have h3 : c4.get 13 = p+s := by simp [c4,c3,c2,Core.wr_get_ne,Core.wr_get]
    rw [exec_op,h3,Core.get_zero]
    simp only [alu]
    rw [show (0 : Word) = 0#32 from rfl,BitVec.zero_add];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.single s4)))),rfl,?_,?_,?_,?_,?_,by rfl⟩
  · simp [d,c4,c3,Core.wr_get_ne,Core.wr_get]
  · simp [d,c4,c3,c2,Core.wr_get_ne,Core.wr_get]
  · simp [d,Core.wr_get]
  · simp [d,c4,Core.wr_get_ne,Core.wr_get]
  · intro r h1 h2 h3 h4
    simp [d,c4,c3,c2,c1,Core.wr_get_ne,h1,h2,h3,h4]

end E5R.Thermostat.DecimalSetup
