-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.BearerGuard
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.BearerGuard
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (len : Nat)
    (hl : len < 2^32) (hp : c.pc = 0x80000542#32) (h10 : c.get 10 = p)
    (h11 : c.get 11 = BitVec.ofNat 32 len) :
    ∃ d n, n ≤ 5 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if p = 0#32 then 0x800005a8#32 else if len < 7 then 0x800005a2#32 else 0x80000550#32) ∧
      d.get 20 = 401#32 ∧ d.get 22 = 1#32 ∧
      (∀ r : Reg, r ≠ 12 → r ≠ 20 → r ≠ 22 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 22 1#32 0x80000544#32
  let c2 := c1.wr 20 401#32 0x80000548#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact be2147484994) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80000544#32).getLsbD 0 = false;decide) be2147484996 fun o => ?_
    rw [exec_opimm,Core.get_zero];rfl
  have v10 : c2.get 10 = p := by simp [c2,c1,Core.wr_get_ne,h10]
  by_cases hz : p = 0#32
  · let d := c2.goto 0x800005a8#32
    have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨d,ram⟩ := by
      refine QuietDet.step_of (by change (0x80000548#32).getLsbD 0 = false;decide) be2147485000 fun o => ?_
      rw [exec_branch,v10,Core.get_zero,hz]
      have ht : taken .eq 0#32 (0 : Word) = true := by decide +kernel
      rw [ht];simp only [ite_true]
      change interp B img o (jump c2 (0x80000548#32+0x60#32)) ram 0 [] = _
      rw [show 0x80000548#32+0x60#32 = 0x800005a8#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
    refine ⟨d,3,by omega,.step s0 (.step s1 (.single s2)),by simp [d,hz],?_,?_,?_,by rfl⟩
    · simp [d,c2,Core.wr_get]
    · simp [d,c2,c1,Core.wr_get_ne,Core.wr_get]
    · intro r h1 h2 h3;simp [d,c2,c1,Core.wr_get_ne,h2,h3]
  · let c3 := c2.goto 0x8000054a#32
    let c4 := c3.wr 12 7#32 0x8000054c#32
    let d := c4.goto (if len < 7 then 0x800005a2#32 else 0x80000550#32)
    have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
      refine QuietDet.step_of (by change (0x80000548#32).getLsbD 0 = false;decide) be2147485000 fun o => ?_
      rw [exec_branch,v10,Core.get_zero]
      have ht : taken .eq p (0 : Word) = false := by change decide (p = 0#32) = false;exact decide_eq_false hz
      rw [ht];rfl
    have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
      refine QuietDet.step_of (by change (0x8000054a#32).getLsbD 0 = false;decide) be2147485002 fun o => ?_
      rw [exec_opimm,Core.get_zero];rfl
    have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨d,ram⟩ := by
      refine QuietDet.step_of (by change (0x8000054c#32).getLsbD 0 = false;decide) be2147485004 fun o => ?_
      have v11 : c4.get 11 = BitVec.ofNat 32 len := by simp [c4,c3,c2,c1,Core.wr_get_ne,h11]
      have v12 : c4.get 12 = 7#32 := by simp [c4,Core.wr_get]
      rw [exec_branch,v11,v12]
      change interp B img o (if taken .ltu (BitVec.ofNat 32 len) (BitVec.ofNat 32 7) then _ else _) ram 0 [] = _
      rw [ParamMath.ult len 7 hl (by decide)]
      by_cases he : len < 7
      · rw [decide_eq_true he];simp only [ite_true,d,ite_eq_left he]
        change interp B img o (jump c4 (0x8000054c#32+0x56#32)) ram 0 [] = _
        rw [show 0x8000054c#32+0x56#32 = 0x800005a2#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
      · rw [decide_eq_false he];simp only [Bool.false_eq_true,ite_false,d,ite_eq_right he];rfl
    refine ⟨d,5,by omega,.step s0 (.step s1 (.step s2 (.step s3 (.single s4)))),by simp [d,hz],?_,?_,?_,by rfl⟩
    · simp [d,c4,c3,c2,Core.wr_get_ne,Core.wr_get]
    · simp [d,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    · intro r h1 h2 h3;simp [d,c4,c3,c2,c1,Core.wr_get_ne,h1,h2,h3]

end E5R.Thermostat.BearerGuard
