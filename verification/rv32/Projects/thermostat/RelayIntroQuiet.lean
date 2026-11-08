-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.RelayIntro
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.RelayIntro
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (len : Nat) (idx : Word)
    (hl : len < 2^32) (hp : c.pc = 0x800021aa#32) (h9 : c.get 9 = BitVec.ofNat 32 len) (h11 : c.get 11 = idx) :
    ∃ d n, n ≤ 6 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if len = 3 then 0x800021de#32 else if len = 2 then 0x800021bc#32 else 0x8000220a#32) ∧
      d.get 12 = idx ∧ d.get 11 = 400#32 ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 idx 0x800021ac#32
  let c2 := c1.wr 13 3#32 0x800021ae#32
  let c3 := c2.wr 11 400#32 0x800021b2#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact wd2147492266) fun o => ?_
    rw [exec_op,Core.get_zero,h11,hp];simp only [alu];rw [show (0 : Word) = 0#32 from rfl,BitVec.zero_add];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (2147492268#32).getLsbD 0 = false;decide) wd2147492268 fun o => ?_
    rw [exec_opimm,Core.get_zero];rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (2147492270#32).getLsbD 0 = false;decide) wd2147492270 fun o => ?_
    rw [exec_opimm,Core.get_zero];rfl
  have pre : Quiet.Steps B img 3 ⟨c,ram⟩ ⟨c3,ram⟩ := .step s0 (.step s1 (.single s2))
  have v9 : c3.get 9 = BitVec.ofNat 32 len := by simp [c3,c2,c1,Core.wr_get_ne,h9]
  have v13 : c3.get 13 = 3#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  by_cases h4 : len = 3
  · let d := c3.goto 0x800021de#32
    have sb : Quiet.Step B img ⟨c3,ram⟩ ⟨d,ram⟩ := by
      refine QuietDet.step_of (by change (2147492274#32).getLsbD 0 = false;decide) wd2147492274 fun o => ?_
      rw [exec_branch,v9,v13]
      change interp B img o (if taken .eq (BitVec.ofNat 32 len) (BitVec.ofNat 32 3) then _ else _) ram 0 [] = _
      rw [Usize.eq len 3 hl (by decide),decide_eq_true h4]
      simp only [ite_true]
      change interp B img o (jump c3 (0x800021b2#32+0x2c#32)) ram 0 [] = _
      rw [show 0x800021b2#32+0x2c#32 = 0x800021de#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
    refine ⟨d,4,by omega,pre.trans (.single sb),by simp [d,h4],?_,?_,?_,by rfl⟩
    · simp [d,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    · simp [d,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    · intro r h1 h2 h3;simp [d,c3,c2,c1,Core.wr_get_ne,h1,h2,h3]
  · let c4 := c3.goto 0x800021b6#32
    let c5 := c4.wr 13 2#32 0x800021b8#32
    let d := c5.goto (if len = 2 then 0x800021bc#32 else 0x8000220a#32)
    have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
      refine QuietDet.step_of (by change (2147492274#32).getLsbD 0 = false;decide) wd2147492274 fun o => ?_
      rw [exec_branch,v9,v13]
      change interp B img o (if taken .eq (BitVec.ofNat 32 len) (BitVec.ofNat 32 3) then _ else _) ram 0 [] = _
      rw [Usize.eq len 3 hl (by decide),decide_eq_false h4];rfl
    have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
      refine QuietDet.step_of (by change (2147492278#32).getLsbD 0 = false;decide) wd2147492278 fun o => ?_
      rw [exec_opimm,Core.get_zero];rfl
    have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨d,ram⟩ := by
      refine QuietDet.step_of (by change (2147492280#32).getLsbD 0 = false;decide) wd2147492280 fun o => ?_
      have v9' : c5.get 9 = BitVec.ofNat 32 len := by simp [c5,c4,Core.wr_get_ne,v9]
      have v13' : c5.get 13 = 2#32 := by simp [c5,Core.wr_get]
      rw [exec_branch,v9',v13']
      change interp B img o (if taken .ne (BitVec.ofNat 32 len) (BitVec.ofNat 32 2) then _ else _) ram 0 [] = _
      rw [Usize.ne len 2 hl (by decide)]
      by_cases h3 : len = 2
      · simp only [h3,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,ite_false,d];rfl
      · simp only [h3,ne_eq,not_false_eq_true,decide_true,ite_true,d,ite_false]
        change interp B img o (jump c5 (0x800021b8#32+0x52#32)) ram 0 [] = _
        rw [show 0x800021b8#32+0x52#32 = 0x8000220a#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
    refine ⟨d,6,by omega,pre.trans (.step s3 (.step s4 (.single s5))),by simp [d,h4],?_,?_,?_,by rfl⟩
    · simp [d,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    · simp [d,c5,c4,c3,Core.wr_get_ne,Core.wr_get]
    · intro r h1 h2 h3;simp [d,c5,c4,c3,c2,c1,Core.wr_get_ne,h1,h2,h3]

end E5R.Thermostat.RelayIntro
