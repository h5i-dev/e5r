import Projects.thermostat.DecodeCode
import Projects.thermostat.Usize
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.ModeIntro
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (len : Nat)
    (hl : len < 2^32) (hp : c.pc = 0x8000215a#32) (h9 : c.get 9 = BitVec.ofNat 32 len) :
    ∃ d n, n ≤ 6 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if len = 4 then 0x8000221c#32 else if len = 3 then 0x8000216e#32 else 0x8000220a#32) ∧
      d.get 10 = 255#32 ∧ d.get 11 = 400#32 ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 4#32 0x8000215c#32
  let c2 := c1.wr 10 255#32 0x80002160#32
  let c3 := c2.wr 11 400#32 0x80002164#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact wd2147492186) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (2147492188#32).getLsbD 0 = false;decide) wd2147492188 fun o => ?_
    rw [exec_opimm,Core.get_zero];rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (2147492192#32).getLsbD 0 = false;decide) wd2147492192 fun o => ?_
    rw [exec_opimm,Core.get_zero];rfl
  have pre : DetSteps B img 3 ⟨c,ram⟩ ⟨c3,ram⟩ := .step s0 (.step s1 (.single s2))
  have v9 : c3.get 9 = BitVec.ofNat 32 len := by simp [c3,c2,c1,Core.wr_get_ne,h9]
  have v12 : c3.get 12 = 4#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  by_cases h4 : len = 4
  · let d := c3.goto 0x8000221c#32
    have sb : DetStep B img ⟨c3,ram⟩ ⟨d,ram⟩ := by
      refine detStep_of (by change (2147492196#32).getLsbD 0 = false;decide) wd2147492196 fun o => ?_
      rw [exec_branch,v9,v12]
      change interp B img o (if taken .eq (BitVec.ofNat 32 len) (BitVec.ofNat 32 4) then _ else _) ram 0 [] = _
      rw [Usize.eq len 4 hl (by decide),decide_eq_true h4]
      simp only [ite_true]
      change interp B img o (jump c3 (0x80002164#32+0xb8#32)) ram 0 [] = _
      rw [show 0x80002164#32+0xb8#32 = 0x8000221c#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
    refine ⟨d,4,by omega,pre.trans (.single sb),by simp [d,h4],?_,?_,?_,by rfl⟩
    · simp [d,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    · simp [d,c3,Core.wr_get]
    · intro r h1 h2 h3;simp [d,c3,c2,c1,Core.wr_get_ne,h1,h2,h3]
  · let c4 := c3.goto 0x80002168#32
    let c5 := c4.wr 12 3#32 0x8000216a#32
    let d := c5.goto (if len = 3 then 0x8000216e#32 else 0x8000220a#32)
    have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
      refine detStep_of (by change (2147492196#32).getLsbD 0 = false;decide) wd2147492196 fun o => ?_
      rw [exec_branch,v9,v12]
      change interp B img o (if taken .eq (BitVec.ofNat 32 len) (BitVec.ofNat 32 4) then _ else _) ram 0 [] = _
      rw [Usize.eq len 4 hl (by decide),decide_eq_false h4];rfl
    have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
      refine detStep_of (by change (2147492200#32).getLsbD 0 = false;decide) wd2147492200 fun o => ?_
      rw [exec_opimm,Core.get_zero];rfl
    have s5 : DetStep B img ⟨c5,ram⟩ ⟨d,ram⟩ := by
      refine detStep_of (by change (2147492202#32).getLsbD 0 = false;decide) wd2147492202 fun o => ?_
      have v9' : c5.get 9 = BitVec.ofNat 32 len := by simp [c5,c4,Core.wr_get_ne,v9]
      have v12' : c5.get 12 = 3#32 := by simp [c5,Core.wr_get]
      rw [exec_branch,v9',v12']
      change interp B img o (if taken .ne (BitVec.ofNat 32 len) (BitVec.ofNat 32 3) then _ else _) ram 0 [] = _
      rw [Usize.ne len 3 hl (by decide)]
      by_cases h3 : len = 3
      · simp only [h3,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,ite_false,d];rfl
      · simp only [h3,ne_eq,not_false_eq_true,decide_true,ite_true,d,ite_false]
        change interp B img o (jump c5 (0x8000216a#32+0xa0#32)) ram 0 [] = _
        rw [show 0x8000216a#32+0xa0#32 = 0x8000220a#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
    refine ⟨d,6,by omega,pre.trans (.step s3 (.step s4 (.single s5))),by simp [d,h4],?_,?_,?_,by rfl⟩
    · simp [d,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    · simp [d,c5,c4,c3,Core.wr_get_ne,Core.wr_get]
    · intro r h1 h2 h3;simp [d,c5,c4,c3,c2,c1,Core.wr_get_ne,h1,h2,h3]
end E5R.Thermostat.ModeIntro
