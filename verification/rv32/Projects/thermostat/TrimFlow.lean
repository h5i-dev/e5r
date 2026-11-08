import Projects.thermostat.TrimCode
import Projects.thermostat.Bytes
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.TrimFlow
open E5R E5R.Thermostat

def leftSetup (c : Core) (p l : Word) : Core :=
  let c1 := c.wr 13 (p+l) 0x80001f84#32
  let c2 := c1.wr 15 (0x800000#32) 0x80001f88#32
  let c3 := c2.wr 14 (23#32) 0x80001f8a#32
  let c4 := c3.wr 15 (0x80001b#32) 0x80001f8c#32
  let c5 := c4.wr 8 (p) 0x80001f8e#32
  c5.wr 9 (l) 0x80001f90#32

theorem leftSetup_contract (B : Board) (c : Core) (p l : Word) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80001f80#32) (h11 : c.get 11 = p) (h12 : c.get 12 = l) :
    DetSteps B img 6 ⟨c,ram⟩ ⟨leftSetup c p l,ram⟩ := by
  let c1 := c.wr 13 (p+l) 0x80001f84#32
  let c2 := c1.wr 15 (0x800000#32) 0x80001f88#32
  let c3 := c2.wr 14 (23#32) 0x80001f8a#32
  let c4 := c3.wr 15 (0x80001b#32) 0x80001f8c#32
  let c5 := c4.wr 8 (p) 0x80001f8e#32
  let c6 := c5.wr 9 (l) 0x80001f90#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact tr2147491712) fun o => ?_
    have hv0 : c.get 11 = p := by simp [Core.wr_get_ne,Core.wr_get,h11,h12]
    have hv1 : c.get 12 = l := by simp [Core.wr_get_ne,Core.wr_get,h11,h12]
    rw [exec_op,hv0,hv1,hp]
    rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80001f84#32).getLsbD 0 = false;decide) tr2147491716 fun o => ?_
    rw [exec_lui]
    rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80001f88#32).getLsbD 0 = false;decide) tr2147491720 fun o => ?_
    rw [exec_opimm,Core.get_zero]
    rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x80001f8a#32).getLsbD 0 = false;decide) tr2147491722 fun o => ?_
    have hv0 : c3.get 15 = 0x800000#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12]
    rw [exec_opimm,hv0]
    rfl
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x80001f8c#32).getLsbD 0 = false;decide) tr2147491724 fun o => ?_
    have hv1 : c4.get 11 = p := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12]
    rw [exec_op,Core.get_zero,hv1]
    simp only [alu]
    rw [show (0 : Word) = 0#32 from rfl,BitVec.zero_add];rfl
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (0x80001f8e#32).getLsbD 0 = false;decide) tr2147491726 fun o => ?_
    have hv1 : c5.get 12 = l := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12]
    rw [exec_op,Core.get_zero,hv1]
    simp only [alu]
    rw [show (0 : Word) = 0#32 from rfl,BitVec.zero_add];rfl
  exact .step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.single s5)))))

theorem leftSetup_fields (c : Core) (p l : Word) :
    (leftSetup c p l).pc = 0x80001f90#32 ∧
      (leftSetup c p l).get 13 = p+l ∧
      (leftSetup c p l).get 15 = 0x80001b#32 ∧
      (leftSetup c p l).get 14 = 23#32 ∧
      (leftSetup c p l).get 8 = p ∧
      (leftSetup c p l).get 9 = l ∧
      (∀ r : Reg, r ≠ 13 → r ≠ 15 → r ≠ 14 → r ≠ 8 → r ≠ 9 → (leftSetup c p l).get r = c.get r) ∧ (leftSetup c p l).sameCsr c := by
  refine ⟨rfl,?_, ?_, ?_, ?_, ?_, ?_,by rfl⟩
  · simp [leftSetup,Core.wr_get_ne,Core.wr_get]
  · simp [leftSetup,Core.wr_get_ne,Core.wr_get]
  · simp [leftSetup,Core.wr_get_ne,Core.wr_get]
  · simp [leftSetup,Core.wr_get_ne,Core.wr_get]
  · simp [leftSetup,Core.wr_get_ne,Core.wr_get]
  · intro r h13 h15 h14 h8 h9
    simp [leftSetup,Core.wr_get_ne,h13,h15,h14,h8,h9]

def rightSetup (c : Core) (p l : Word) : Core :=
  let c1 := c.wr 11 (p+l) 0x80002110#32
  let c2 := c1.wr 13 (0x800000#32) 0x80002114#32
  let c3 := c2.wr 11 ((p+l)+0xffffffff#32) 0x80002116#32
  let c4 := c3.wr 12 (23#32) 0x80002118#32
  c4.wr 13 (0x80001b#32) 0x8000211a#32

theorem rightSetup_contract (B : Board) (c : Core) (p l : Word) (ram : Word → BitVec 8)
    (hp : c.pc = 0x8000210e#32) (h11 : c.get 11 = p) (h12 : c.get 12 = l) :
    DetSteps B img 5 ⟨c,ram⟩ ⟨rightSetup c p l,ram⟩ := by
  let c1 := c.wr 11 (p+l) 0x80002110#32
  let c2 := c1.wr 13 (0x800000#32) 0x80002114#32
  let c3 := c2.wr 11 ((p+l)+0xffffffff#32) 0x80002116#32
  let c4 := c3.wr 12 (23#32) 0x80002118#32
  let c5 := c4.wr 13 (0x80001b#32) 0x8000211a#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact tr2147492110) fun o => ?_
    have hv0 : c.get 11 = p := by simp [Core.wr_get_ne,Core.wr_get,h11,h12]
    have hv1 : c.get 12 = l := by simp [Core.wr_get_ne,Core.wr_get,h11,h12]
    rw [exec_op,hv0,hv1,hp]
    rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80002110#32).getLsbD 0 = false;decide) tr2147492112 fun o => ?_
    rw [exec_lui]
    rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80002114#32).getLsbD 0 = false;decide) tr2147492116 fun o => ?_
    have hv0 : c2.get 11 = p+l := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12]
    rw [exec_opimm,hv0]
    rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x80002116#32).getLsbD 0 = false;decide) tr2147492118 fun o => ?_
    rw [exec_opimm,Core.get_zero]
    rfl
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x80002118#32).getLsbD 0 = false;decide) tr2147492120 fun o => ?_
    have hv0 : c4.get 13 = 0x800000#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12]
    rw [exec_opimm,hv0]
    rfl
  exact .step s0 (.step s1 (.step s2 (.step s3 (.single s4))))

theorem rightSetup_fields (c : Core) (p l : Word) :
    (rightSetup c p l).pc = 0x8000211a#32 ∧
      (rightSetup c p l).get 11 = (p+l)+0xffffffff#32 ∧
      (rightSetup c p l).get 13 = 0x80001b#32 ∧
      (rightSetup c p l).get 12 = 23#32 ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 13 → r ≠ 12 → (rightSetup c p l).get r = c.get r) ∧ (rightSetup c p l).sameCsr c := by
  refine ⟨rfl,?_, ?_, ?_, ?_,by rfl⟩
  · simp [rightSetup,Core.wr_get_ne,Core.wr_get]
  · simp [rightSetup,Core.wr_get_ne,Core.wr_get]
  · simp [rightSetup,Core.wr_get_ne,Core.wr_get]
  · intro r h11 h13 h12
    simp [rightSetup,Core.wr_get_ne,h11,h13,h12]

def empty (c : Core) (p : Word) : Core :=
  let c1 := c.wr 9 (0#32) 0x80001fb2#32
  c1.wr 8 (p) 0x80001fb4#32

theorem empty_contract (B : Board) (c : Core) (p : Word) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80001fb0#32) (h11 : c.get 11 = p) :
    DetSteps B img 2 ⟨c,ram⟩ ⟨empty c p,ram⟩ := by
  let c1 := c.wr 9 (0#32) 0x80001fb2#32
  let c2 := c1.wr 8 (p) 0x80001fb4#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact tr2147491760) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp]
    rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80001fb2#32).getLsbD 0 = false;decide) tr2147491762 fun o => ?_
    have hv1 : c1.get 11 = p := by simp [c1,Core.wr_get_ne,Core.wr_get,h11]
    rw [exec_op,Core.get_zero,hv1]
    simp only [alu]
    rw [show (0 : Word) = 0#32 from rfl,BitVec.zero_add];rfl
  exact .step s0 (.single s1)

theorem empty_fields (c : Core) (p : Word) :
    (empty c p).pc = 0x80001fb4#32 ∧
      (empty c p).get 9 = 0#32 ∧
      (empty c p).get 8 = p ∧
      (∀ r : Reg, r ≠ 9 → r ≠ 8 → (empty c p).get r = c.get r) ∧ (empty c p).sameCsr c := by
  refine ⟨rfl,?_, ?_, ?_,by rfl⟩
  · simp [empty,Core.wr_get_ne,Core.wr_get]
  · simp [empty,Core.wr_get_ne,Core.wr_get]
  · intro r h9 h8
    simp [empty,Core.wr_get_ne,h9,h8]

def leftEmpty (c : Core) (p : Word) : Core :=
  let c1 := c.wr 8 (p) 0x80001fae#32
  c1.goto 0x80001fb4#32

theorem leftEmpty_contract (B : Board) (c : Core) (p : Word) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80001fac#32) (h13 : c.get 13 = p) :
    DetSteps B img 2 ⟨c,ram⟩ ⟨leftEmpty c p,ram⟩ := by
  let c1 := c.wr 8 (p) 0x80001fae#32
  let c2 := c1.goto 0x80001fb4#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact tr2147491756) fun o => ?_
    have hv1 : c.get 13 = p := by simp [Core.wr_get_ne,Core.wr_get,h13]
    rw [exec_op,Core.get_zero,hv1,hp]
    simp only [alu]
    rw [show (0 : Word) = 0#32 from rfl,BitVec.zero_add];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80001fae#32).getLsbD 0 = false;decide) tr2147491758 fun o => ?_
    rw [exec_jal]
    have hp1 : c1.pc = 0x80001fae#32 := rfl
    rw [hp1]
    rw [show 0x80001fae#32+0x6#32 = 0x80001fb4#32 by decide +kernel,jump_ok _ _ (by decide)]
    rfl
  exact .step s0 (.single s1)

theorem leftEmpty_fields (c : Core) (p : Word) :
    (leftEmpty c p).pc = 0x80001fb4#32 ∧
      (leftEmpty c p).get 8 = p ∧
      (∀ r : Reg, r ≠ 8 → (leftEmpty c p).get r = c.get r) ∧ (leftEmpty c p).sameCsr c := by
  refine ⟨rfl,?_, ?_,by rfl⟩
  · simp [leftEmpty,Core.wr_get_ne,Core.wr_get]
  · intro r h8
    simp [leftEmpty,Core.wr_get_ne,h8]

def rightEmpty (c : Core) : Core :=
  c.goto 0x80001fb4#32

theorem rightEmpty_contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80002134#32) :
    DetSteps B img 1 ⟨c,ram⟩ ⟨rightEmpty c,ram⟩ := by
  let c1 := c.goto 0x80001fb4#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact tr2147492148) fun o => ?_
    rw [exec_jal,hp]
    rw [show 0x80002134#32+0xfffffe80#32 = 0x80001fb4#32 by decide +kernel,jump_ok _ _ (by decide)]
    rfl
  exact .single s0

theorem rightEmpty_fields (c : Core) :
    (rightEmpty c).pc = 0x80001fb4#32 ∧
      (∀ r : Reg, (rightEmpty c).get r = c.get r) ∧ (rightEmpty c).sameCsr c := by
  refine ⟨rfl,?_,by rfl⟩
  · intro r 
    rfl

theorem entry (B : Board) (c : Core) (ram : Word → BitVec 8) (z : Word)
    (hp : c.pc = 0x80001f7e#32) (hz : c.get 12 = z) :
    DetStep B img ⟨c,ram⟩ ⟨c.goto (if z = 0#32 then 0x80001fb0#32 else 0x80001f80#32),ram⟩ := by
  refine detStep_of (by rw [hp];decide) (by rw [hp];exact tr2147491710) fun o => ?_
  rw [exec_branch,hz,Core.get_zero]
  have ht : taken .eq z (0 : Word) = decide (z = 0#32) := by rfl
  rw [ht]
  by_cases he : z = 0#32
  · simp only [ite_eq_left he,decide_eq_true he,ite_true]
    rw [hp,show 0x80001f7e#32+50#32 = 0x80001fb0#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  · simp only [ite_eq_right he,decide_eq_false he,Bool.false_eq_true,ite_false]
    rw [hp];rfl

end E5R.Thermostat.TrimFlow
