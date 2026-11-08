import Projects.thermostat.MemcmpCode
import Projects.thermostat.ParamMath
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.MemcmpAdvance
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p q : Word) (n : Nat)
    (hn : 0 < n) (hb : n < 2^32) (hp : c.pc = 0x80005170#32)
    (h10 : c.get 10 = p) (h11 : c.get 11 = q) (h12 : c.get 12 = BitVec.ofNat 32 n) :
    ∃ d, DetSteps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if n = 1 then 0x80005178#32 else 0x80005164#32) ∧
      d.get 10 = p+1#32 ∧ d.get 11 = q+1#32 ∧ d.get 12 = BitVec.ofNat 32 (n-1) ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 (BitVec.ofNat 32 (n-1)) 0x80005172#32
  let c2 := c1.wr 11 (q+1#32) 0x80005174#32
  let c3 := c2.wr 10 (p+1#32) 0x80005176#32
  let d := c3.goto (if n = 1 then 0x80005178#32 else 0x80005164#32)
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact mc2147504496) fun o => ?_
    rw [exec_opimm,h12]
    change interp B img o (.done (c.wr 12 (BitVec.ofNat 32 n+0xffffffff#32) (c.pc+2#32))) ram 0 [] = _
    rw [ParamMath.decrement n hn,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80005172#32).getLsbD 0 = false;decide) mc2147504498 fun o => ?_
    have hv : c1.get 11 = q := by simp [c1,Core.wr_get_ne,h11]
    rw [exec_opimm,hv];rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80005174#32).getLsbD 0 = false;decide) mc2147504500 fun o => ?_
    have hv : c2.get 10 = p := by simp [c2,c1,Core.wr_get_ne,h10]
    rw [exec_opimm,hv];rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨d,ram⟩ := by
    refine detStep_of (by change (0x80005176#32).getLsbD 0 = false;decide) mc2147504502 fun o => ?_
    have hv : c3.get 12 = BitVec.ofNat 32 (n-1) := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_branch,hv,Core.get_zero,ParamMath.counter_branch n hn hb]
    by_cases he : n = 1
    · simp only [he,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,ite_false,d];rfl
    · simp only [he,ne_eq,not_false_eq_true,decide_true,ite_true,d,ite_false]
      change interp B img o (jump c3 (0x80005176#32+0xffffffee#32)) ram 0 [] = _
      rw [show 0x80005176#32+0xffffffee#32 = 0x80005164#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.single s3))),rfl,?_,?_,?_,?_,by rfl⟩
  · simp [d,c3,Core.wr_get]
  · simp [d,c3,c2,Core.wr_get_ne,Core.wr_get]
  · simp [d,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · intro r h1 h2 h3;simp [d,c3,c2,c1,Core.wr_get_ne,h1,h2,h3]
end E5R.Thermostat.MemcmpAdvance
