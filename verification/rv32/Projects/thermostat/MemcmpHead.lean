import Projects.thermostat.MemcmpCode
import Projects.thermostat.ReadBytes
import Projects.thermostat.Literal
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.MemcmpHead
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p q : Word) (a b : BitVec 8)
    (hp : c.pc = 0x80005164#32) (h10 : c.get 10 = p) (h11 : c.get 11 = q)
    (ha : ReadBytes.Byte B img ram p a) (hb : ReadBytes.Byte B img ram q b) :
    ∃ d, DetSteps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if a = b then 0x80005170#32 else 0x8000517c#32) ∧
      d.get 13 = BitVec.ofNat 32 a.toNat ∧ d.get 14 = BitVec.ofNat 32 b.toNat ∧
      (∀ r : Reg, r ≠ 13 → r ≠ 14 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 13 (BitVec.ofNat 32 a.toNat) 0x80005168#32
  let c2 := c1.wr 14 (BitVec.ofNat 32 b.toNat) 0x8000516c#32
  let d := c2.goto (if a = b then 0x80005170#32 else 0x8000517c#32)
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact mc2147504484) fun o => ?_
    rw [exec_load,h10,BitVec.add_zero,ReadBytes.load ha,ReadBytes.extend_byte,←Memory.ofNat_width,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80005168#32).getLsbD 0 = false;decide) mc2147504488 fun o => ?_
    have hv : c1.get 11 = q := by simp [c1,Core.wr_get_ne,h11]
    rw [exec_load,hv,BitVec.add_zero,ReadBytes.load hb,ReadBytes.extend_byte,←Memory.ofNat_width];rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨d,ram⟩ := by
    refine detStep_of (by change (0x8000516c#32).getLsbD 0 = false;decide) mc2147504492 fun o => ?_
    have v13 : c2.get 13 = BitVec.ofNat 32 a.toNat := by simp [c2,c1,Core.wr_get_ne,Core.wr_get]
    have v14 : c2.get 14 = BitVec.ofNat 32 b.toNat := by simp [c2,Core.wr_get]
    rw [exec_branch,v13,v14]
    have ht : taken .ne (BitVec.ofNat 32 a.toNat) (BitVec.ofNat 32 b.toNat) = decide (a ≠ b) := by
      change decide (BitVec.ofNat 32 a.toNat ≠ BitVec.ofNat 32 b.toNat) = _
      simp only [ne_eq,Literal.byte_injective]
    rw [ht]
    by_cases he : a = b
    · simp only [he,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,ite_false,d];rfl
    · simp only [he,ne_eq,not_false_eq_true,decide_true,ite_true,d,ite_false]
      change interp B img o (jump c2 (0x8000516c#32+16#32)) ram 0 [] = _
      rw [show 0x8000516c#32+16#32 = 0x8000517c#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  refine ⟨d,.step s0 (.step s1 (.single s2)),rfl,?_,?_,?_,by rfl⟩
  · simp [d,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [d,c2,Core.wr_get]
  · intro r h1 h2;simp [d,c2,c1,Core.wr_get_ne,h1,h2]
end E5R.Thermostat.MemcmpHead
