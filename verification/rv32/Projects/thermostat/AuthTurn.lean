import Projects.thermostat.AuthCode
import Projects.thermostat.ReadBytes
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.AuthTurn
open E5R E5R.Thermostat

theorem end_test (q : Word) (n : Nat) (hn : 0 < n) (hb : n < 2^32) :
    taken .ne (q+1#32) (q+BitVec.ofNat 32 n) = decide (n ≠ 1) := by
  have he : q+1#32 = q+BitVec.ofNat 32 n ↔ n = 1 := by
    constructor
    · intro h
      have hh := congrArg BitVec.toNat ((BitVec.add_right_inj q).mp h)
      simp only [BitVec.toNat_ofNat] at hh
      omega
    · intro h;rw [h]
  change decide (q+1#32 ≠ q+BitVec.ofNat 32 n) = _
  simp only [ne_eq,he]

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p q : Word)
    (a b acc : BitVec 8) (n : Nat) (hn : 0 < n) (hb : n < 2^32)
    (ha : ReadBytes.Byte B img ram p a) (hkey : ReadBytes.Byte B img ram q b)
    (hp : c.pc = 0x80000582#32) (h10 : c.get 10 = acc.setWidth 32)
    (h11 : c.get 11 = q) (h12 : c.get 12 = p) (h13 : c.get 13 = q+BitVec.ofNat 32 n) :
    ∃ d, DetSteps B img 7 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if n = 1 then 0x80000596#32 else 0x80000582#32) ∧
      d.get 10 = (acc ||| (a ^^^ b)).setWidth 32 ∧ d.get 11 = q+1#32 ∧ d.get 12 = p+1#32 ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 14 → r ≠ 15 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (a.setWidth 32) 0x80000586#32
  let c2 := c1.wr 15 (b.setWidth 32) 0x8000058a#32
  let c3 := c2.wr 14 ((a ^^^ b).setWidth 32) 0x8000058c#32
  let c4 := c3.wr 11 (q+1#32) 0x8000058e#32
  let c5 := c4.wr 10 ((acc ||| (a ^^^ b)).setWidth 32) 0x80000590#32
  let c6 := c5.wr 12 (p+1#32) 0x80000592#32
  let d := c6.goto (if n = 1 then 0x80000596#32 else 0x80000582#32)
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact au2147485058) fun o => ?_
    rw [exec_load,h12,BitVec.add_zero,ReadBytes.load ha,ReadBytes.extend_byte,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80000586#32).getLsbD 0 = false;decide) au2147485062 fun o => ?_
    have hv : c1.get 11 = q := by simp [c1,Core.wr_get_ne,h11]
    rw [exec_load,hv,BitVec.add_zero,ReadBytes.load hkey,ReadBytes.extend_byte];rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x8000058a#32).getLsbD 0 = false;decide) au2147485066 fun o => ?_
    have v14 : c2.get 14 = a.setWidth 32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get]
    have v15 : c2.get 15 = b.setWidth 32 := by simp [c2,Core.wr_get]
    rw [exec_op,v14,v15]
    simp only [alu,←BitVec.setWidth_xor];rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x8000058c#32).getLsbD 0 = false;decide) au2147485068 fun o => ?_
    have hv : c3.get 11 = q := by simp [c3,c2,c1,Core.wr_get_ne,h11]
    rw [exec_opimm,hv];rfl
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x8000058e#32).getLsbD 0 = false;decide) au2147485070 fun o => ?_
    have v10 : c4.get 10 = acc.setWidth 32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,h10]
    have v14 : c4.get 14 = (a ^^^ b).setWidth 32 := by simp [c4,c3,Core.wr_get_ne,Core.wr_get]
    rw [exec_op,v10,v14]
    simp only [alu,←BitVec.setWidth_or];rfl
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (0x80000590#32).getLsbD 0 = false;decide) au2147485072 fun o => ?_
    have hv : c5.get 12 = p := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,h12]
    rw [exec_opimm,hv];rfl
  have s6 : DetStep B img ⟨c6,ram⟩ ⟨d,ram⟩ := by
    refine detStep_of (by change (0x80000592#32).getLsbD 0 = false;decide) au2147485074 fun o => ?_
    have v11 : c6.get 11 = q+1#32 := by simp [c6,c5,c4,Core.wr_get_ne,Core.wr_get]
    have v13 : c6.get 13 = q+BitVec.ofNat 32 n := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,h13]
    rw [exec_branch,v11,v13,end_test q n hn hb]
    by_cases he : n = 1
    · simp only [he,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,ite_false,d];rfl
    · simp only [he,ne_eq,not_false_eq_true,decide_true,ite_true,d,ite_false]
      change interp B img o (jump c6 (0x80000592#32+0xfffffff0#32)) ram 0 [] = _
      rw [show 0x80000592#32+0xfffffff0#32 = 0x80000582#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.single s6)))))),rfl,?_,?_,?_,?_,by rfl⟩
  · simp [d,c6,c5,Core.wr_get_ne,Core.wr_get]
  · simp [d,c6,c5,c4,Core.wr_get_ne,Core.wr_get]
  · simp [d,c6,Core.wr_get]
  · intro r h1 h2 h3 h4 h5;simp [d,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,h1,h2,h3,h4,h5]
end E5R.Thermostat.AuthTurn
