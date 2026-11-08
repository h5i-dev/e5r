-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ParamTurn
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.ParamTurn
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (b : BitVec 8) (a n : Nat)
    (ha : a < 2^32) (hn : 0 < n) (hbound : n < 2^32)
    (hp : c.pc = 0x800027d8#32) (h11 : c.get 11 = BitVec.ofNat 32 a) (h13 : c.get 13 = 0#32)
    (h12 : c.get 12 = BitVec.ofNat 32 n) (h14 : c.get 14 = p) (h10 : c.get 10 = 10#32)
    (hm : B.inRam p 1 = true) (hb : ram p = b) (hd : DecimalSpec.digit b = true) :
    ∃ d, Quiet.Steps B img 18 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if n = 1 then 0x8000280e#32 else 0x800027d8#32) ∧
      d.get 11 = BitVec.ofNat 32 (10*a+(b.toNat-48)) ∧ d.get 13 = BitVec.ofNat 32 ((10*a+(b.toNat-48))/4294967296) ∧
      d.get 12 = BitVec.ofNat 32 (n-1) ∧ d.get 14 = p+1#32 ∧
      (∀ r : Reg, r ≠ 5 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 17 → d.get r = c.get r) ∧ d.sameCsr c := by
  have hdb : 48 ≤ b.toNat ∧ b.toNat ≤ 57 := by simpa only [DecimalSpec.digit,decide_eq_true_eq] using hd
  let c1 := c.wr 15 (BitVec.ofNat 32 b.toNat) 0x800027dc#32
  let c2 := c1.wr 15 (BitVec.ofNat 32 b.toNat+0xffffffd0#32) 0x800027e0#32
  let c3 := c2.wr 15 (BitVec.ofNat 32 (b.toNat-48)) 0x800027e4#32
  let c4 := c3.goto 0x800027e8#32
  let c5 := c4.wr 16 (BitVec.ofNat 32 (10*a/4294967296)) 0x800027ec#32
  let c6 := c5.wr 17 (BitVec.ofNat 32 a <<< 1) 0x800027f0#32
  let c7 := c6.wr 11 (BitVec.ofNat 32 a <<< 3) 0x800027f2#32
  let c8 := c7.wr 17 (BitVec.ofNat 32 (10*a)) 0x800027f4#32
  let c9 := c8.wr 5 (0#32) 0x800027f8#32
  let c10 := c9.wr 13 (0#32) 0x800027fa#32
  let c11 := c10.wr 11 (BitVec.ofNat 32 (10*a+(b.toNat-48))) 0x800027fe#32
  let c12 := c11.wr 13 (0#32) 0x80002800#32
  let c13 := c12.wr 15 (ParamMath.carry a (b.toNat-48)) 0x80002804#32
  let c14 := c13.wr 13 (ParamMath.carry a (b.toNat-48)) 0x80002806#32
  let c15 := c14.wr 12 (BitVec.ofNat 32 (n-1)) 0x80002808#32
  let c16 := c15.wr 14 (p+1#32) 0x8000280a#32
  let c17 := c16.wr 13 (BitVec.ofNat 32 ((10*a+(b.toNat-48))/4294967296)) 0x8000280c#32
  let d := c17.goto (if n = 1 then 0x8000280e#32 else 0x800027d8#32)
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact pm2147493848) fun o => ?_
    rw [exec_load,h14,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .b) o
      (by change p.toNat%1 = 0;exact Nat.mod_one _) hm,Memory.load_byte]
    change interp B img o (.done (c.wr 15 (BitVec.ofNat 32 (ram p).toNat) (c.pc+4#32))) ram 0 [] = _
    rw [hb,hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x800027dc#32).getLsbD 0 = false;decide) pm2147493852 fun o => ?_
    have hv0 : c1.get 15 = BitVec.ofNat 32 b.toNat := by simp [c1,Core.wr_get_ne,Core.wr_get,h11,h13,h12,h14,h10]
    rw [exec_opimm,hv0]
    rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x800027e0#32).getLsbD 0 = false;decide) pm2147493856 fun o => ?_
    have hv0 : c2.get 15 = BitVec.ofNat 32 b.toNat+0xffffffd0#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h11,h13,h12,h14,h10]
    rw [exec_opimm,hv0]
    simp only [alu]
    rw [ParamMath.digit_value b hd];rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x800027e4#32).getLsbD 0 = false;decide) pm2147493860 fun o => ?_
    have hv0 : c3.get 15 = BitVec.ofNat 32 (b.toNat-48) := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h13,h12,h14,h10]
    have hv1 : c3.get 10 = 10#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h13,h12,h14,h10]
    rw [exec_branch,hv0,hv1]
    have ht : taken .geu (BitVec.ofNat 32 (b.toNat-48)) 10#32 = false := by
      simp only [taken]
      rw [BitVec.ult,BitVec.toNat_ofNat]
      change (!decide ((b.toNat-48)%4294967296 < 10)) = false
      have hi : (b.toNat-48)%4294967296 < 10 := by omega
      simp only [decide_eq_true hi,Bool.not_true]
    rw [ht];rfl
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x800027e8#32).getLsbD 0 = false;decide) pm2147493864 fun o => ?_
    have hv0 : c4.get 11 = BitVec.ofNat 32 a := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h13,h12,h14,h10]
    have hv1 : c4.get 10 = 10#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h13,h12,h14,h10]
    rw [exec_muldiv,hv0,hv1]
    rw [ParamMath.mulhu_ten a ha];rfl
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (0x800027ec#32).getLsbD 0 = false;decide) pm2147493868 fun o => ?_
    have hv0 : c5.get 11 = BitVec.ofNat 32 a := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h13,h12,h14,h10]
    rw [exec_opimm,hv0]
    rfl
  have s6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine QuietDet.step_of (by change (0x800027f0#32).getLsbD 0 = false;decide) pm2147493872 fun o => ?_
    have hv0 : c6.get 11 = BitVec.ofNat 32 a := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h13,h12,h14,h10]
    rw [exec_opimm,hv0]
    rfl
  have s7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine QuietDet.step_of (by change (0x800027f2#32).getLsbD 0 = false;decide) pm2147493874 fun o => ?_
    have hv0 : c7.get 17 = BitVec.ofNat 32 a <<< 1 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h13,h12,h14,h10]
    have hv1 : c7.get 11 = BitVec.ofNat 32 a <<< 3 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h13,h12,h14,h10]
    rw [exec_op,hv0,hv1]
    simp only [alu]
    rw [ParamMath.ten_shifts a];rfl
  have s8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine QuietDet.step_of (by change (0x800027f4#32).getLsbD 0 = false;decide) pm2147493876 fun o => ?_
    have hv0 : c8.get 13 = 0#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h13,h12,h14,h10]
    rw [exec_opimm,hv0]
    rfl
  have s9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine QuietDet.step_of (by change (0x800027f8#32).getLsbD 0 = false;decide) pm2147493880 fun o => ?_
    have hv0 : c9.get 13 = 0#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h13,h12,h14,h10]
    rw [exec_opimm,hv0]
    rfl
  have s10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine QuietDet.step_of (by change (0x800027fa#32).getLsbD 0 = false;decide) pm2147493882 fun o => ?_
    have hv0 : c10.get 17 = BitVec.ofNat 32 (10*a) := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h13,h12,h14,h10]
    have hv1 : c10.get 15 = BitVec.ofNat 32 (b.toNat-48) := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h13,h12,h14,h10]
    rw [exec_op,hv0,hv1]
    simp only [alu]
    rw [←BitVec.ofNat_add];rfl
  have s11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine QuietDet.step_of (by change (0x800027fe#32).getLsbD 0 = false;decide) pm2147493886 fun o => ?_
    have hv0 : c11.get 13 = 0#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h13,h12,h14,h10]
    have hv1 : c11.get 5 = 0#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h13,h12,h14,h10]
    rw [exec_op,hv0,hv1]
    rfl
  have s12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002800#32).getLsbD 0 = false;decide) pm2147493888 fun o => ?_
    have hv0 : c12.get 11 = BitVec.ofNat 32 (10*a+(b.toNat-48)) := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h13,h12,h14,h10]
    have hv1 : c12.get 17 = BitVec.ofNat 32 (10*a) := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h13,h12,h14,h10]
    rw [exec_op,hv0,hv1]
    dsimp only [c13]
    unfold ParamMath.carry
    rfl
  have s13 : Quiet.Step B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002804#32).getLsbD 0 = false;decide) pm2147493892 fun o => ?_
    have hv0 : c13.get 13 = 0#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h13,h12,h14,h10]
    have hv1 : c13.get 15 = ParamMath.carry a (b.toNat-48) := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h13,h12,h14,h10]
    rw [exec_op,hv0,hv1]
    simp only [alu,BitVec.zero_add];rfl
  have s14 : Quiet.Step B img ⟨c14,ram⟩ ⟨c15,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002806#32).getLsbD 0 = false;decide) pm2147493894 fun o => ?_
    have hv0 : c14.get 12 = BitVec.ofNat 32 n := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h13,h12,h14,h10]
    rw [exec_opimm,hv0]
    simp only [alu]
    rw [ParamMath.decrement n hn];rfl
  have s15 : Quiet.Step B img ⟨c15,ram⟩ ⟨c16,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002808#32).getLsbD 0 = false;decide) pm2147493896 fun o => ?_
    have hv0 : c15.get 14 = p := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h13,h12,h14,h10]
    rw [exec_opimm,hv0]
    rfl
  have s16 : Quiet.Step B img ⟨c16,ram⟩ ⟨c17,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000280a#32).getLsbD 0 = false;decide) pm2147493898 fun o => ?_
    have hv0 : c16.get 13 = ParamMath.carry a (b.toNat-48) := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h13,h12,h14,h10]
    have hv1 : c16.get 16 = BitVec.ofNat 32 (10*a/4294967296) := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h13,h12,h14,h10]
    rw [exec_op,hv0,hv1]
    simp only [alu]
    rw [ParamMath.carry_add a (b.toNat-48) ha (by omega)];rfl
  have s17 : Quiet.Step B img ⟨c17,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000280c#32).getLsbD 0 = false;decide) pm2147493900 fun o => ?_
    have hv : c17.get 12 = BitVec.ofNat 32 (n-1) := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_branch,hv,Core.get_zero,ParamMath.counter_branch n hn hbound]
    by_cases he : n = 1
    · simp only [d,ite_eq_left he,he,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,ite_false];rfl
    · simp only [d,ite_eq_right he,he,ne_eq,not_false_eq_true,decide_true,ite_true]
      change interp B img o (jump c17 (0x8000280c#32+0xffffffcc#32)) ram 0 [] = _
      rw [show 0x8000280c#32+0xffffffcc#32 = 0x800027d8#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.step s11 (.step s12 (.step s13 (.step s14 (.step s15 (.step s16 (.single s17))))))))))))))))),rfl,?_,?_,?_,?_,?_,by rfl⟩
  · simp [d,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [d,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [d,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [d,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · intro r h5 h11 h12 h13 h14 h15 h16 h17
    simp [d,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h5,h11,h12,h13,h14,h15,h16,h17]

end E5R.Thermostat.ParamTurn
