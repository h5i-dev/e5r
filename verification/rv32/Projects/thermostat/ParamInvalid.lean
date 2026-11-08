import Projects.thermostat.ParamCode
import Projects.thermostat.ParamMath
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ParamInvalid
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (b : BitVec 8)
    (hp : c.pc = 0x800027d8#32) (h14 : c.get 14 = p) (h10 : c.get 10 = 10#32)
    (hm : B.inRam p 1 = true) (hb : ram p = b) (hd : DecimalSpec.digit b = false) :
    ∃ d, DetSteps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x800027be#32 ∧
      (∀ r : Reg, r ≠ 15 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 15 (BitVec.ofNat 32 b.toNat) 0x800027dc#32
  let c2 := c1.wr 15 (BitVec.ofNat 32 b.toNat+0xffffffd0#32) 0x800027e0#32
  let c3 := c2.wr 15 (BitVec.ofNat 32 ((b.toNat+208)%256)) 0x800027e4#32
  let d := c3.goto 0x800027be#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact pm2147493848) fun o => ?_
    rw [exec_load,h14,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .b) o
      (by change p.toNat%1 = 0;exact Nat.mod_one _) hm,Memory.load_byte]
    change interp B img o (.done (c.wr 15 (BitVec.ofNat 32 (ram p).toNat) (c.pc+4#32))) ram 0 [] = _
    rw [hb,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x800027dc#32).getLsbD 0 = false;decide) pm2147493852 fun o => ?_
    have hv : c1.get 15 = BitVec.ofNat 32 b.toNat := by simp [c1,Core.wr_get]
    rw [exec_opimm,hv];rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x800027e0#32).getLsbD 0 = false;decide) pm2147493856 fun o => ?_
    have hv : c2.get 15 = BitVec.ofNat 32 b.toNat+0xffffffd0#32 := by simp [c2,Core.wr_get]
    rw [exec_opimm,hv]
    simp only [alu]
    rw [ParamMath.digit_word b];rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨d,ram⟩ := by
    refine detStep_of (by change (0x800027e4#32).getLsbD 0 = false;decide) pm2147493860 fun o => ?_
    have hv15 : c3.get 15 = BitVec.ofNat 32 ((b.toNat+208)%256) := by simp [c3,Core.wr_get]
    have hv10 : c3.get 10 = 10#32 := by simp [c3,c2,c1,Core.wr_get_ne,h10]
    have ht := ParamMath.digit_guard b
    rw [ParamMath.digit_word b,hd] at ht
    rw [exec_branch,hv15,hv10,ht]
    simp only [Bool.not_false,ite_true]
    change interp B img o (jump c3 (0x800027e4#32+0xffffffda#32)) ram 0 [] = _
    rw [show 0x800027e4#32+0xffffffda#32 = 0x800027be#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.single s3))),rfl,?_,by rfl⟩
  intro r hr;simp [d,c3,c2,c1,Core.wr_get_ne,hr]
end E5R.Thermostat.ParamInvalid
