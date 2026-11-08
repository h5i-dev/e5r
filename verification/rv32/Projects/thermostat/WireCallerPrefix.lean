import Projects.thermostat.WireCallerCode
import Projects.thermostat.WireCallerBytes
import Projects.thermostat.Literal
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.WireCallerPrefix
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (w : Word)
    (hp : c.pc = 0x800005f4#32) (h10 : c.get 10 = w) :
    ∃ d, DetSteps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if byteOf w 0 = 255#8 then 0x800005a2#32 else 0x80000604#32) ∧
      d.get 20 = w >>> 16 ∧ d.get 10 = w ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 20 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 11 255#32 0x800005f8#32
  let c2 := c1.wr 12 (w &&& 255#32) 0x800005fc#32
  let c3 := c2.wr 20 (w >>> 16) 0x80000600#32
  let d := c3.goto (if byteOf w 0 = 255#8 then 0x800005a2#32 else 0x80000604#32)
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact wc2147485172) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x800005f8#32).getLsbD 0 = false;decide) wc2147485176 fun o => ?_
    have hv : c1.get 10 = w := by simp [c1,Core.wr_get_ne,h10]
    rw [exec_opimm,hv];rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x800005fc#32).getLsbD 0 = false;decide) wc2147485180 fun o => ?_
    have hv : c2.get 10 = w := by simp [c2,c1,Core.wr_get_ne,h10]
    rw [exec_opimm,hv];rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨d,ram⟩ := by
    refine detStep_of (by change (0x80000600#32).getLsbD 0 = false;decide) wc2147485184 fun o => ?_
    have v11 : c3.get 11 = 255#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have v12 : c3.get 12 = w &&& 255#32 := by simp [c3,c2,Core.wr_get_ne,Core.wr_get]
    rw [exec_branch,v12,v11,WireCallerBytes.low_mask]
    have ht : taken .eq (BitVec.ofNat 32 (byteOf w 0).toNat) 255#32 = decide (byteOf w 0 = 255#8) := by
      change decide (BitVec.ofNat 32 (byteOf w 0).toNat = BitVec.ofNat 32 (255#8).toNat) = _
      simp only [Literal.byte_injective]
    rw [ht]
    by_cases he : byteOf w 0 = 255#8
    · rw [decide_eq_true he];simp only [ite_true,d,ite_eq_left he]
      change interp B img o (jump c3 (0x80000600#32+0xffffffa2#32)) ram 0 [] = _
      rw [show 0x80000600#32+0xffffffa2#32 = 0x800005a2#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
    · rw [decide_eq_false he];simp only [Bool.false_eq_true,ite_false,d,ite_eq_right he];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.single s3))),rfl,?_,?_,?_,by rfl⟩
  · simp [d,c3,Core.wr_get]
  · simp [d,c3,c2,c1,Core.wr_get_ne,h10]
  · intro r h1 h2 h3;simp [d,c3,c2,c1,Core.wr_get_ne,h1,h2,h3]

theorem ok_tag (w : Word) (cmd : Spec.Command) (h : WireSpec.CommandWord w cmd) : byteOf w 0 ≠ 255#8 := by
  have ht := h ⟨0,by decide⟩ (Encoding.commandTag cmd) rfl
  rw [ht];cases cmd <;> simp only [Encoding.commandTag] <;> decide +kernel
end E5R.Thermostat.WireCallerPrefix
