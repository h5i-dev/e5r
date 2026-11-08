import Projects.thermostat.WritePrefixCode
import Projects.thermostat.FormatData
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.PrefixCharCall
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (writer sign : Word) (h19 : c.get 19 = 0x80005c04#32)
    (h20 : c.get 20 = writer) (h12 : c.get 12 = sign)
    (hrom : B.inRam 0x80005c14#32 4 = false)
    (hp : c.pc = 0x80004e1e#32) :
    ∃ d, DetSteps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002302#32 ∧
      d.get 13 = 0x80002302#32 ∧ d.get 10 = writer ∧ d.get 11 = sign ∧ d.get 1 = 0x80004e28#32 ∧ (∀ r : Reg, r ≠ 13 → r ≠ 10 → r ≠ 11 → r ≠ 1 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 13 (0x80002302#32) 0x80004e22#32
  let c2 := c1.wr 10 (writer) 0x80004e24#32
  let c3 := c2.wr 11 (sign) 0x80004e26#32
  let c4 := c3.wr 1 (0x80004e28#32) 0x80002302#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact wp2147503646) fun o => ?_
    rw [exec_load,h19,show 0x80005c04#32+16#32 = 0x80005c14#32 by decide +kernel,
      interp_load_rom (B := B) (img := img) (w := .w) o (by decide) hrom rfl FormatData.cursor_char_method_word,hp];first | rfl | (rw [hp]; rfl)
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80004e22#32).getLsbD 0 = false;decide) wp2147503650 fun o => ?_
    have hv : c1.get 20 = writer := by simp [c1,Core.wr_get_ne,Core.wr_get,h19,h20,h12]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80004e24#32).getLsbD 0 = false;decide) wp2147503652 fun o => ?_
    have hv : c2.get 12 = sign := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h19,h20,h12]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x80004e26#32).getLsbD 0 = false;decide) wp2147503654 fun o => ?_
    have hv : c3.get 13 = 0x80002302#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h20,h12]
    rw [exec_jalr,hv,BitVec.add_zero]
    change interp B img o (jump (c3.set 1 0x80004e28#32) (0x80002302#32 &&& ~~~1)) ram 0 [] = _
    rw [show 0x80002302#32 &&& ~~~1 = 0x80002302#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp]; rfl)
  refine ⟨c4,.step s0 (.step s1 (.step s2 (.single s3))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h20,h12]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h20,h12]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h20,h12]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h20,h12]
  · intro r h13 h10 h11 h1
    simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h20,h12,h13,h10,h11,h1]
end E5R.Thermostat.PrefixCharCall
