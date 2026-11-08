import Projects.thermostat.MemcpyCode
import Projects.thermostat.ParamMath
import Projects.thermostat.WordZero
import Projects.thermostat.CopyBits
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.CopyLongStart
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (n : Nat) (hs : c.get 2 = sp+16#32) (h12 : c.get 12 = BitVec.ofNat 32 n) (hn : 16≤n) (hb : n<2^32)
    (hp : c.pc = 0x80005182#32) :
    ∃ d, DetSteps B img 5 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80005192#32 ∧
      d.get 6 = 0x80005182#32 ∧ d.get 2 = sp ∧ d.get 13 = 16#32 ∧ (∀ r : Reg, r ≠ 6 → r ≠ 2 → r ≠ 13 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 6 (0x80005182#32) 0x80005186#32
  let c2 := c1.goto 0x8000518a#32
  let c3 := c2.wr 2 (sp) 0x8000518c#32
  let c4 := c3.wr 13 (16#32) 0x8000518e#32
  let c5 := c4.goto 0x80005192#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact cp2147504514) fun o => ?_
    rw [exec_auipc,hp];first | rfl | (rw [hp]; rfl)
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80005186#32).getLsbD 0 = false;decide) cp2147504518 fun o => ?_
    have hv : c1.get 6 = 0x80005182#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,hs,h12]
    rw [exec_jalr,hv]
    change interp B img o (jump c1 ((0x80005182#32+8#32) &&& ~~~1)) ram 0 [] = _
    rw [show (0x80005182#32+8#32) &&& ~~~1 = 0x8000518a#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp]; rfl)
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x8000518a#32).getLsbD 0 = false;decide) cp2147504522 fun o => ?_
    have hv : c2.get 2 = sp+16#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,hs,h12]
    rw [exec_opimm,hv]
    change interp B img o (.done (c2.wr 2 ((sp+16#32)+0xfffffff0#32) 0x8000518c#32)) ram 0 [] = _
    rw [BitVec.add_assoc,show (16#32+0xfffffff0#32)=0#32 by decide +kernel,BitVec.add_zero];first | rfl | (rw [hp]; rfl)
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x8000518c#32).getLsbD 0 = false;decide) cp2147504524 fun o => ?_
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp]; rfl)
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x8000518e#32).getLsbD 0 = false;decide) cp2147504526 fun o => ?_
    have hv12 : c4.get 12 = BitVec.ofNat 32 n := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h12]
    have hv13 : c4.get 13 = 16#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h12]
    rw [exec_branch,hv12,hv13,ParamMath.ult n 16 hb (by decide),decide_eq_false (show ¬n<16 by omega)]
    simp only [ite_false];first | rfl | (rw [hp]; rfl)
  refine ⟨c5,.step s0 (.step s1 (.step s2 (.step s3 (.single s4)))),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h12]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h12]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h12]
  · intro r h6 h2 h13
    simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h12,h6,h2,h13]
end E5R.Thermostat.CopyLongStart
