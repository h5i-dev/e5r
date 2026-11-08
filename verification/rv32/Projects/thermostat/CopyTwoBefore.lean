import Projects.thermostat.MemcpyCode
import Projects.thermostat.CopyInitData
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.CopyTwoBefore
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (h7 : c.get 7=0#32) (h17 : c.get 17=2#32) (h11 : c.get 11=0x80005ba6#32)
    (h16 : c.get 16=0#32) (h6 : c.get 6=sp+14#32)
    (hro : B.inRam 0x80005ba6#32 2=false)
    (hp : c.pc = 0x800051e0#32) :
    ∃ d, DetSteps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80005240#32 ∧
      d.get 17 = 0x227b#32 ∧ d.get 16 = sp+14#32 ∧ (∀ r : Reg, r ≠ 17 → r ≠ 16 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x800051e4#32
  let c2 := c1.wr 17 (2#32) 0x800051e8#32
  let c3 := c2.goto 0x80005236#32
  let c4 := c3.wr 17 (0x80005ba6#32) 0x8000523a#32
  let c5 := c4.wr 17 (0x227b#32) 0x8000523e#32
  let c6 := c5.wr 16 (sp+14#32) 0x80005240#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact cp2147504608) fun o => ?_
    have h0 : c.get 7=0#32 := by simp [Core.wr_get_ne,Core.wr_get,h7,h17,h11,h16,h6]
    rw [exec_branch,h0,Core.get_zero,show E5R.taken .ne (0#32) (0)=false by decide]
    simp only [ite_true,ite_false]
    first | rfl | (rw [hp]; rfl)
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x800051e4#32).getLsbD 0 = false;decide) cp2147504612 fun o => ?_
    have hv : c1.get 17=2#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h7,h17,h11,h16,h6]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x800051e8#32).getLsbD 0 = false;decide) cp2147504616 fun o => ?_
    have h0 : c2.get 17=2#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h7,h17,h11,h16,h6]
    rw [exec_branch,h0,Core.get_zero,show E5R.taken .ne (2#32) (0)=true by decide]
    simp only [ite_true,ite_false]
    try simp only [hp]
    change interp B img o (jump c2 0x80005236#32) ram 0 [] = _
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp]; rfl)
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x80005236#32).getLsbD 0 = false;decide) cp2147504694 fun o => ?_
    have hv11 : c3.get 11=0x80005ba6#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h7,h17,h11,h16,h6]
    have hv16 : c3.get 16=0#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h7,h17,h11,h16,h6]
    rw [exec_op,hv11,hv16];simp only [alu,BitVec.add_zero];first | rfl | (rw [hp]; rfl)
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x8000523a#32).getLsbD 0 = false;decide) cp2147504698 fun o => ?_
    have hv : c4.get 17=0x80005ba6#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h7,h17,h11,h16,h6]
    rw [exec_load,hv,BitVec.add_zero,interp_load_rom (B := B) (img := img) (w := .h) o (by decide) hro rfl CopyInitData.half_rom];first | rfl | (rw [hp]; rfl)
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (0x8000523e#32).getLsbD 0 = false;decide) cp2147504702 fun o => ?_
    have hv16 : c5.get 16=0#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h7,h17,h11,h16,h6]
    have hv6 : c5.get 6=sp+14#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h7,h17,h11,h16,h6]
    rw [exec_op,hv16,hv6];simp only [alu,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  refine ⟨c6,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.single s5))))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h7,h17,h11,h16,h6]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h7,h17,h11,h16,h6]
  · intro r h17 h16
    simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h7,h17,h11,h16,h6,h17,h16]
end E5R.Thermostat.CopyTwoBefore
