import Projects.thermostat.MemcpyCode
import Projects.thermostat.ParamMath
import Projects.thermostat.WordZero
import Projects.thermostat.CopyBits
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.CopyAlignedSetup
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst : Word) (n bulk : Nat) (hb : 0<bulk) (hw : dst.toNat+bulk<2^32)
    (h11 : c.get 11 = src) (h12 : c.get 12 = BitVec.ofNat 32 n) (h13 : c.get 13 = 0#32) (h14 : c.get 14 = dst)
    (ha : src.toNat%4=0) (hmask : BitVec.ofNat 32 n &&& 0xfffffffc#32 = BitVec.ofNat 32 bulk)
    (hp : c.pc = 0x800051b6#32) :
    ∃ d, DetSteps B img 8 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80005212#32 ∧
      d.get 11 = src ∧ d.get 12 = BitVec.ofNat 32 n ∧ d.get 15 = BitVec.ofNat 32 bulk ∧ d.get 5 = 0#32 ∧ d.get 13 = dst+BitVec.ofNat 32 bulk ∧ d.get 16 = src ∧ (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 15 → r ≠ 5 → r ≠ 13 → r ≠ 16 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 11 (src) 0x800051b8#32
  let c2 := c1.wr 12 (BitVec.ofNat 32 n) 0x800051ba#32
  let c3 := c2.wr 15 (BitVec.ofNat 32 bulk) 0x800051be#32
  let c4 := c3.wr 5 (0#32) 0x800051c2#32
  let c5 := c4.wr 13 (dst+BitVec.ofNat 32 bulk) 0x800051c6#32
  let c6 := c5.goto 0x8000520c#32
  let c7 := c6.goto 0x80005210#32
  let c8 := c7.wr 16 (src) 0x80005212#32
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact cp2147504566) fun o => ?_
    rw [exec_op,h11,h13];simp only [alu,BitVec.add_zero];first | rfl | (rw [hp]; rfl)
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x800051b8#32).getLsbD 0 = false;decide) cp2147504568 fun o => ?_
    have hv12 : c1.get 12 = BitVec.ofNat 32 n := by simp [c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h14]
    have hv13 : c1.get 13 = 0#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h14]
    rw [exec_op,hv12,hv13];simp only [alu,BitVec.sub_zero];first | rfl | (rw [hp]; rfl)
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x800051ba#32).getLsbD 0 = false;decide) cp2147504570 fun o => ?_
    have hv : c2.get 12 = BitVec.ofNat 32 n := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h14]
    rw [exec_opimm,hv]
    change interp B img o (.done (c2.wr 15 (BitVec.ofNat 32 n &&& 0xfffffffc#32) 0x800051be#32)) ram 0 [] = _
    rw [hmask];first | rfl | (rw [hp]; rfl)
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x800051be#32).getLsbD 0 = false;decide) cp2147504574 fun o => ?_
    have hv : c3.get 11 = src := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h14]
    rw [exec_opimm,hv]
    change interp B img o (.done (c3.wr 5 (src &&& 3#32) 0x800051c2#32)) ram 0 [] = _
    rw [CopyBits.aligned src ha];first | rfl | (rw [hp]; rfl)
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x800051c2#32).getLsbD 0 = false;decide) cp2147504578 fun o => ?_
    have hv14 : c4.get 14 = dst := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h14]
    have hv15 : c4.get 15 = BitVec.ofNat 32 bulk := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h14]
    rw [exec_op,hv14,hv15];first | rfl | (rw [hp]; rfl)
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (0x800051c6#32).getLsbD 0 = false;decide) cp2147504582 fun o => ?_
    have hv : c5.get 5 = 0#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h14]
    rw [exec_branch,hv,Core.get_zero,show E5R.taken .eq 0#32 (0 : Word) = true by decide]
    simp only [ite_true]
    change interp B img o (jump c5 0x8000520c#32) ram 0 [] = _
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp]; rfl)
  have s6 : DetStep B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine detStep_of (by change (0x8000520c#32).getLsbD 0 = false;decide) cp2147504652 fun o => ?_
    have hv14 : c6.get 14 = dst := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h14]
    have hv13 : c6.get 13 = dst+BitVec.ofNat 32 bulk := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h14]
    have ht : E5R.taken .geu dst (dst+BitVec.ofNat 32 bulk) = false := by
      change (!decide (dst.toNat < (dst+BitVec.ofNat 32 bulk).toNat)) = false
      rw [WordZero.add_nat dst bulk hw,decide_eq_true (show dst.toNat<dst.toNat+bulk by omega)];first | rfl | (rw [hp]; rfl)
    rw [exec_branch,hv14,hv13,ht];simp only [ite_false];first | rfl | (rw [hp]; rfl)
  have s7 : DetStep B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine detStep_of (by change (0x80005210#32).getLsbD 0 = false;decide) cp2147504656 fun o => ?_
    have hv : c7.get 11 = src := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h14]
    rw [exec_op,Core.get_zero,hv];simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  refine ⟨c8,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.single s7))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h14]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h14]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h14]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h14]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h14]
  · simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h14]
  · intro r h11 h12 h15 h5 h13 h16
    simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h14,h11,h12,h15,h5,h13,h16]
end E5R.Thermostat.CopyAlignedSetup
