-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.CopyUnalignedHeader
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.CopyUnalignedHeader
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst offset : Word) (n bulk : Nat)
    (h11 : c.get 11=src) (h12 : c.get 12=BitVec.ofNat 32 n) (h13 : c.get 13=0#32) (h14 : c.get 14=dst)
    (hm : BitVec.ofNat 32 n &&& 0xfffffffc#32=BitVec.ofNat 32 bulk) (ho : src &&& 3#32=offset) (hz : offset≠0#32)
    (hp : c.pc = 0x800051b6#32) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x800051ca#32 ∧
      d.get 11 = src ∧ d.get 12 = BitVec.ofNat 32 n ∧ d.get 15 = BitVec.ofNat 32 bulk ∧ d.get 5 = offset ∧ d.get 13 = dst+BitVec.ofNat 32 bulk ∧ (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 15 → r ≠ 5 → r ≠ 13 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 11 (src) 0x800051b8#32
  let c2 := c1.wr 12 (BitVec.ofNat 32 n) 0x800051ba#32
  let c3 := c2.wr 15 (BitVec.ofNat 32 bulk) 0x800051be#32
  let c4 := c3.wr 5 (offset) 0x800051c2#32
  let c5 := c4.wr 13 (dst+BitVec.ofNat 32 bulk) 0x800051c6#32
  let c6 := c5.goto 0x800051ca#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact cp2147504566) fun o => ?_
    rw [exec_op,h11,h13];simp only [alu,BitVec.add_zero];first | rfl | (rw [hp]; rfl)
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x800051b8#32).getLsbD 0 = false;decide) cp2147504568 fun o => ?_
    have hv12 : c1.get 12=BitVec.ofNat 32 n := by simp [c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h14]
    have hv13 : c1.get 13=0#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h14]
    rw [exec_op,hv12,hv13];simp only [alu,BitVec.sub_zero];first | rfl | (rw [hp]; rfl)
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x800051ba#32).getLsbD 0 = false;decide) cp2147504570 fun o => ?_
    have hv : c2.get 12=BitVec.ofNat 32 n := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h14]
    rw [exec_opimm,hv]
    change interp B img o (.done (c2.wr 15 (BitVec.ofNat 32 n &&& 0xfffffffc#32) 0x800051be#32)) ram 0 [] = _
    rw [hm];first | rfl | (rw [hp]; rfl)
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x800051be#32).getLsbD 0 = false;decide) cp2147504574 fun o => ?_
    have hv : c3.get 11=src := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h14]
    rw [exec_opimm,hv]
    change interp B img o (.done (c3.wr 5 (src &&& 3#32) 0x800051c2#32)) ram 0 [] = _
    rw [ho];first | rfl | (rw [hp]; rfl)
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x800051c2#32).getLsbD 0 = false;decide) cp2147504578 fun o => ?_
    have hv14 : c4.get 14=dst := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h14]
    have hv15 : c4.get 15=BitVec.ofNat 32 bulk := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h14]
    rw [exec_op,hv14,hv15];first | rfl | (rw [hp]; rfl)
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (0x800051c6#32).getLsbD 0 = false;decide) cp2147504582 fun o => ?_
    have hv : c5.get 5=offset := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h14]
    rw [exec_branch,hv,Core.get_zero,show E5R.taken .eq offset (0:Word)=false by simp [taken,hz]]
    simp only [ite_false];first | rfl | (rw [hp]; rfl)
  refine ⟨c6,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.single s5))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h14]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h14]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h14]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h14]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h14]
  · intro r h11 h12 h15 h5 h13
    simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h12,h13,h14,h11,h12,h15,h5,h13]

end E5R.Thermostat.CopyUnalignedHeader
