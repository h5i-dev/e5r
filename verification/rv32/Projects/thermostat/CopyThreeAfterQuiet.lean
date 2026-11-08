-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.CopyThreeAfter
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.CopyThreeAfter
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp dst finish : Word) (hsp : c.get 2=sp) (h17 : c.get 17=1#32) (h5 : c.get 5=3#32)
    (h14 : c.get 14=dst) (h13 : c.get 13=finish) (h11 : c.get 11=0x80005bc7#32)
    (hm : Memory.Block B sp 16) (ha : sp.toNat%4=0) (hword : ramRead ram (sp+12#32) .w=0x7b000000#32)
    (hlt : E5R.taken .ltu (dst+4#32) finish=true)
    (hp : c.pc = 0x8000522c#32) :
    ∃ d, Quiet.Steps B img 10 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x8000525e#32 ∧
      d.get 16 = 24#32 ∧ d.get 17 = 0x7b000000#32 ∧ d.get 7 = 8#32 ∧ d.get 6 = 0x80005bc4#32 ∧ (∀ r : Reg, r ≠ 16 → r ≠ 17 → r ≠ 7 → r ≠ 6 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 16 (1#32) 0x8000522e#32
  let c2 := c1.wr 17 (0#32) 0x80005232#32
  let c3 := c2.goto 0x800051ec#32
  let c4 := c3.wr 17 (0x7b000000#32) 0x800051ee#32
  let c5 := c4.wr 7 (dst+4#32) 0x800051f2#32
  let c6 := c5.wr 16 (24#32) 0x800051f6#32
  let c7 := c6.wr 6 (0x80005bc4#32) 0x800051fa#32
  let c8 := c7.goto 0x80005256#32
  let c9 := c8.wr 7 (0xffffffe8#32) 0x8000525a#32
  let c10 := c9.wr 7 (8#32) 0x8000525e#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact cp2147504684) fun o => ?_
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp]; rfl)
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000522e#32).getLsbD 0 = false;decide) cp2147504686 fun o => ?_
    have hv : c1.get 17=1#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,hsp,h17,h5,h14,h13,h11]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x80005232#32).getLsbD 0 = false;decide) cp2147504690 fun o => ?_
    have h0 : c2.get 17=0#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,hsp,h17,h5,h14,h13,h11]
    rw [exec_branch,h0,Core.get_zero,show E5R.taken .eq (0#32) (0)=true by decide]
    simp only [ite_true,ite_false]
    try simp only [hp]
    change interp B img o (jump c2 (0x80005232#32+0xffffffba#32)) ram 0 [] = _
    rw [show (0x80005232#32+0xffffffba#32)=0x800051ec#32 by decide +kernel]
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp]; rfl)
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x800051ec#32).getLsbD 0 = false;decide) cp2147504620 fun o => ?_
    have hv : c3.get 2=sp := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,hsp,h17,h5,h14,h13,h11]
    rw [exec_load,hv,interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 3 ha) (Memory.block_access hm (off := 12) (by decide) (by decide)),hword];first | rfl | (rw [hp]; rfl)
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x800051ee#32).getLsbD 0 = false;decide) cp2147504622 fun o => ?_
    have hv : c4.get 14=dst := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hsp,h17,h5,h14,h13,h11]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (0x800051f2#32).getLsbD 0 = false;decide) cp2147504626 fun o => ?_
    have hv : c5.get 5=3#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hsp,h17,h5,h14,h13,h11]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine QuietDet.step_of (by change (0x800051f6#32).getLsbD 0 = false;decide) cp2147504630 fun o => ?_
    have hv11 : c6.get 11=0x80005bc7#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hsp,h17,h5,h14,h13,h11]
    have hv5 : c6.get 5=3#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hsp,h17,h5,h14,h13,h11]
    rw [exec_op,hv11,hv5];first | rfl | (rw [hp]; rfl)
  have s7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine QuietDet.step_of (by change (0x800051fa#32).getLsbD 0 = false;decide) cp2147504634 fun o => ?_
    have hv7 : c7.get 7=dst+4#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hsp,h17,h5,h14,h13,h11]
    have hv13 : c7.get 13=finish := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hsp,h17,h5,h14,h13,h11]
    rw [exec_branch,hv7,hv13,hlt]
    simp only [ite_true]
    change interp B img o (jump c7 0x80005256#32) ram 0 [] = _
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp]; rfl)
  have s8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine QuietDet.step_of (by change (0x80005256#32).getLsbD 0 = false;decide) cp2147504726 fun o => ?_
    have hv : c8.get 16=24#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hsp,h17,h5,h14,h13,h11]
    rw [exec_op,Core.get_zero,hv];first | rfl | (rw [hp]; rfl)
  have s9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000525a#32).getLsbD 0 = false;decide) cp2147504730 fun o => ?_
    have hv : c9.get 7=0xffffffe8#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hsp,h17,h5,h14,h13,h11]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  refine ⟨c10,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.single s9))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hsp,h17,h5,h14,h13,h11]
  · simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hsp,h17,h5,h14,h13,h11]
  · simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hsp,h17,h5,h14,h13,h11]
  · simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hsp,h17,h5,h14,h13,h11]
  · intro r h16 h17 h7 h6
    simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hsp,h17,h5,h14,h13,h11,h16,h17,h7,h6]

end E5R.Thermostat.CopyThreeAfter
