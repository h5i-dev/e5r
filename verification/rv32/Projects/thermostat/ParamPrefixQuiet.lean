-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ParamPrefix
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.ParamPrefix
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (req pathPtr : Word)
    (path : List (BitVec 8)) (s e count : Nat) (h : ParamInput.Capture B ram req pathPtr path s e count)
    (hp : c.pc = 0x8000278a#32) (h10 : c.get 10 = req) (h11 : c.get 11 = 0#32) :
    ∃ d, Quiet.Steps B img 15 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if 1 ≤ e-s ∧ e-s ≤ 10 then 0x800027c2#32 else 0x800027be#32) ∧
      d.get 11 = BitVec.ofNat 32 e ∧ d.get 14 = BitVec.ofNat 32 s ∧ d.get 12 = BitVec.ofNat 32 (e-s) ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → d.get r = c.get r) ∧ d.sameCsr c := by
  have hpath : path.length < 2^32 := h.bytes.length
  have hs : s < 2^32 := by have := h.ordered;have := h.bounded;omega
  have he : e < 2^32 := by have := h.bounded;omega
  have hl : e-s < 2^32 := by omega
  let c1 := c.wr 12 (BitVec.ofNat 32 count) 0x8000278e#32
  let c2 := c1.goto 0x80002792#32
  let c3 := c2.wr 12 (3#32) 0x80002794#32
  let c4 := c3.goto 0x80002798#32
  let c5 := c4.wr 11 (0#32) 0x8000279a#32
  let c6 := c5.wr 11 (req) 0x8000279c#32
  let c7 := c6.wr 14 (BitVec.ofNat 32 s) 0x800027a0#32
  let c8 := c7.wr 11 (BitVec.ofNat 32 e) 0x800027a4#32
  let c9 := c8.wr 12 (BitVec.ofNat 32 path.length) 0x800027a8#32
  let c10 := c9.goto 0x800027ac#32
  let c11 := c10.goto 0x800027b0#32
  let c12 := c11.wr 12 (BitVec.ofNat 32 (e-s)) 0x800027b4#32
  let c13 := c12.wr 13 (BitVec.ofNat 32 (e-s)+0xfffffff5#32) 0x800027b8#32
  let c14 := c13.wr 15 (0xfffffff5#32) 0x800027ba#32
  let d := c14.goto (if 1 ≤ e-s ∧ e-s ≤ 10 then 0x800027c2#32 else 0x800027be#32)
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact pm2147493770) fun o => ?_
    have hv0 : c.get 10 = req := by simp [Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_load,hv0]
    rw [interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned req 92 h.aligned)
      (Memory.block_access h.object (off := 368) (by decide) (by decide)),h.count_word]
    rw [hp]
    rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000278e#32).getLsbD 0 = false;decide) pm2147493774 fun o => ?_
    have hv0 : c1.get 11 = 0#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    have hv1 : c1.get 12 = BitVec.ofNat 32 count := by simp [c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_branch,hv0,hv1]
    have ht : taken .geu 0#32 (BitVec.ofNat 32 count) = false := by
      simp only [taken]
      rw [BitVec.ult,BitVec.toNat_ofNat]
      change (!decide (0 < count%4294967296)) = false
      have hh : 0 < count%4294967296 := by have := h.count_bound;omega
      simp only [decide_eq_true hh,Bool.not_true]
    rw [ht];rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002792#32).getLsbD 0 = false;decide) pm2147493778 fun o => ?_
    rw [exec_opimm,Core.get_zero]
    rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002794#32).getLsbD 0 = false;decide) pm2147493780 fun o => ?_
    have hv0 : c3.get 12 = 3#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    have hv1 : c3.get 11 = 0#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_branch,hv0,hv1]
    have ht : taken .ltu 3#32 0#32 = false := by decide +kernel
    rw [ht];rfl
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002798#32).getLsbD 0 = false;decide) pm2147493784 fun o => ?_
    have hv0 : c4.get 11 = 0#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_opimm,hv0]
    rfl
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000279a#32).getLsbD 0 = false;decide) pm2147493786 fun o => ?_
    have hv0 : c5.get 11 = 0#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    have hv1 : c5.get 10 = req := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_op,hv0,hv1]
    simp only [alu,BitVec.zero_add];rfl
  have s6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000279c#32).getLsbD 0 = false;decide) pm2147493788 fun o => ?_
    have hv0 : c6.get 11 = req := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_load,hv0]
    rw [interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned req 84 h.aligned)
      (Memory.block_access h.object (off := 336) (by decide) (by decide)),h.start_word]
    rfl
  have s7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine QuietDet.step_of (by change (0x800027a0#32).getLsbD 0 = false;decide) pm2147493792 fun o => ?_
    have hv0 : c7.get 11 = req := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_load,hv0]
    rw [interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned req 85 h.aligned)
      (Memory.block_access h.object (off := 340) (by decide) (by decide)),h.finish_word]
    rfl
  have s8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine QuietDet.step_of (by change (0x800027a4#32).getLsbD 0 = false;decide) pm2147493796 fun o => ?_
    have hv0 : c8.get 10 = req := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_load,hv0]
    rw [interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned req 77 h.aligned)
      (Memory.block_access h.object (off := 308) (by decide) (by decide)),h.path_length]
    rfl
  have s9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine QuietDet.step_of (by change (0x800027a8#32).getLsbD 0 = false;decide) pm2147493800 fun o => ?_
    have hv0 : c9.get 11 = BitVec.ofNat 32 e := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    have hv1 : c9.get 14 = BitVec.ofNat 32 s := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_branch,hv0,hv1]
    rw [ParamMath.ult e s he hs]
    have hno : ¬(e < s) := by have := h.ordered;omega
    simp only [decide_eq_false hno,Bool.false_eq_true,ite_false];rfl
  have s10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine QuietDet.step_of (by change (0x800027ac#32).getLsbD 0 = false;decide) pm2147493804 fun o => ?_
    have hv0 : c10.get 12 = BitVec.ofNat 32 path.length := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    have hv1 : c10.get 11 = BitVec.ofNat 32 e := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_branch,hv0,hv1]
    rw [ParamMath.ult path.length e hpath he]
    have hno : ¬(path.length < e) := by have := h.bounded;omega
    simp only [decide_eq_false hno,Bool.false_eq_true,ite_false];rfl
  have s11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine QuietDet.step_of (by change (0x800027b0#32).getLsbD 0 = false;decide) pm2147493808 fun o => ?_
    have hv0 : c11.get 11 = BitVec.ofNat 32 e := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    have hv1 : c11.get 14 = BitVec.ofNat 32 s := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_op,hv0,hv1]
    simp only [alu]
    rw [ParamMath.difference e s h.ordered];rfl
  have s12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine QuietDet.step_of (by change (0x800027b4#32).getLsbD 0 = false;decide) pm2147493812 fun o => ?_
    have hv0 : c12.get 12 = BitVec.ofNat 32 (e-s) := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h11]
    rw [exec_opimm,hv0]
    rfl
  have s13 : Quiet.Step B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine QuietDet.step_of (by change (0x800027b8#32).getLsbD 0 = false;decide) pm2147493816 fun o => ?_
    rw [exec_opimm,Core.get_zero]
    rfl
  have s14 : Quiet.Step B img ⟨c14,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x800027ba#32).getLsbD 0 = false;decide) pm2147493818 fun o => ?_
    have hv15 : c14.get 15 = 0xfffffff5#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have hv13 : c14.get 13 = BitVec.ofNat 32 (e-s)+0xfffffff5#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_branch,hv15,hv13,ParamMath.length_guard (e-s) hl]
    by_cases hg : 1 ≤ e-s ∧ e-s ≤ 10
    · simp only [d,ite_eq_left hg,decide_eq_true hg,ite_true]
      change interp B img o (jump c14 (0x800027ba#32+8#32)) ram 0 [] = _
      rw [show 0x800027ba#32+8#32 = 0x800027c2#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
    · simp only [d,ite_eq_right hg,decide_eq_false hg,Bool.false_eq_true,ite_false];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.step s11 (.step s12 (.step s13 (.single s14)))))))))))))),rfl,?_,?_,?_,?_,by rfl⟩
  · simp [d,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [d,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [d,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · intro r h1 h2 h3 h4 h5
    simp [d,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h1,h2,h3,h4,h5]

end E5R.Thermostat.ParamPrefix
