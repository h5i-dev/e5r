-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.FormatEngineSetup
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.FormatEngineSetup
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp obj args desc : Word) (first : BitVec 8)
    (hs : c.get 2 = sp) (h10 : c.get 10 = obj) (h11 : c.get 11 = 0x80005c04#32)
    (h13 : c.get 13 = args) (h12 : c.get 12 = desc) (hargs : args &&& 1#32 = 0#32)
    (hfirst : ReadBytes.Byte B img ram desc first) (hn : first.toNat ≠ 0)
    (hrom : B.inRam 0x80005c10#32 4 = false)
    (hp : c.pc = 0x80004990#32) :
    ∃ d, Quiet.Steps B img 15 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x800049e8#32 ∧
      d.get 8 = sp+64#32 ∧ d.get 9 = args ∧ d.get 18 = 0x80005c04#32 ∧ d.get 11 = 0#32 ∧ d.get 19 = obj ∧ d.get 21 = BitVec.ofNat 32 first.toNat ∧ d.get 24 = 0#32 ∧ d.get 22 = 0x800022a0#32 ∧ d.get 23 = 128#32 ∧ d.get 10 = 0x60000000#32 ∧ d.get 25 = 192#32 ∧ d.get 26 = 0x60000020#32 ∧ (∀ r : Reg, r ≠ 8 → r ≠ 9 → r ≠ 18 → r ≠ 11 → r ≠ 19 → r ≠ 21 → r ≠ 24 → r ≠ 22 → r ≠ 23 → r ≠ 10 → r ≠ 25 → r ≠ 26 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 8 (sp+64#32) 0x80004992#32
  let c2 := c1.wr 9 (args) 0x80004994#32
  let c3 := c2.wr 18 (0x80005c04#32) 0x80004996#32
  let c4 := c3.wr 11 (0#32) 0x8000499a#32
  let c5 := c4.wr 19 (obj) 0x8000499c#32
  let c6 := c5.goto 0x800049a0#32
  let c7 := c6.wr 21 (BitVec.ofNat 32 first.toNat) 0x800049a4#32
  let c8 := c7.goto 0x800049a8#32
  let c9 := c8.wr 24 (0#32) 0x800049aa#32
  let c10 := c9.wr 22 (0x800022a0#32) 0x800049ae#32
  let c11 := c10.wr 23 (128#32) 0x800049b2#32
  let c12 := c11.wr 10 (0x60000000#32) 0x800049b6#32
  let c13 := c12.wr 25 (192#32) 0x800049ba#32
  let c14 := c13.wr 26 (0x60000020#32) 0x800049be#32
  let c15 := c14.goto 0x800049e8#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact fe2147502480) fun o => ?_
    rw [exec_opimm,hs,hp];first | rfl | (rw [hp]; rfl)
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004992#32).getLsbD 0 = false;decide) fe2147502482 fun o => ?_
    have hv : c1.get 13 = args := by simp [c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h12]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004994#32).getLsbD 0 = false;decide) fe2147502484 fun o => ?_
    have hv : c2.get 11 = 0x80005c04#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h12]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x80004996#32).getLsbD 0 = false;decide) fe2147502486 fun o => ?_
    have hv : c3.get 13 = args := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h12]
    rw [exec_opimm,hv]
    change interp B img o (.done (c3.wr 11 (args &&& 1#32) 0x8000499a#32)) ram 0 [] = _
    rw [hargs];first | rfl | (rw [hp]; rfl)
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000499a#32).getLsbD 0 = false;decide) fe2147502490 fun o => ?_
    have hv : c4.get 10 = obj := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h12]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000499c#32).getLsbD 0 = false;decide) fe2147502492 fun o => ?_
    have hv : c5.get 11 = 0#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h12]
    rw [exec_branch,hv,Core.get_zero,show E5R.taken .ne (0#32) (0 : Word) = false by decide]
    simp only [ite_true,ite_false]
    first | rfl | (rw [hp]; rfl)
  have s6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine QuietDet.step_of (by change (0x800049a0#32).getLsbD 0 = false;decide) fe2147502496 fun o => ?_
    have hv : c6.get 12 = desc := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h12]
    rw [exec_load,hv,BitVec.add_zero,ReadBytes.load hfirst,ReadBytes.extend_byte,←Memory.ofNat_width];first | rfl | (rw [hp]; rfl)
  have s7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine QuietDet.step_of (by change (0x800049a4#32).getLsbD 0 = false;decide) fe2147502500 fun o => ?_
    have hv : c7.get 21 = BitVec.ofNat 32 first.toNat := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h12]
    rw [exec_branch,hv,Core.get_zero,FormatBits.byte_nonzero first hn]
    simp only [ite_false];first | rfl | (rw [hp]; rfl)
  have s8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine QuietDet.step_of (by change (0x800049a8#32).getLsbD 0 = false;decide) fe2147502504 fun o => ?_
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp]; rfl)
  have s9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine QuietDet.step_of (by change (0x800049aa#32).getLsbD 0 = false;decide) fe2147502506 fun o => ?_
    have hv : c9.get 18 = 0x80005c04#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h12]
    rw [exec_load,hv,show 0x80005c04#32+12#32 = 0x80005c10#32 by decide +kernel,
      interp_load_rom (B := B) (img := img) (w := .w) o (by decide) hrom rfl FormatLiterals.cursor_method_word];first | rfl | (rw [hp]; rfl)
  have s10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine QuietDet.step_of (by change (0x800049ae#32).getLsbD 0 = false;decide) fe2147502510 fun o => ?_
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp]; rfl)
  have s11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine QuietDet.step_of (by change (0x800049b2#32).getLsbD 0 = false;decide) fe2147502514 fun o => ?_
    rw [exec_lui];first | rfl | (rw [hp]; rfl)
  have s12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine QuietDet.step_of (by change (0x800049b6#32).getLsbD 0 = false;decide) fe2147502518 fun o => ?_
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp]; rfl)
  have s13 : Quiet.Step B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine QuietDet.step_of (by change (0x800049ba#32).getLsbD 0 = false;decide) fe2147502522 fun o => ?_
    have hv : c13.get 10 = 0x60000000#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h12]
    rw [exec_opimm,hv];first | rfl | (rw [hp]; rfl)
  have s14 : Quiet.Step B img ⟨c14,ram⟩ ⟨c15,ram⟩ := by
    refine QuietDet.step_of (by change (0x800049be#32).getLsbD 0 = false;decide) fe2147502526 fun o => ?_
    rw [exec_jal]
    change interp B img o (jump c14 0x800049e8#32) ram 0 [] = _
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp]; rfl)
  refine ⟨c15,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.step s9 (.step s10 (.step s11 (.step s12 (.step s13 (.single s14)))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h12]
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h12]
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h12]
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h12]
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h12]
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h12]
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h12]
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h12]
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h12]
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h12]
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h12]
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h12]
  · intro r h8 h9 h18 h11 h19 h21 h24 h22 h23 h10 h25 h26
    simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,hs,h10,h11,h13,h12,h8,h9,h18,h11,h19,h21,h24,h22,h23,h10,h25,h26]

end E5R.Thermostat.FormatEngineSetup
