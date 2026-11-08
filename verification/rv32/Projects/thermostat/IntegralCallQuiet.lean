-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.IntegralCall
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.IntegralCall
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (fmt writer sign litPrefix prefixLen : Word)
    (h19 : c.get 19 = fmt) (h22 : c.get 22 = sign) (h21 : c.get 21 = litPrefix) (h20 : c.get 20 = prefixLen)
    (hm : Memory.Block B fmt 14) (ha : fmt.toNat%4 = 0)
    (hw : ramRead ram fmt .w = writer) (hv : ramRead ram (fmt+4#32) .w = 0x80005c04#32)
    (hp : c.pc = 0x800045d0#32) :
    ∃ d, Quiet.Steps B img 9 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80004e00#32 ∧
      d.get 23 = writer ∧ d.get 19 = 0x80005c04#32 ∧ d.get 10 = writer ∧ d.get 11 = 0x80005c04#32 ∧ d.get 12 = sign ∧ d.get 13 = litPrefix ∧ d.get 14 = prefixLen ∧ d.get 1 = 0x800045ea#32 ∧ (∀ r : Reg, r ≠ 23 → r ≠ 19 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 1 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 23 (writer) 0x800045d4#32
  let c2 := c1.wr 19 (0x80005c04#32) 0x800045d8#32
  let c3 := c2.wr 10 (writer) 0x800045da#32
  let c4 := c3.wr 11 (0x80005c04#32) 0x800045dc#32
  let c5 := c4.wr 12 (sign) 0x800045de#32
  let c6 := c5.wr 13 (litPrefix) 0x800045e0#32
  let c7 := c6.wr 14 (prefixLen) 0x800045e2#32
  let c8 := c7.wr 1 (0x800055e2#32) 0x800045e6#32
  let c9 := c8.wr 1 (0x800045ea#32) 0x80004e00#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact pi2147501520) fun o => ?_
    rw [exec_load,h19,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .w) o ha
      (by simpa only [BitVec.add_zero] using Memory.block_access hm (off := 0) (by decide) (by decide)),hw,hp];first | rfl | (rw [hp]; rfl)
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x800045d4#32).getLsbD 0 = false;decide) pi2147501524 fun o => ?_
    have hf : c1.get 19 = fmt := by simp [c1,Core.wr_get_ne,Core.wr_get,h19,h22,h21,h20]
    rw [exec_load,hf,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned fmt 1 ha) (Memory.block_access hm (off := 4) (by decide) (by decide)),hv];first | rfl | (rw [hp]; rfl)
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x800045d8#32).getLsbD 0 = false;decide) pi2147501528 fun o => ?_
    have hv : c2.get 23 = writer := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h19,h22,h21,h20]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x800045da#32).getLsbD 0 = false;decide) pi2147501530 fun o => ?_
    have hv : c3.get 19 = 0x80005c04#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h22,h21,h20]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x800045dc#32).getLsbD 0 = false;decide) pi2147501532 fun o => ?_
    have hv : c4.get 22 = sign := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h22,h21,h20]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (0x800045de#32).getLsbD 0 = false;decide) pi2147501534 fun o => ?_
    have hv : c5.get 21 = litPrefix := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h22,h21,h20]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine QuietDet.step_of (by change (0x800045e0#32).getLsbD 0 = false;decide) pi2147501536 fun o => ?_
    have hv : c6.get 20 = prefixLen := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h22,h21,h20]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];first | rfl | (rw [hp]; rfl)
  have s7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine QuietDet.step_of (by change (0x800045e2#32).getLsbD 0 = false;decide) pi2147501538 fun o => ?_
    rw [exec_auipc];first | rfl | (rw [hp]; rfl)
  have s8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine QuietDet.step_of (by change (0x800045e6#32).getLsbD 0 = false;decide) pi2147501542 fun o => ?_
    have hv : c8.get 1 = 0x800055e2#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h22,h21,h20]
    rw [exec_jalr,hv]
    change interp B img o (jump (c8.set 1 0x800045ea#32) ((0x800055e2#32+0xfffff81e#32) &&& ~~~1)) ram 0 [] = _
    rw [show (0x800055e2#32+0xfffff81e#32) &&& ~~~1 = 0x80004e00#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp]; rfl)
  refine ⟨c9,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.single s8)))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h22,h21,h20]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h22,h21,h20]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h22,h21,h20]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h22,h21,h20]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h22,h21,h20]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h22,h21,h20]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h22,h21,h20]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h22,h21,h20]
  · intro r h23 h19 h10 h11 h12 h13 h14 h1
    simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h19,h22,h21,h20,h23,h19,h10,h11,h12,h13,h14,h1]

end E5R.Thermostat.IntegralCall
