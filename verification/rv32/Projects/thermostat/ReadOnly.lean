import Projects.thermostat.KernelCode
import Projects.thermostat.RamRun
import Projects.thermostat.Memory
import Projects.thermostat.Encoding

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ReadOnly
open E5R E5R.Thermostat

/-- The emitted function recognizes Read (tag 4) for every byte, without writes.
    The caller supplies one readable command byte; no fixed argument address. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80000302) (hr : B.inRam (c.get 10) 1 = true) :
    ∃ d, DetSteps B img 4 ⟨c, ram⟩ ⟨d, ram⟩ ∧
      d.pc = c.get 1 &&& ~~~1 ∧
      d.get 10 = (if ram (c.get 10) = 4#8 then 1 else 0) ∧
      (∀ r : Reg, r ≠ 10 → d.get r = c.get r) ∧ d.sameCsr c := by
  let v := extend .b false (ramRead ram (c.get 10) .b)
  let c1 := c.wr 10 v 0x80000306
  let c2 := c1.wr 10 (v + 0xfffffffc#32) 0x80000308
  let c3 := c2.wr 10 (alu .sltu (v + 0xfffffffc#32) 1#32) 0x8000030c
  let d := c3.goto (c.get 1 &&& ~~~1)
  have s0 : DetStep B img ⟨c, ram⟩ ⟨c1, ram⟩ := by
    refine detStep_of (by rw [hp]; decide) (by rw [hp]; exact d2147484418) fun o => ?_
    rw [exec_load, BitVec.add_zero, interp_load_ram o (by simp only [Width.bytes, Nat.mod_one]) hr, hp]
    rfl
  have s1 : DetStep B img ⟨c1, ram⟩ ⟨c2, ram⟩ := by
    refine detStep_of (by change (0x80000306 : Word).getLsbD 0 = false; decide) d2147484422 fun o => ?_
    rw [exec_opimm]
    simp only [c1, Core.wr_pc, Core.wr_get_self _ 10 _ _ (by decide)]
    rfl
  have s2 : DetStep B img ⟨c2, ram⟩ ⟨c3, ram⟩ := by
    refine detStep_of (by change (0x80000308 : Word).getLsbD 0 = false; decide) d2147484424 fun o => ?_
    rw [exec_opimm]
    simp only [c2, Core.wr_pc, Core.wr_get_self _ 10 _ _ (by decide)]
    rfl
  have s3 : DetStep B img ⟨c3, ram⟩ ⟨d, ram⟩ := by
    refine detStep_of (by change (0x8000030c : Word).getLsbD 0 = false; decide) d2147484428 fun o => ?_
    rw [exec_jalr]
    have ha : c3.get 1 = c.get 1 := by simp [c3, c2, c1, Core.wr_get_ne]
    rw [ha]
    simp only [BitVec.add_zero, Core.set_zero, jump_ok _ _ (clear_bit0 _)]
    rfl
  refine ⟨d, .step s0 (.step s1 (.step s2 (.single s3))), rfl, ?_, ?_, ?_⟩
  · simp only [d, Core.goto_get, c3, Core.wr_get_self _ 10 _ _ (by decide)]
    unfold v
    rw [Memory.load_byte, Memory.ofNat_width]
    exact Memory.read_tag (ram (c.get 10))
  · intro r h
    simp [d, c3, c2, c1, Core.wr_get_ne, h]
  · exact (Core.sameCsr_goto _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
      ((Core.sameCsr_wr _ _ _ _).trans (Core.sameCsr_wr _ _ _ _)))

theorem source_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (cmd : Spec.Command)
    (hp : c.pc = 0x80000302) (hr : B.inRam (c.get 10) 1 = true)
    (hc : ram (c.get 10) = Encoding.commandTag cmd) :
    ∃ d, DetSteps B img 4 ⟨c, ram⟩ ⟨d, ram⟩ ∧
      d.pc = c.get 1 &&& ~~~1 ∧ d.get 10 = (if Spec.readOnly cmd then 1 else 0) ∧
      (∀ r : Reg, r ≠ 10 → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨d,hs,hp,hv,hf,hcsr⟩ := contract B c ram hp hr
  refine ⟨d,hs,hp,?_,hf,hcsr⟩
  rw [hc, Encoding.read_tag] at hv
  exact hv

end E5R.Thermostat.ReadOnly
