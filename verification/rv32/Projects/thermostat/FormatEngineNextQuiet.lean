-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.FormatEngineNext
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.FormatEngineNext
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (ptr : Word) (tag : BitVec 8)
    (hp : c.pc = 0x800049de#32) (h20 : c.get 20 = ptr) (hb : ReadBytes.Byte B img ram ptr tag) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = resultPc tag ∧
      d.get 21 = BitVec.ofNat 32 tag.toNat ∧ d.get 12 = ptr ∧
      (∀ r : Reg, r ≠ 21 → r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  let a := c.wr 21 (BitVec.ofNat 32 tag.toNat) 0x800049e2#32
  let b := a.wr 12 ptr 0x800049e4#32
  let d := b.goto (resultPc tag)
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact fe2147502558) fun o => ?_
    rw [exec_load,h20,BitVec.add_zero,ReadBytes.load hb,ReadBytes.extend_byte,←Memory.ofNat_width,hp];rfl
  have s1 : Quiet.Step B img ⟨a,ram⟩ ⟨b,ram⟩ := by
    refine QuietDet.step_of (by change (0x800049e2#32).getLsbD 0 = false;decide) fe2147502562 fun o => ?_
    have hv : a.get 20 = ptr := by simp [a,Core.wr_get_ne,h20]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];rfl
  have s2 : Quiet.Step B img ⟨b,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x800049e4#32).getLsbD 0 = false;decide) fe2147502564 fun o => ?_
    have hv : b.get 21 = BitVec.ofNat 32 tag.toNat := by simp [b,a,Core.wr_get_ne,Core.wr_get]
    rw [exec_branch,hv,Core.get_zero]
    by_cases hz : tag.toNat = 0
    · rw [hz,show taken .eq (BitVec.ofNat 32 0) (0 : Word) = true by decide]
      simp only [ite_true]
      change interp B img o (jump b 0x80004b12#32) ram 0 [] = _
      rw [jump_ok _ _ (by decide)]
      simp only [d,resultPc,ite_eq_left hz];rfl
    · rw [FormatBits.byte_nonzero tag hz]
      simp only [ite_false]
      change interp B img o (.done (b.goto 0x800049e8#32)) ram 0 [] = _
      simp only [d,resultPc,ite_eq_right hz];rfl
  refine ⟨d,.step s0 (.step s1 (.single s2)),rfl,?_,?_,?_,by rfl⟩
  · simp [d,b,a,Core.wr_get_ne,Core.wr_get]
  · simp [d,b,Core.wr_get]
  · intro r h21 h12;simp [d,b,a,Core.wr_get_ne,h21,h12]

end E5R.Thermostat.FormatEngineNext
