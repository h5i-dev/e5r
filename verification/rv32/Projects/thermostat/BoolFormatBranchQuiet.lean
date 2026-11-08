-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.BoolFormatBranch
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.BoolFormatBranch
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (src fmt : Word) (b : Bool)
    (hp : c.pc = 0x80005112#32) (h10 : c.get 10 = src) (h11 : c.get 11 = fmt)
    (hb : ReadBytes.Byte B img ram src (Encoding.boolByte b)) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = (if b then 0x8000511a#32 else 0x8000512c#32) ∧
      d.get 10 = fmt ∧ (∀ r : Reg, r ≠ 10 → r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 (BitVec.ofNat 32 (Encoding.boolByte b).toNat) 0x80005116#32
  let c2 := c1.wr 10 fmt 0x80005118#32
  let d := c2.goto (if b then 0x8000511a#32 else 0x8000512c#32)
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact bf2147504402) fun o => ?_
    rw [exec_load,h10,BitVec.add_zero,ReadBytes.load hb,ReadBytes.extend_byte,←Memory.ofNat_width,hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80005116#32).getLsbD 0 = false;decide) bf2147504406 fun o => ?_
    have hv : c1.get 11 = fmt := by simp [c1,Core.wr_get_ne,h11]
    rw [exec_op,Core.get_zero,hv]
    simp only [alu,show (0 : Word) = 0#32 from rfl,BitVec.zero_add];rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x80005118#32).getLsbD 0 = false;decide) bf2147504408 fun o => ?_
    have hv : c2.get 12 = BitVec.ofNat 32 (Encoding.boolByte b).toNat := by simp [c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_branch,hv,Core.get_zero]
    cases b with
    | false =>
      have ht : taken .eq (BitVec.ofNat 32 (Encoding.boolByte false).toNat) (0 : Word) = true := by decide +kernel
      rw [ht];simp only [ite_true]
      change interp B img o (jump c2 0x8000512c#32) ram 0 [] = _
      rw [jump_ok _ _ (by decide)];rfl
    | true =>
      have ht : taken .eq (BitVec.ofNat 32 (Encoding.boolByte true).toNat) (0 : Word) = false := by decide +kernel
      rw [ht];rfl
  refine ⟨d,.step s0 (.step s1 (.single s2)),rfl,?_,?_,by rfl⟩
  · simp [d,c2,Core.wr_get]
  · intro r h10 h12;simp [d,c2,c1,Core.wr_get_ne,h10,h12]

end E5R.Thermostat.BoolFormatBranch
