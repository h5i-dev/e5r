-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ErrorLoad
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.ErrorLoad
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (ptr dst cap : Word) (e : Spec.Error)
    (hp : c.pc=0x80001e52#32) (h10 : c.get 10=ptr) (h11 : c.get 11=dst) (h12 : c.get 12=cap)
    (hs : ReadBytes.Byte B img ram ptr (Errors.code e)) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001e5a#32 ∧
      d.get 8=cap ∧ d.get 12=BitVec.ofNat 32 (Errors.code e).toNat ∧ d.get 10=dst ∧
      (∀ r : Reg, r≠8 → r≠12 → r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 8 cap 0x80001e54#32
  let b := a.wr 12 (BitVec.ofNat 32 (Errors.code e).toNat) 0x80001e58#32
  let d := b.wr 10 dst 0x80001e5a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact ee2147491410) fun o => ?_
    rw [exec_op,Core.get_zero,h12,hp];simp only [alu,show (0:Word)=0#32 from rfl,BitVec.zero_add];rfl
  have t1 : Quiet.Step B img ⟨a,ram⟩ ⟨b,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001e54#32).getLsbD 0=false;decide) ee2147491412 fun o => ?_
    have a10 : a.get 10=ptr := (Core.wr_get_ne _ _ _ _ _ (by decide)).trans h10
    rw [exec_load,a10,BitVec.add_zero,ReadBytes.load hs,ReadBytes.extend_byte,←Memory.ofNat_width];rfl
  have t2 : Quiet.Step B img ⟨b,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001e58#32).getLsbD 0=false;decide) ee2147491416 fun o => ?_
    have b11 : b.get 11=dst := by simp [b,a,Core.wr_get_ne,h11]
    rw [exec_op,Core.get_zero,b11];simp only [alu,show (0:Word)=0#32 from rfl,BitVec.zero_add];rfl
  refine ⟨d,.step t0 (.step t1 (.single t2)),rfl,?_,?_,?_,?_,by rfl⟩
  · simp [d,b,a,Core.wr_get_ne,Core.wr_get]
  · simp [d,b,Core.wr_get_ne,Core.wr_get]
  · simp [d,Core.wr_get]
  · intro reg h8 h12 h10
    simp [d,b,a,Core.wr_get_ne,h8,h12,h10]

end E5R.Thermostat.ErrorLoad
