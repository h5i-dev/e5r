-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.TrimRightStop
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.TrimRightStepQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat E5R.Thermostat.TrimRightStep
namespace E5R.Thermostat.TrimRightStop
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (b : BitVec 8)
    (hp : c.pc = 0x8000211a#32) (h11 : c.get 11 = p)
    (h12 : c.get 12 = 23#32) (h13 : c.get 13 = 0x80001b#32)
    (hm : B.inRam p 1 = true) (hb : ram p = b) (hw : TrimMath.white b = false) :
    ∃ d k, k ≤ 6 ∧ Quiet.Steps B img k ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80001fb4#32 ∧
      (∀ r : Reg, r ≠ 14 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (BitVec.ofNat 32 b.toNat) 0x8000211e#32
  let c2 := c1.wr 14 (BitVec.ofNat 32 b.toNat+0xfffffff7#32) 0x80002120#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := E5R.Thermostat.TrimRightStep.trim_load_step_quiet B c ram p b hp h11 hm hb
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := E5R.Thermostat.TrimRightStep.trim_sub_step_quiet B c1 ram b rfl (by simp [c1,Core.wr_get])
  have hv16 : c2.get 14 = BitVec.ofNat 32 b.toNat+0xfffffff7#32 := by simp [c2,Core.wr_get]
  have hv14 : c2.get 12 = 23#32 := by simp [c2,c1,Core.wr_get_ne,h12]
  by_cases hrange : 9 ≤ b.toNat ∧ b.toNat ≤ 32
  · let c3 := c2.goto 0x80002124#32
    let c4 := c3.wr 14 (TrimMath.shifted b) 0x80002128#32
    let c5 := c4.wr 14 0#32 0x8000212a#32
    let d := c5.goto 0x80001fb4#32
    have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := E5R.Thermostat.TrimRightStep.trim_range_step_quiet B c2 ram b rfl hv16 hv14 hrange
    have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := E5R.Thermostat.TrimRightStep.trim_shift_step_quiet B c3 ram b rfl
      (by simp [c3,c2,c1,Core.wr_get_ne,h13]) hv16
    have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
      have hh := E5R.Thermostat.TrimRightStep.mask_any_quiet B c4 ram b rfl (by simp [c4,Core.wr_get]) hrange
      simpa only [hw,Bool.false_eq_true,ite_false] using hh
    have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨d,ram⟩ := by
      refine QuietDet.step_of (by change (0x8000212a#32).getLsbD 0 = false;decide) tr2147492138 fun o => ?_
      have hv : c5.get 14 = 0#32 := by simp [c5,Core.wr_get]
      rw [exec_branch,hv,Core.get_zero]
      have ht : taken .eq 0#32 (0 : Word) = true := by decide +kernel
      rw [ht]
      simp only [ite_true]
      change interp B img o (jump c5 (0x8000212a#32+0xfffffe8a#32)) ram 0 [] = _
      rw [show 0x8000212a#32+0xfffffe8a#32 = 0x80001fb4#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
    refine ⟨d,6,by decide,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.single s5))))),rfl,?_,by rfl⟩
    intro r hr;simp [d,c5,c4,c3,c2,c1,Core.wr_get_ne,hr]
  · let d := c2.goto 0x80001fb4#32
    have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨d,ram⟩ := by
      refine QuietDet.step_of (by change (0x80002120#32).getLsbD 0 = false;decide) tr2147492128 fun o => ?_
      rw [exec_branch,hv14,hv16,TrimMath.range]
      have he : b.toNat < 9 ∨ 32 < b.toNat := by omega
      simp only [decide_eq_true he,ite_true]
      change interp B img o (jump c2 (0x80002120#32+0xfffffe94#32)) ram 0 [] = _
      rw [show 0x80002120#32+0xfffffe94#32 = 0x80001fb4#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
    refine ⟨d,3,by decide,.step s0 (.step s1 (.single s2)),rfl,?_,by rfl⟩
    intro r hr;simp [d,c2,c1,Core.wr_get_ne,hr]

end E5R.Thermostat.TrimRightStop
