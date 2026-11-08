-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.TrimRightStep
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.TrimRightStep
theorem trim_shift_step_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (b : BitVec 8)
    (hp : c.pc = 0x80002124#32) (h13 : c.get 13 = 0x80001b#32)
    (h16 : c.get 14 = BitVec.ofNat 32 b.toNat+0xfffffff7#32) :
    Quiet.Step B img ⟨c,ram⟩ ⟨c.wr 14 (TrimMath.shifted b) 0x80002128#32,ram⟩ := by
  refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact tr2147492132) fun o => ?_
  rw [exec_op,h13,h16,hp]
  unfold TrimMath.shifted
  rfl

end E5R.Thermostat.TrimRightStep
namespace E5R.Thermostat.TrimRightStep
theorem trim_load_step_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (b : BitVec 8)
    (hp : c.pc = 0x8000211a#32) (h11 : c.get 11 = p) (hm : B.inRam p 1 = true) (hb : ram p = b) :
    Quiet.Step B img ⟨c,ram⟩ ⟨c.wr 14 (BitVec.ofNat 32 b.toNat) 0x8000211e#32,ram⟩ := by
  refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact tr2147492122) fun o => ?_
  rw [exec_load,h11,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .b) o
    (by change p.toNat%1 = 0;exact Nat.mod_one _) hm,Memory.load_byte]
  change interp B img o (.done (c.wr 14 (BitVec.ofNat 32 (ram p).toNat) (c.pc+4#32))) ram 0 [] = _
  rw [hb,hp];rfl

end E5R.Thermostat.TrimRightStep
namespace E5R.Thermostat.TrimRightStep
theorem trim_sub_step_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (b : BitVec 8)
    (hp : c.pc = 0x8000211e#32) (h16 : c.get 14 = BitVec.ofNat 32 b.toNat) :
    Quiet.Step B img ⟨c,ram⟩ ⟨c.wr 14 (BitVec.ofNat 32 b.toNat+0xfffffff7#32) 0x80002120#32,ram⟩ := by
  refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact tr2147492126) fun o => ?_
  rw [exec_opimm,h16,hp];rfl

end E5R.Thermostat.TrimRightStep
namespace E5R.Thermostat.TrimRightStep
theorem trim_range_step_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (b : BitVec 8)
    (hp : c.pc = 0x80002120#32) (h16 : c.get 14 = BitVec.ofNat 32 b.toNat+0xfffffff7#32)
    (h12 : c.get 12 = 23#32) (hb : 9 ≤ b.toNat ∧ b.toNat ≤ 32) :
    Quiet.Step B img ⟨c,ram⟩ ⟨c.goto 0x80002124#32,ram⟩ := by
  refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact tr2147492128) fun o => ?_
  rw [exec_branch,h16,h12,TrimMath.range]
  have he : ¬(b.toNat < 9 ∨ 32 < b.toNat) := by omega
  simp only [decide_eq_false he,Bool.false_eq_true,ite_false]
  rw [hp];rfl

end E5R.Thermostat.TrimRightStep
namespace E5R.Thermostat.TrimRightStep
theorem mask_any_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (b : BitVec 8)
    (hp : c.pc = 0x80002128#32) (h16 : c.get 14 = TrimMath.shifted b)
    (hwhite : 9 ≤ b.toNat ∧ b.toNat ≤ 32) :
    Quiet.Step B img ⟨c,ram⟩ ⟨c.wr 14 (if TrimMath.white b then 1#32 else 0#32) 0x8000212a#32,ram⟩ := by
  refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact tr2147492136) fun o => ?_
  rw [exec_opimm,h16]
  simp only [alu]
  rw [TrimMath.mask b hwhite,hp];rfl

end E5R.Thermostat.TrimRightStep
