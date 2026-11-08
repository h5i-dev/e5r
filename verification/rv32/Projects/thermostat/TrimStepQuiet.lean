-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.TrimStep
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.TrimStep
theorem trim_shift_step_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (b : BitVec 8)
    (hp : c.pc = 0x80001f9a#32) (h15 : c.get 15 = 0x80001b#32)
    (h16 : c.get 16 = BitVec.ofNat 32 b.toNat+0xfffffff7#32) :
    Quiet.Step B img ⟨c,ram⟩ ⟨c.wr 16 (TrimMath.shifted b) 0x80001f9e#32,ram⟩ := by
  refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact tr2147491738) fun o => ?_
  rw [exec_op,h15,h16,hp]
  unfold TrimMath.shifted
  rfl

end E5R.Thermostat.TrimStep
namespace E5R.Thermostat.TrimStep
theorem trim_mask_step_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (b : BitVec 8)
    (hp : c.pc = 0x80001f9e#32)
    (h16 : c.get 16 = TrimMath.shifted b)
    (hw : TrimMath.white b = true) (hwhite : 9 ≤ b.toNat ∧ b.toNat ≤ 32) :
    Quiet.Step B img ⟨c,ram⟩ ⟨c.wr 16 1#32 0x80001fa2#32,ram⟩ := by
  refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact tr2147491742) fun o => ?_
  rw [exec_opimm,h16]
  simp only [alu]
  rw [TrimMath.mask b hwhite,hw,hp];rfl

end E5R.Thermostat.TrimStep
namespace E5R.Thermostat.TrimStep
theorem trim_load_step_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (b : BitVec 8)
    (hp : c.pc = 0x80001f90#32) (h8 : c.get 8 = p) (hm : B.inRam p 1 = true) (hb : ram p = b) :
    Quiet.Step B img ⟨c,ram⟩ ⟨c.wr 16 (BitVec.ofNat 32 b.toNat) 0x80001f94#32,ram⟩ := by
  refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact tr2147491728) fun o => ?_
  rw [exec_load,h8,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .b) o
    (by change p.toNat%1 = 0;exact Nat.mod_one _) hm,Memory.load_byte]
  change interp B img o (.done (c.wr 16 (BitVec.ofNat 32 (ram p).toNat) (c.pc+4#32))) ram 0 [] = _
  rw [hb,hp];rfl

end E5R.Thermostat.TrimStep
namespace E5R.Thermostat.TrimStep
theorem trim_sub_step_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (b : BitVec 8)
    (hp : c.pc = 0x80001f94#32) (h16 : c.get 16 = BitVec.ofNat 32 b.toNat) :
    Quiet.Step B img ⟨c,ram⟩ ⟨c.wr 16 (BitVec.ofNat 32 b.toNat+0xfffffff7#32) 0x80001f96#32,ram⟩ := by
  refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact tr2147491732) fun o => ?_
  rw [exec_opimm,h16,hp];rfl

end E5R.Thermostat.TrimStep
namespace E5R.Thermostat.TrimStep
theorem trim_range_step_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (b : BitVec 8)
    (hp : c.pc = 0x80001f96#32) (h16 : c.get 16 = BitVec.ofNat 32 b.toNat+0xfffffff7#32)
    (h14 : c.get 14 = 23#32) (hb : 9 ≤ b.toNat ∧ b.toNat ≤ 32) :
    Quiet.Step B img ⟨c,ram⟩ ⟨c.goto 0x80001f9a#32,ram⟩ := by
  refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact tr2147491734) fun o => ?_
  rw [exec_branch,h16,h14,TrimMath.range]
  have he : ¬(b.toNat < 9 ∨ 32 < b.toNat) := by omega
  simp only [decide_eq_false he,Bool.false_eq_true,ite_false]
  rw [hp];rfl

end E5R.Thermostat.TrimStep
namespace E5R.Thermostat.TrimStep
theorem trim_nonzero_step_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80001fa2#32) (h16 : c.get 16 = 1#32) :
    Quiet.Step B img ⟨c,ram⟩ ⟨c.goto 0x80001fa6#32,ram⟩ := by
  refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact tr2147491746) fun o => ?_
  rw [exec_branch,h16,Core.get_zero]
  have ht : taken .eq 1#32 (0 : Word) = false := by decide +kernel
  rw [ht,hp];rfl

end E5R.Thermostat.TrimStep
namespace E5R.Thermostat.TrimStep
theorem trim_dec_step_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (n : Nat)
    (hp : c.pc = 0x80001fa6#32) (h9 : c.get 9 = BitVec.ofNat 32 n)
    (hs : BitVec.ofNat 32 n+0xffffffff#32 = BitVec.ofNat 32 (n-1)) :
    Quiet.Step B img ⟨c,ram⟩ ⟨c.wr 9 (BitVec.ofNat 32 (n-1)) 0x80001fa8#32,ram⟩ := by
  refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact tr2147491750) fun o => ?_
  rw [exec_opimm,h9]
  simp only [alu]
  rw [hs,hp];rfl

end E5R.Thermostat.TrimStep
namespace E5R.Thermostat.TrimStep
theorem trim_inc_step_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (hp : c.pc = 0x80001fa8#32) (h8 : c.get 8 = p) :
    Quiet.Step B img ⟨c,ram⟩ ⟨c.wr 8 (p+1#32) 0x80001faa#32,ram⟩ := by
  refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact tr2147491752) fun o => ?_
  rw [exec_opimm,h8,hp];rfl

end E5R.Thermostat.TrimStep
namespace E5R.Thermostat.TrimStep
theorem trim_repeat_step_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (n : Nat)
    (hp : c.pc = 0x80001faa#32) (h9 : c.get 9 = BitVec.ofNat 32 (n-1))
    (hne : taken .ne (BitVec.ofNat 32 (n-1)) (0 : Word) = decide (n ≠ 1)) :
    Quiet.Step B img ⟨c,ram⟩ ⟨c.goto (if n = 1 then 0x80001fac#32 else 0x80001f90#32),ram⟩ := by
  refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact tr2147491754) fun o => ?_
  rw [exec_branch,h9,Core.get_zero,hne]
  by_cases he : n = 1
  · simp only [ite_eq_left he,he,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,ite_false]
    rw [hp];rfl
  · simp only [ite_eq_right he,he,ne_eq,not_false_eq_true,decide_true,ite_true]
    change interp B img o (jump c (c.pc+0xffffffe6#32)) ram 0 [] = _
    rw [hp,show 0x80001faa#32+0xffffffe6#32 = 0x80001f90#32 by decide +kernel,jump_ok _ _ (by decide)];rfl

end E5R.Thermostat.TrimStep
namespace E5R.Thermostat.TrimStep
theorem mask_any_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (b : BitVec 8)
    (hp : c.pc = 0x80001f9e#32) (h16 : c.get 16 = TrimMath.shifted b)
    (hwhite : 9 ≤ b.toNat ∧ b.toNat ≤ 32) :
    Quiet.Step B img ⟨c,ram⟩ ⟨c.wr 16 (if TrimMath.white b then 1#32 else 0#32) 0x80001fa2#32,ram⟩ := by
  refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact tr2147491742) fun o => ?_
  rw [exec_opimm,h16]
  simp only [alu]
  rw [TrimMath.mask b hwhite,hp];rfl

end E5R.Thermostat.TrimStep
