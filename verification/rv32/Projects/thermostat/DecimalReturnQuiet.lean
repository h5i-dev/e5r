-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.DecimalReturn
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.DecimalReturn
theorem none_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (hp : c.pc = 0x80001dc8#32) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = c.get 1 &&& ~~~1 ∧ d.get 10 = 0#32 ∧
      (∀ r : Reg, r ≠ 10 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 0#32 0x80001dca#32
  let d := c1.goto (c.get 1 &&& ~~~1)
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact dc2147491272) fun o => ?_
    rw [exec_opimm,Core.get_zero,hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001dca#32).getLsbD 0 = false;decide) dc2147491274 fun o => ?_
    have hr : c1.get 1 = c.get 1 := by simp [c1,Core.wr_get_ne]
    rw [exec_jalr,hr,BitVec.add_zero,jump_ok _ _ (clear_bit0 _)];rfl
  refine ⟨d,.step s0 (.single s1),rfl,?_,?_,by rfl⟩
  · simp [d,c1,Core.wr_get]
  · intro r hr;simp [d,c1,Core.wr_get_ne,hr]

end E5R.Thermostat.DecimalReturn
namespace E5R.Thermostat.DecimalReturn
theorem range_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (negative : Bool) (n : Nat)
    (hn : n ≤ 99999) (hp : c.pc = 0x80001e1a#32) (hv : c.get 11 = DecimalMath.signed negative n) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = c.get 1 &&& ~~~1 ∧
      d.get 10 = (if n ≤ (if negative then 32768 else 32767) then 1#32 else 0#32) ∧
      (∀ r : Reg, r ≠ 10 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 32768#32 0x80001e1c#32
  let c2 := c1.wr 10 (32768#32+DecimalMath.signed negative n) 0x80001e1e#32
  let c3 := c2.wr 10 ((32768#32+DecimalMath.signed negative n) >>> 16) 0x80001e20#32
  let c4 := c3.wr 10 (if n ≤ (if negative then 32768 else 32767) then 1#32 else 0#32) 0x80001e24#32
  let d := c4.goto (c.get 1 &&& ~~~1)
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact dc2147491354) fun o => ?_
    change interp B img o (.done (c.wr 10 32768#32 (c.pc+2#32))) ram 0 [] = _
    rw [hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001e1c#32).getLsbD 0 = false;decide) dc2147491356 fun o => ?_
    have h10 : c1.get 10 = 32768#32 := by simp [c1,Core.wr_get]
    have h11 : c1.get 11 = DecimalMath.signed negative n := by simp [c1,Core.wr_get_ne,hv]
    rw [exec_op,h10,h11];rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001e1e#32).getLsbD 0 = false;decide) dc2147491358 fun o => ?_
    have h10 : c2.get 10 = 32768#32+DecimalMath.signed negative n := by simp [c2,Core.wr_get]
    rw [exec_opimm,h10];rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001e20#32).getLsbD 0 = false;decide) dc2147491360 fun o => ?_
    have h10 : c3.get 10 = (32768#32+DecimalMath.signed negative n) >>> 16 := by simp [c3,Core.wr_get]
    rw [exec_opimm,h10,DecimalMath.range_guard negative n hn];rfl
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001e24#32).getLsbD 0 = false;decide) dc2147491364 fun o => ?_
    have hr : c4.get 1 = c.get 1 := by simp [c4,c3,c2,c1,Core.wr_get_ne]
    rw [exec_jalr,hr,BitVec.add_zero,jump_ok _ _ (clear_bit0 _)];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.single s4)))),rfl,?_,?_,by rfl⟩
  · simp [d,c4,Core.wr_get]
  · intro r hr;simp [d,c4,c3,c2,c1,Core.wr_get_ne,hr]

end E5R.Thermostat.DecimalReturn
namespace E5R.Thermostat.DecimalReturn
theorem sign_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (b : BitVec 8) (n : Nat)
    (hn : n ≤ 99999) (hp : c.pc = 0x80001e0a#32)
    (h12 : c.get 12 = BitVec.ofNat 32 b.toNat) (h11 : c.get 11 = BitVec.ofNat 32 n) :
    ∃ d k, k ≤ 9 ∧ Quiet.Steps B img k ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = c.get 1 &&& ~~~1 ∧
      d.get 10 = (if n ≤ (if b = 45#8 then 32768 else 32767) then 1#32 else 0#32) ∧
      d.get 11 = DecimalMath.signed (decide (b = 45#8)) n ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (BitVec.ofNat 32 b.toNat) 0x80001e0e#32
  let c2 := c1.wr 12 45#32 0x80001e12#32
  let c3 := c2.goto (if b = 45#8 then 0x80001e16#32 else 0x80001e1a#32)
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact dc2147491338) fun o => ?_
    rw [exec_opimm,h12]
    simp only [alu]
    rw [DecimalMath.low_byte b.toNat b.isLt,hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001e0e#32).getLsbD 0 = false;decide) dc2147491342 fun o => ?_
    rw [exec_opimm,Core.get_zero];rfl
  have ht : taken .ne (BitVec.ofNat 32 b.toNat) 45#32 = decide (b ≠ 45#8) := by
    change decide (BitVec.ofNat 32 b.toNat ≠ 45#32) = _
    have hh : BitVec.ofNat 32 b.toNat = 45#32 ↔ b = 45#8 := by
      constructor
      · intro h
        have he := congrArg BitVec.toNat h
        change b.toNat%4294967296 = 45 at he
        apply BitVec.eq_of_toNat_eq
        change b.toNat = 45
        have := b.isLt;omega
      · intro h;subst b;rfl
    simp only [ne_eq,hh]
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001e12#32).getLsbD 0 = false;decide) dc2147491346 fun o => ?_
    have h10 : c2.get 10 = BitVec.ofNat 32 b.toNat := by simp [c2,c1,Core.wr_get_ne,Core.wr_get]
    have h12' : c2.get 12 = 45#32 := by simp [c2,Core.wr_get]
    rw [exec_branch,h10,h12',ht]
    by_cases he : b = 45#8
    · simp only [c3,he,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,ite_false,ite_true]
      rfl
    · simp only [c3,he,ne_eq,not_false_eq_true,decide_true,ite_true,ite_false]
      change interp B img o (jump c2 (0x80001e12#32+8#32)) ram 0 [] = _
      rw [show 0x80001e12#32+8#32 = 0x80001e1a#32 by decide +kernel,jump_ok _ _ (by decide)]
      rfl
  have hprefix : Quiet.Steps B img 3 ⟨c,ram⟩ ⟨c3,ram⟩ := .step s0 (.step s1 (.single s2))
  have hr : ∀ r : Reg, r ≠ 10 → r ≠ 12 → c3.get r = c.get r := by
    intro r h1 h2;simp [c3,c2,c1,Core.wr_get_ne,h1,h2]
  by_cases he : b = 45#8
  · let c4 := c3.wr 11 (0#32-BitVec.ofNat 32 n) 0x80001e1a#32
    have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
      have hpc : c3.pc = 0x80001e16#32 := by simp [c3,he]
      refine QuietDet.step_of (by rw [hpc];decide) (by rw [hpc];exact dc2147491350) fun o => ?_
      have h11' : c3.get 11 = BitVec.ofNat 32 n := (hr 11 (by decide) (by decide)).trans h11
      rw [exec_op,Core.get_zero,h11']
      change interp B img o (.done (c3.wr 11 ((0 : Word)-BitVec.ofNat 32 n) (c3.pc+4#32))) ram 0 [] = _
      rw [hpc];rfl
    obtain ⟨d,hsteps,hpc,htag,hregs,hcsr⟩ := E5R.Thermostat.DecimalReturn.range_quiet B c4 ram true n hn rfl (by simp [c4,Core.wr_get,DecimalMath.signed])
    refine ⟨d,9,by decide,?_,?_,?_,?_,?_,hcsr⟩
    · exact (hprefix.trans (.single s3)).trans hsteps
    · rw [hpc]
      simp [c4,Core.wr_get_ne,hr]
    · simpa only [he,ite_true] using htag
    · rw [hregs 11 (by decide)]
      simp [c4,Core.wr_get,DecimalMath.signed,he]
    · intro r h1 h2 h3
      rw [hregs r h1]
      simp [c4,Core.wr_get_ne,h2,hr r h1 h3]
  · obtain ⟨d,hsteps,hpc,htag,hregs,hcsr⟩ := E5R.Thermostat.DecimalReturn.range_quiet B c3 ram false n hn (by simp [c3,he])
      (by simpa [DecimalMath.signed] using (hr 11 (by decide) (by decide)).trans h11)
    refine ⟨d,8,by decide,hprefix.trans hsteps,?_,?_,?_,?_,hcsr⟩
    · rw [hpc,hr 1 (by decide) (by decide)]
    · simpa only [he,ite_false,Bool.false_eq_true] using htag
    · rw [hregs 11 (by decide),hr 11 (by decide) (by decide),h11]
      simp [DecimalMath.signed,he]
    · intro r h1 h2 h3;exact (hregs r h1).trans (hr r h1 h3)

end E5R.Thermostat.DecimalReturn
