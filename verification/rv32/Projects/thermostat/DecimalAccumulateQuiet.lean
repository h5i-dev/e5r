-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.DecimalAccumulate
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.DecimalAccumulate
theorem turn_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p e : Word)
    (b : BitVec 8) (a : Nat) (again : Bool)
    (hp : c.pc = 0x80001dea#32) (h13 : c.get 13 = p) (h11 : c.get 11 = BitVec.ofNat 32 a)
    (h10 : c.get 10 = e) (hm : B.inRam p 1 = true) (hb : ram p = b)
    (hd : DecimalSpec.digit b = true) (ht : taken .ne (p+1#32) e = again) :
    ∃ d, Quiet.Steps B img 10 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if again then 0x80001dea#32 else 0x80001e0a#32) ∧
      d.get 11 = BitVec.ofNat 32 (10*a+(b.toNat-48)) ∧ d.get 13 = p+1#32 ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 13 → r ≠ 14 → r ≠ 15 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (BitVec.ofNat 32 b.toNat) 0x80001dee#32
  let c2 := c1.wr 15 (p+1#32) 0x80001df2#32
  let c3 := c2.wr 13 (BitVec.ofNat 32 a <<< 1) 0x80001df6#32
  let c4 := c3.wr 11 (BitVec.ofNat 32 a <<< 3) 0x80001df8#32
  let c5 := c4.wr 14 (BitVec.ofNat 32 b.toNat+0xffffffd0#32) 0x80001dfc#32
  let c6 := c5.wr 11 ((BitVec.ofNat 32 a <<< 3)+(BitVec.ofNat 32 a <<< 1)) 0x80001dfe#32
  let c7 := c6.wr 13 ((BitVec.ofNat 32 b.toNat+0xffffffd0#32) &&& 255#32) 0x80001e02#32
  let c8 := c7.wr 11 (((BitVec.ofNat 32 a <<< 3)+(BitVec.ofNat 32 a <<< 1))+((BitVec.ofNat 32 b.toNat+0xffffffd0#32) &&& 255#32)) 0x80001e04#32
  let c9 := c8.wr 13 (p+1#32) 0x80001e06#32
  let d := c9.goto (if again then 0x80001dea#32 else 0x80001e0a#32)
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact dc2147491306) fun o => ?_
    rw [exec_load,h13,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .b) o
      (by change p.toNat%1 = 0;exact Nat.mod_one _) hm,Memory.load_byte]
    change interp B img o (.done (c.wr 14 (BitVec.ofNat 32 (ram p).toNat) (c.pc+4#32))) ram 0 [] = _
    rw [hb,hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001dee#32).getLsbD 0 = false;decide) dc2147491310 fun o => ?_
    have h0 : c1.get 13 = p := by simp [c1,Core.wr_get_ne,Core.wr_get,h13,h11,h10]
    rw [exec_opimm,h0];rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001df2#32).getLsbD 0 = false;decide) dc2147491314 fun o => ?_
    have h0 : c2.get 11 = BitVec.ofNat 32 a := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h13,h11,h10]
    rw [exec_opimm,h0];rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001df6#32).getLsbD 0 = false;decide) dc2147491318 fun o => ?_
    have h0 : c3.get 11 = BitVec.ofNat 32 a := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h11,h10]
    rw [exec_opimm,h0];rfl
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001df8#32).getLsbD 0 = false;decide) dc2147491320 fun o => ?_
    have h0 : c4.get 14 = BitVec.ofNat 32 b.toNat := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h11,h10]
    rw [exec_opimm,h0];rfl
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001dfc#32).getLsbD 0 = false;decide) dc2147491324 fun o => ?_
    have h0 : c5.get 11 = BitVec.ofNat 32 a <<< 3 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h11,h10]
    have h1 : c5.get 13 = BitVec.ofNat 32 a <<< 1 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h11,h10]
    rw [exec_op,h0,h1];rfl
  have s6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001dfe#32).getLsbD 0 = false;decide) dc2147491326 fun o => ?_
    have h0 : c6.get 14 = BitVec.ofNat 32 b.toNat+0xffffffd0#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h11,h10]
    rw [exec_opimm,h0];rfl
  have s7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001e02#32).getLsbD 0 = false;decide) dc2147491330 fun o => ?_
    have h0 : c7.get 11 = (BitVec.ofNat 32 a <<< 3)+(BitVec.ofNat 32 a <<< 1) := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h11,h10]
    have h1 : c7.get 13 = (BitVec.ofNat 32 b.toNat+0xffffffd0#32) &&& 255#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h11,h10]
    rw [exec_op,h0,h1];rfl
  have s8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001e04#32).getLsbD 0 = false;decide) dc2147491332 fun o => ?_
    have h0 : c8.get 15 = p+1#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h11,h10]
    rw [exec_op,h0,Core.get_zero]
    simp only [alu]
    rw [show (0 : Word) = 0#32 from rfl,BitVec.zero_add]
    rfl
  have s9 : Quiet.Step B img ⟨c9,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001e06#32).getLsbD 0 = false;decide) dc2147491334 fun o => ?_
    have h15 : c9.get 15 = p+1#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10]
    have he : c9.get 10 = e := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10]
    rw [exec_branch,h15,he,ht]
    cases again with
    | false => rfl
    | true =>
      simp only [ite_true]
      change interp B img o (jump c9 (0x80001e06#32+0xffffffe4#32)) ram 0 [] = _
      rw [show 0x80001e06#32+0xffffffe4#32 = 0x80001dea#32 by decide +kernel,jump_ok _ _ (by decide)]
      rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.step s8 (.single s9))))))))),rfl,?_,?_,?_,by rfl⟩
  · simp only [d,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,Core.goto_get]
    exact DecimalMath.accumulate a b hd
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,d]
  · intro r h1 h2 h3 h4
    simp [d,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h10,h1,h2,h3,h4]

end E5R.Thermostat.DecimalAccumulate
namespace E5R.Thermostat.DecimalAccumulate
theorem loop_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8))
    (a : Nat) (hs : Bytes.Span B ram p xs) (hn : 0 < xs.length) (hd : xs.all DecimalSpec.digit = true)
    (hp : c.pc = 0x80001dea#32) (h13 : c.get 13 = p) (h11 : c.get 11 = BitVec.ofNat 32 a)
    (h10 : c.get 10 = p+BitVec.ofNat 32 xs.length) :
    ∃ d, Quiet.Steps B img (10*xs.length) ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80001e0a#32 ∧
      d.get 11 = BitVec.ofNat 32 (DecimalSpec.number xs a) ∧
      d.get 13 = p+BitVec.ofNat 32 xs.length ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 13 → r ≠ 14 → r ≠ 15 → d.get r = c.get r) ∧ d.sameCsr c := by
  induction xs generalizing c p a with
  | nil => simp at hn
  | cons b bs ih =>
    have hd' : DecimalSpec.digit b = true ∧ bs.all DecimalSpec.digit = true := by
      simpa only [List.all_cons,Bool.and_eq_true] using hd
    obtain ⟨hb,hm⟩ := Bytes.head hs
    have ht : taken .ne (p+1#32) (p+BitVec.ofNat 32 (b::bs).length) = decide (0 < bs.length) := by
      cases bs with
      | nil => simp [taken]
      | cons b' bs' =>
        have hne : p+1#32 ≠ p+BitVec.ofNat 32 (b::b'::bs').length :=
          Bytes.offset_ne p 1 _ (by decide) hs.length (by simp)
        change decide (p+1#32 ≠ p+BitVec.ofNat 32 (b::b'::bs').length) = true
        exact decide_eq_true hne
    obtain ⟨d,hturn,hpc,hacc,hptr,hr,hcsr⟩ := E5R.Thermostat.DecimalAccumulate.turn_quiet B c ram p _ b a (decide (0 < bs.length)) hp h13 h11 h10 hm hb hd'.1 ht
    cases bs with
    | nil =>
      refine ⟨d,hturn,?_,hacc,hptr,hr,hcsr⟩
      simpa using hpc
    | cons b' bs' =>
      have heq : (p+1#32)+BitVec.ofNat 32 (b'::bs').length = p+BitVec.ofNat 32 (b::b'::bs').length := by
        rw [BitVec.add_assoc,←BitVec.ofNat_add]
        congr 2
        simp [Nat.add_comm]
      obtain ⟨e,he,hepc,heacc,heptr,her,hecsr⟩ := ih d (p+1#32) (10*a+(b.toNat-48))
        (Bytes.tail hs) (by simp) hd'.2 (by simpa using hpc) hptr hacc
        (by rw [heq];exact (hr 10 (by decide) (by decide) (by decide) (by decide)).trans h10)
      refine ⟨e,?_,hepc,heacc,heptr.trans heq,?_,hecsr.trans hcsr⟩
      · have hh := hturn.trans he
        simpa only [List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_comm] using hh
      · intro r h1 h2 h3 h4;exact (her r h1 h2 h3 h4).trans (hr r h1 h2 h3 h4)

end E5R.Thermostat.DecimalAccumulate
