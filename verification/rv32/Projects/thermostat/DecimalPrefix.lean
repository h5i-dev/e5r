import Projects.thermostat.DecimalCode
import Projects.thermostat.DecimalMath
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.DecimalPrefix
open E5R E5R.Thermostat

def digits (b : BitVec 8) (bs : List (BitVec 8)) := if b = 45#8 then bs else b::bs
def sign (b : BitVec 8) : Word := if b = 45#8 then 1#32 else 0#32

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (b : BitVec 8) (bs : List (BitVec 8)) (hs : Bytes.Span B ram p (b::bs))
    (hp : c.pc = 0x80001dae#32) (h10 : c.get 10 = p) (h11 : c.get 11 = BitVec.ofNat 32 (b::bs).length) :
    ∃ d, DetSteps B img 8 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if 1 ≤ (digits b bs).length ∧ (digits b bs).length ≤ 5 then 0x80001dcc#32 else 0x80001dc8#32) ∧
      d.get 11 = BitVec.ofNat 32 (digits b bs).length ∧ d.get 12 = BitVec.ofNat 32 b.toNat ∧
      d.get 13 = sign b ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨hb,hm⟩ := Bytes.head hs
  have hlen : (digits b bs).length < 2^32 := by
    have hh := hs.length
    unfold digits;split <;> simp only [List.length_cons] at hh ⊢ <;> omega
  have hsub : BitVec.ofNat 32 (b::bs).length-sign b = BitVec.ofNat 32 (digits b bs).length := by
    by_cases he : b = 45#8
    · simp only [sign,digits,he,ite_true,List.length_cons]
      rw [BitVec.ofNat_add,BitVec.add_sub_cancel]
    · simp only [sign,digits,he,ite_false,BitVec.sub_zero]
  let c1 := c.goto 0x80001db0#32
  let c2 := c1.wr 12 (BitVec.ofNat 32 b.toNat) 0x80001db4#32
  let c3 := c2.wr 13 (BitVec.ofNat 32 b.toNat+0xffffffd3#32) 0x80001db8#32
  let c4 := c3.wr 13 (sign b) 0x80001dbc#32
  let c5 := c4.wr 11 (BitVec.ofNat 32 (digits b bs).length) 0x80001dbe#32
  let c6 := c5.wr 14 (BitVec.ofNat 32 (digits b bs).length+0xfffffffa#32) 0x80001dc2#32
  let c7 := c6.wr 15 0xfffffffb#32 0x80001dc4#32
  let d := c7.goto (if 1 ≤ (digits b bs).length ∧ (digits b bs).length ≤ 5 then 0x80001dcc#32 else 0x80001dc8#32)
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact dc2147491246) fun o => ?_
    have hn : BitVec.ofNat 32 (b::bs).length ≠ (0 : Word) := by
      intro h
      have hh := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hs.length] at hh
      change (b::bs).length = 0 at hh
      simp at hh
    rw [exec_branch,h11,Core.get_zero]
    have ht : taken .eq (BitVec.ofNat 32 (b::bs).length) (0 : Word) = false := by simpa [taken] using hn
    rw [ht,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine detStep_of (by change (0x80001db0#32).getLsbD 0 = false;decide) dc2147491248 fun o => ?_
    have hv : c1.get 10 = p := h10
    rw [exec_load,hv,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .b) o
      (by change p.toNat%1 = 0;exact Nat.mod_one _) hm,Memory.load_byte]
    change interp B img o (.done (c1.wr 12 (BitVec.ofNat 32 (ram p).toNat) 0x80001db4#32)) ram 0 [] = _
    rw [hb];rfl
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine detStep_of (by change (0x80001db4#32).getLsbD 0 = false;decide) dc2147491252 fun o => ?_
    have h0 : c2.get 12 = BitVec.ofNat 32 b.toNat := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h11]
    rw [exec_opimm,h0]
    rfl
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine detStep_of (by change (0x80001db8#32).getLsbD 0 = false;decide) dc2147491256 fun o => ?_
    have h0 : c3.get 13 = BitVec.ofNat 32 b.toNat+0xffffffd3#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11]
    rw [exec_opimm,h0]
    rw [DecimalMath.sign_zero]
    rfl
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine detStep_of (by change (0x80001dbc#32).getLsbD 0 = false;decide) dc2147491260 fun o => ?_
    have h0 : c4.get 11 = BitVec.ofNat 32 (b::bs).length := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11]
    have h1 : c4.get 13 = sign b := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11]
    rw [exec_op,h0,h1]
    simp only [alu]
    rw [hsub]
    rfl
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine detStep_of (by change (0x80001dbe#32).getLsbD 0 = false;decide) dc2147491262 fun o => ?_
    have h0 : c5.get 11 = BitVec.ofNat 32 (digits b bs).length := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11]
    rw [exec_opimm,h0]
    rfl
  have s6 : DetStep B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine detStep_of (by change (0x80001dc2#32).getLsbD 0 = false;decide) dc2147491266 fun o => ?_
    rw [exec_opimm,Core.get_zero]
    rfl
  have s7 : DetStep B img ⟨c7,ram⟩ ⟨d,ram⟩ := by
    refine detStep_of (by change (0x80001dc4#32).getLsbD 0 = false;decide) dc2147491268 fun o => ?_
    have h14 : c7.get 14 = BitVec.ofNat 32 (digits b bs).length+0xfffffffa#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    have h15 : c7.get 15 = 0xfffffffb#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_branch,h14,h15,DecimalMath.length_guard _ hlen]
    by_cases he : 1 ≤ (digits b bs).length ∧ (digits b bs).length ≤ 5
    · simp only [d,ite_eq_left he,decide_eq_true he,ite_true]
      change interp B img o (jump c7 (0x80001dc4#32+8#32)) ram 0 [] = _
      rw [show 0x80001dc4#32+8#32 = 0x80001dcc#32 by decide +kernel,jump_ok _ _ (by decide)]
      rfl
    · simp only [d,ite_eq_right he,decide_eq_false he,Bool.false_eq_true,ite_false]
      rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.single s7))))))),rfl,?_,?_,?_,?_,by rfl⟩
  · simp [d,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [d,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [d,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · intro r h1 h2 h3 h4 h5
    simp [d,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h1,h2,h3,h4,h5]
end E5R.Thermostat.DecimalPrefix
