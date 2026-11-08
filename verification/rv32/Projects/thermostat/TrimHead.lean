import Projects.thermostat.TrimCode
import Projects.thermostat.TrimMath
import Projects.thermostat.TrimStep
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.TrimHead
open E5R E5R.Thermostat E5R.Thermostat.TrimStep

theorem turn (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (b : BitVec 8) (n : Nat) (hn : 0 < n) (hbound : n < 2^32)
    (hp : c.pc = 0x80001f90#32) (h8 : c.get 8 = p) (h9 : c.get 9 = BitVec.ofNat 32 n)
    (h14 : c.get 14 = 23#32) (h15 : c.get 15 = 0x80001b#32)
    (hm : B.inRam p 1 = true) (hb : ram p = b) (hw : TrimMath.white b = true) :
    ∃ d, DetSteps B img 9 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if n = 1 then 0x80001fac#32 else 0x80001f90#32) ∧
      d.get 9 = BitVec.ofNat 32 (n-1) ∧ d.get 8 = p+1#32 ∧
      (∀ r : Reg, r ≠ 8 → r ≠ 9 → r ≠ 16 → d.get r = c.get r) ∧ d.sameCsr c := by
  have hwhite : 9 ≤ b.toNat ∧ b.toNat ≤ 32 := by
    have hh : b.toNat = 9 ∨ b.toNat = 10 ∨ b.toNat = 12 ∨ b.toNat = 13 ∨ b.toNat = 32 := by
      simpa only [TrimMath.white,decide_eq_true_eq] using hw
    omega
  have hsub : BitVec.ofNat 32 n+0xffffffff#32 = BitVec.ofNat 32 (n-1) := by
    have he : n = (n-1)+1 := by omega
    calc
      BitVec.ofNat 32 n+0xffffffff#32 = (BitVec.ofNat 32 (n-1)+1#32)+0xffffffff#32 := by
        exact congrArg (fun x : Word => x+0xffffffff#32) (by rw [←BitVec.ofNat_add];exact congrArg (BitVec.ofNat 32) he)
      _ = _ := by rw [BitVec.add_assoc,show 1#32+0xffffffff#32 = 0#32 by decide +kernel,BitVec.add_zero]
  have hne : taken .ne (BitVec.ofNat 32 (n-1)) (0 : Word) = decide (n ≠ 1) := by
    change decide (BitVec.ofNat 32 (n-1) ≠ (0 : Word)) = _
    have he : BitVec.ofNat 32 (n-1) = (0 : Word) ↔ n = 1 := by
      constructor
      · intro h
        have hh := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show n-1 < 2^32 by omega)] at hh
        change n-1 = 0 at hh;omega
      · intro h;subst n;rfl
    simp only [ne_eq,he]
  let c1 := c.wr 16 (BitVec.ofNat 32 b.toNat) 0x80001f94#32
  let c2 := c1.wr 16 (BitVec.ofNat 32 b.toNat+0xfffffff7#32) 0x80001f96#32
  let c3 := c2.goto 0x80001f9a#32
  let c4 := c3.wr 16 (TrimMath.shifted b) 0x80001f9e#32
  let c5 := c4.wr 16 (1#32) 0x80001fa2#32
  let c6 := c5.goto 0x80001fa6#32
  let c7 := c6.wr 9 (BitVec.ofNat 32 (n-1)) 0x80001fa8#32
  let c8 := c7.wr 8 (p+1#32) 0x80001faa#32
  let d := c8.goto (if n = 1 then 0x80001fac#32 else 0x80001f90#32)
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    exact trim_load_step B c ram p b hp h8 hm hb
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    have h0 : c1.get 16 = BitVec.ofNat 32 b.toNat := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h9,h14,h15]
    exact trim_sub_step B c1 ram b rfl h0
  have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    have h0 : c2.get 16 = BitVec.ofNat 32 b.toNat+0xfffffff7#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h14,h15]
    have h1 : c2.get 14 = 23#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h14,h15]
    exact trim_range_step B c2 ram b rfl h0 h1 hwhite
  have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    have h0 : c3.get 15 = 0x80001b#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h14,h15]
    have h1 : c3.get 16 = BitVec.ofNat 32 b.toNat+0xfffffff7#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h14,h15]
    exact trim_shift_step B c3 ram b rfl h0 h1
  have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    have h0 : c4.get 16 = TrimMath.shifted b := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h14,h15]
    exact trim_mask_step B c4 ram b rfl h0 hw hwhite
  have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    have h0 : c5.get 16 = 1#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h14,h15]
    exact trim_nonzero_step B c5 ram rfl h0
  have s6 : DetStep B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    have h0 : c6.get 9 = BitVec.ofNat 32 n := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h14,h15]
    exact trim_dec_step B c6 ram n rfl h0 hsub
  have s7 : DetStep B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    have h0 : c7.get 8 = p := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h14,h15]
    exact trim_inc_step B c7 ram p rfl h0
  have s8 : DetStep B img ⟨c8,ram⟩ ⟨d,ram⟩ := by
    have h0 : c8.get 9 = BitVec.ofNat 32 (n-1) := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h14,h15]
    exact trim_repeat_step B c8 ram n rfl h0 hne
  refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.single s8)))))))),rfl,?_,?_,?_,by rfl⟩
  · simp [d,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [d,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · intro r h1 h2 h3
    simp [d,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h1,h2,h3]
end E5R.Thermostat.TrimHead
