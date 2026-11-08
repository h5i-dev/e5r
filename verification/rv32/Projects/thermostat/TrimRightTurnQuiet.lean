-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.TrimRightTurn
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.TrimRightTurn
theorem turn_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (b : BitVec 8) (n : Nat) (hn : 0 < n) (hbound : n < 2^32)
    (hp : c.pc = 0x8000211a#32) (h11 : c.get 11 = p) (h9 : c.get 9 = BitVec.ofNat 32 n)
    (h12 : c.get 12 = 23#32) (h13 : c.get 13 = 0x80001b#32)
    (hm : B.inRam p 1 = true) (hb : ram p = b) (hw : TrimMath.white b = true) :
    ∃ d, Quiet.Steps B img 9 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if n = 1 then 0x80002134#32 else 0x8000211a#32) ∧
      d.get 9 = BitVec.ofNat 32 (n-1) ∧ d.get 11 = p+0xffffffff#32 ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 9 → r ≠ 14 → d.get r = c.get r) ∧ d.sameCsr c := by
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
  let c1 := c.wr 14 (BitVec.ofNat 32 b.toNat) 0x8000211e#32
  let c2 := c1.wr 14 (BitVec.ofNat 32 b.toNat+0xfffffff7#32) 0x80002120#32
  let c3 := c2.goto 0x80002124#32
  let c4 := c3.wr 14 (TrimMath.shifted b) 0x80002128#32
  let c5 := c4.wr 14 (1#32) 0x8000212a#32
  let c6 := c5.goto 0x8000212e#32
  let c7 := c6.wr 9 (BitVec.ofNat 32 (n-1)) 0x80002130#32
  let c8 := c7.wr 11 (p+0xffffffff#32) 0x80002132#32
  let d := c8.goto (if n = 1 then 0x80002134#32 else 0x8000211a#32)
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact tr2147492122) fun o => ?_
    rw [exec_load,h11,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .b) o
      (by change p.toNat%1 = 0;exact Nat.mod_one _) hm,Memory.load_byte]
    change interp B img o (.done (c.wr 14 (BitVec.ofNat 32 (ram p).toNat) (c.pc+4#32))) ram 0 [] = _
    rw [hb,hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000211e#32).getLsbD 0 = false;decide) tr2147492126 fun o => ?_
    have h0 : c1.get 14 = BitVec.ofNat 32 b.toNat := by simp [c1,Core.wr_get_ne,Core.wr_get,h11,h9,h12,h13]
    rw [exec_opimm,h0]
    rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002120#32).getLsbD 0 = false;decide) tr2147492128 fun o => ?_
    have h0 : c2.get 14 = BitVec.ofNat 32 b.toNat+0xfffffff7#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h11,h9,h12,h13]
    have h1 : c2.get 12 = 23#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h11,h9,h12,h13]
    rw [exec_branch,h0,h1,TrimMath.range]
    have he : ¬(b.toNat < 9 ∨ 32 < b.toNat) := by omega
    simp only [decide_eq_false he,Bool.false_eq_true,ite_false];rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002124#32).getLsbD 0 = false;decide) tr2147492132 fun o => ?_
    have h0 : c3.get 13 = 0x80001b#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h9,h12,h13]
    have h1 : c3.get 14 = BitVec.ofNat 32 b.toNat+0xfffffff7#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h9,h12,h13]
    rw [exec_op,h0,h1]
    dsimp only [c4]
    unfold TrimMath.shifted
    rfl
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002128#32).getLsbD 0 = false;decide) tr2147492136 fun o => ?_
    have h0 : c4.get 14 = TrimMath.shifted b := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h9,h12,h13]
    rw [exec_opimm,h0]
    simp only [alu]
    rw [TrimMath.mask b hwhite,hw];rfl
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000212a#32).getLsbD 0 = false;decide) tr2147492138 fun o => ?_
    have h0 : c5.get 14 = 1#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h9,h12,h13]
    rw [exec_branch,h0,Core.get_zero]
    have ht : taken .eq 1#32 (0 : Word) = false := by decide +kernel
    rw [ht];rfl
  have s6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000212e#32).getLsbD 0 = false;decide) tr2147492142 fun o => ?_
    have h0 : c6.get 9 = BitVec.ofNat 32 n := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h9,h12,h13]
    rw [exec_opimm,h0]
    simp only [alu]
    rw [hsub];rfl
  have s7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002130#32).getLsbD 0 = false;decide) tr2147492144 fun o => ?_
    have h0 : c7.get 11 = p := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h11,h9,h12,h13]
    rw [exec_opimm,h0]
    rfl
  have s8 : Quiet.Step B img ⟨c8,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002132#32).getLsbD 0 = false;decide) tr2147492146 fun o => ?_
    have h0 : c8.get 9 = BitVec.ofNat 32 (n-1) := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
    rw [exec_branch,h0,Core.get_zero,hne]
    by_cases he : n = 1
    · simp only [d,ite_eq_left he,he,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,ite_false];rfl
    · simp only [d,ite_eq_right he,he,ne_eq,not_false_eq_true,decide_true,ite_true]
      change interp B img o (jump c8 (0x80002132#32+0xffffffe8#32)) ram 0 [] = _
      rw [show 0x80002132#32+0xffffffe8#32 = 0x8000211a#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.step s6 (.step s7 (.single s8)))))))),rfl,?_,?_,?_,by rfl⟩
  · simp [d,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · simp [d,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
  · intro r h1 h2 h3
    simp [d,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h1,h2,h3]

end E5R.Thermostat.TrimRightTurn
