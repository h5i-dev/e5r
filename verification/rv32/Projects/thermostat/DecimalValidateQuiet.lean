-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.DecimalValidate
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.DecimalValidate
theorem turn_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word)
    (b : BitVec 8) (n : Nat) (hn : 0 < n) (hbound : n < 2^32)
    (hp : c.pc = 0x80001dd8#32) (h11 : c.get 11 = BitVec.ofNat 32 n)
    (h15 : c.get 15 = p) (h14 : c.get 14 = 10#32)
    (hm : B.inRam p 1 = true) (hb : ram p = b) (hd : DecimalSpec.digit b = true) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if n = 1 then 0x80001dea#32 else 0x80001dd8#32) ∧
      d.get 11 = BitVec.ofNat 32 (n-1) ∧ d.get 15 = p+1#32 ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 15 → r ≠ 16 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 16 (BitVec.ofNat 32 b.toNat) 0x80001ddc#32
  let c2 := c1.wr 16 (BitVec.ofNat 32 b.toNat+0xffffffd0#32) 0x80001de0#32
  let c3 := c2.goto 0x80001de4#32
  let c4 := c3.wr 11 (BitVec.ofNat 32 (n-1)) 0x80001de6#32
  let c5 := c4.wr 15 (p+1#32) 0x80001de8#32
  let d := c5.goto (if n = 1 then 0x80001dea#32 else 0x80001dd8#32)
  have hs : BitVec.ofNat 32 n+0xffffffff#32 = BitVec.ofNat 32 (n-1) := by
    have he : n = (n-1)+1 := by omega
    calc
      BitVec.ofNat 32 n+0xffffffff#32 = (BitVec.ofNat 32 (n-1)+1#32)+0xffffffff#32 := by
        exact congrArg (fun x : Word => x+0xffffffff#32) (by rw [←BitVec.ofNat_add];exact congrArg (BitVec.ofNat 32) he)
      _ = _ := by rw [BitVec.add_assoc,show 1#32+0xffffffff#32 = 0#32 by decide +kernel,BitVec.add_zero]
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact dc2147491288) fun o => ?_
    rw [exec_load,h15,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .b) o (by change p.toNat % 1 = 0;exact Nat.mod_one _) hm,Memory.load_byte]
    change interp B img o (.done (c.wr 16 (BitVec.ofNat 32 (ram p).toNat) (c.pc+4#32))) ram 0 [] = _
    rw [hb,hp]
    rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001ddc#32).getLsbD 0 = false;decide) dc2147491292 fun o => ?_
    rw [exec_opimm]
    have hv : c1.get 16 = BitVec.ofNat 32 b.toNat := by simp [c1,Core.wr_get]
    rw [hv];rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001de0#32).getLsbD 0 = false;decide) dc2147491296 fun o => ?_
    have hv : c2.get 16 = BitVec.ofNat 32 b.toNat+0xffffffd0#32 := by simp [c2,Core.wr_get]
    have ht : c2.get 14 = 10#32 := by simp [c2,c1,Core.wr_get_ne,h14]
    rw [exec_branch,hv,ht,DecimalMath.digit_guard,hd]
    rfl
  have s3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001de4#32).getLsbD 0 = false;decide) dc2147491300 fun o => ?_
    have hv : c3.get 11 = BitVec.ofNat 32 n := by simp [c3,c2,c1,Core.wr_get_ne,h11]
    rw [exec_opimm,hv]
    change interp B img o (.done (c3.wr 11 (BitVec.ofNat 32 n+0xffffffff#32) 0x80001de6#32)) ram 0 [] = _
    rw [hs];rfl
  have s4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001de6#32).getLsbD 0 = false;decide) dc2147491302 fun o => ?_
    have hv : c4.get 15 = p := by simp [c4,c3,c2,c1,Core.wr_get_ne,h15]
    rw [exec_opimm,hv];rfl
  have s5 : Quiet.Step B img ⟨c5,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001de8#32).getLsbD 0 = false;decide) dc2147491304 fun o => ?_
    have hv : c5.get 11 = BitVec.ofNat 32 (n-1) := by simp [c5,c4,Core.wr_get_ne,Core.wr_get]
    have he : taken .ne (BitVec.ofNat 32 (n-1)) (0 : Word) = decide (n ≠ 1) := by
      change decide (BitVec.ofNat 32 (n-1) ≠ 0#32) = _
      have hh : BitVec.ofNat 32 (n-1) = 0#32 ↔ n = 1 := by
        constructor
        · intro h
          have hx := congrArg BitVec.toNat h
          simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show n-1 < 2^32 by omega)] at hx
          change n-1 = 0 at hx
          omega
        · intro h;subst n;rfl
      simp only [ne_eq,hh]
    rw [exec_branch,hv,Core.get_zero,he]
    by_cases hz : n = 1
    · simp only [d,if_pos hz,hz,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,ite_false]
      rfl
    · simp only [d,if_neg hz,hz,ne_eq,not_false_eq_true,decide_true,ite_true]
      change interp B img o (jump c5 (0x80001de8#32+0xfffffff0#32)) ram 0 [] = _
      rw [show 0x80001de8#32+0xfffffff0#32 = 0x80001dd8#32 by decide +kernel,jump_ok _ _ (by decide)]
      rfl
  refine ⟨d,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.single s5))))),rfl,?_,?_,?_,by rfl⟩
  · simp [d,c5,c4,Core.wr_get_ne,Core.wr_get]
  · simp [d,c5,Core.wr_get]
  · intro r h1 h2 h3
    simp [d,c5,c4,c3,c2,c1,Core.wr_get_ne,h1,h2,h3]

end E5R.Thermostat.DecimalValidate
namespace E5R.Thermostat.DecimalValidate
theorem invalid_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (b : BitVec 8)
    (hp : c.pc = 0x80001dd8#32) (h15 : c.get 15 = p) (h14 : c.get 14 = 10#32)
    (hm : B.inRam p 1 = true) (hb : ram p = b) (hd : DecimalSpec.digit b = false) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80001dc8#32 ∧
      (∀ r : Reg, r ≠ 16 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 16 (BitVec.ofNat 32 b.toNat) 0x80001ddc#32
  let c2 := c1.wr 16 (BitVec.ofNat 32 b.toNat+0xffffffd0#32) 0x80001de0#32
  let d := c2.goto 0x80001dc8#32
  have s0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact dc2147491288) fun o => ?_
    rw [exec_load,h15,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .b) o
      (by change p.toNat%1 = 0;exact Nat.mod_one _) hm,Memory.load_byte]
    change interp B img o (.done (c.wr 16 (BitVec.ofNat 32 (ram p).toNat) (c.pc+4#32))) ram 0 [] = _
    rw [hb,hp];rfl
  have s1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001ddc#32).getLsbD 0 = false;decide) dc2147491292 fun o => ?_
    rw [exec_opimm]
    have hv : c1.get 16 = BitVec.ofNat 32 b.toNat := by simp [c1,Core.wr_get]
    rw [hv];rfl
  have s2 : Quiet.Step B img ⟨c2,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x80001de0#32).getLsbD 0 = false;decide) dc2147491296 fun o => ?_
    have hv : c2.get 16 = BitVec.ofNat 32 b.toNat+0xffffffd0#32 := by simp [c2,Core.wr_get]
    have ht : c2.get 14 = 10#32 := by simp [c2,c1,Core.wr_get_ne,h14]
    rw [exec_branch,hv,ht,DecimalMath.digit_guard,hd]
    simp only [Bool.not_false,ite_true]
    change interp B img o (jump c2 (0x80001de0#32+0xffffffe8#32)) ram 0 [] = _
    rw [show 0x80001de0#32+0xffffffe8#32 = 0x80001dc8#32 by decide +kernel,jump_ok _ _ (by decide)]
    rfl
  refine ⟨d,.step s0 (.step s1 (.single s2)),rfl,?_,by rfl⟩
  intro r hr;simp [d,c2,c1,Core.wr_get_ne,hr]

end E5R.Thermostat.DecimalValidate
namespace E5R.Thermostat.DecimalValidate
theorem loop_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8))
    (hs : Bytes.Span B ram p xs) (hn : 0 < xs.length)
    (hp : c.pc = 0x80001dd8#32) (h11 : c.get 11 = BitVec.ofNat 32 xs.length)
    (h15 : c.get 15 = p) (h14 : c.get 14 = 10#32) :
    ∃ d k, k ≤ 6*xs.length ∧ Quiet.Steps B img k ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if xs.all DecimalSpec.digit then 0x80001dea#32 else 0x80001dc8#32) ∧
      (xs.all DecimalSpec.digit = true → d.get 11 = 0#32 ∧ d.get 15 = p+BitVec.ofNat 32 xs.length) ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 15 → r ≠ 16 → d.get r = c.get r) ∧ d.sameCsr c := by
  induction xs generalizing c p with
  | nil => simp at hn
  | cons b bs ih =>
    obtain ⟨hb,hm⟩ := Bytes.head hs
    cases hd : DecimalSpec.digit b with
    | false =>
      obtain ⟨d,ht,hpc,hr,hcsr⟩ := E5R.Thermostat.DecimalValidate.invalid_quiet B c ram p b hp h15 h14 hm hb hd
      refine ⟨d,3,by simp;omega,ht,?_,?_,?_,hcsr⟩
      · simpa [List.all_cons,hd] using hpc
      · simp [List.all_cons,hd]
      · intro r h1 h2 h3;exact hr r h3
    | true =>
      obtain ⟨d,ht,hpc,hcnt,hptr,hr,hcsr⟩ := E5R.Thermostat.DecimalValidate.turn_quiet B c ram p b (bs.length+1) (by omega)
        (by simpa using hs.length) hp h11 h15 h14 hm hb hd
      cases bs with
      | nil =>
        refine ⟨d,6,by simp,ht,?_,?_,hr,hcsr⟩
        · simpa [hd] using hpc
        · intro _;exact ⟨hcnt,hptr⟩
      | cons b' bs' =>
        have hn' : 0 < (b'::bs').length := by simp
        have hp' : d.pc = 0x80001dd8#32 := by simpa using hpc
        obtain ⟨e,k,hk,he,hepc,heout,her,hecsr⟩ := ih d (p+1#32) (Bytes.tail hs) hn' hp'
          (by simpa using hcnt) hptr ((hr 14 (by decide) (by decide) (by decide)).trans h14)
        refine ⟨e,6+k,by simp only [List.length_cons] at hk ⊢;omega,ht.trans he,?_,?_,?_,hecsr.trans hcsr⟩
        · simpa [List.all_cons,hd] using hepc
        · intro ha
          have hb' : (b'::bs').all DecimalSpec.digit = true := by simpa [List.all_cons,hd] using ha
          obtain ⟨hz,hend⟩ := heout hb'
          refine ⟨hz,?_⟩
          rw [hend,BitVec.add_assoc,←BitVec.ofNat_add]
          congr 2
          simp [Nat.add_comm]
        · intro r h1 h2 h3;exact (her r h1 h2 h3).trans (hr r h1 h2 h3)

end E5R.Thermostat.DecimalValidate
