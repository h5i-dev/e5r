/-
  `Deframer::unpark_pending` on the pinned RMK image, proved against memmove's contract as an
  explicit hypothesis.

  Original e5r code, Apache-2.0.

  PROVED here, CONDITIONAL ON `CopyContract` (a hypothesis, not an axiom, not proved here):
  `unpark_from_copy : UnparkFromCopy`, i.e. `CopyContract → UnparkContract`: from every machine at
  `unpark_pending` meeting `CallEnv unparkPc parkStack` with `parked ≤ len`, a quiet run reaches
  `UnparkPost` (the parked bytes at the buffer's end moved to its front, consumed := 0,
  filled := parked).
-/
import Projects.rmk.Deframer.Park

set_option maxRecDepth 100000

namespace E5R.Rmk.Deframer.Unpark
open E5R E5R.Rmk.ParkFetch E5R.Rmk.Deframer.Tail E5R.Rmk.Deframer.Park

/-! ## To memmove's entry: 0x8001d3f2 .. 0x8001d414 -/

/-- At memmove's entry: a0 = buf, a1 = buf + (len - k), a2 = s0 = k, s1 = self, ra = 0x8001d418. -/
def ucall (c : Core) : Core :=
  let d := alu .sub (c.get 12) (c.get 13)
  (c.wr 2 (pfp c) 0x8001d3f4).goto 0x8001d3fa
    |>.wr 9 (alu .add 0 (c.get 10)) 0x8001d3fc
    |>.wr 10 d 0x8001d400
    |>.goto 0x8001d404
    |>.wr 8 (alu .add 0 (c.get 13)) 0x8001d406
    |>.wr 12 (alu .add (c.get 11) d) 0x8001d40a
    |>.wr 10 (alu .add 0 (c.get 11)) 0x8001d40c
    |>.wr 11 (alu .add 0 (alu .add (c.get 11) d)) 0x8001d40e
    |>.wr 12 (alu .add 0 (c.get 13)) 0x8001d410
    |>.wr 1 (0x8001d410 + 0x4000#32) 0x8001d414
    |>.wr 1 0x8001d418 0x80020c1e

theorem ucall_sameCsr (c) : (ucall c).sameCsr c := by
  unfold ucall
  repeat (first | exact Core.sameCsr_wr _ _ _ _ | exact Core.sameCsr_goto _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_)

theorem ucall_get1 (c) : (ucall c).get 1 = 0x8001d418 := by simp [ucall, Core.wr_get_self]
theorem ucall_get2 (c) : (ucall c).get 2 = pfp c := by simp [ucall, Core.wr_get_ne, Core.wr_get_self]
theorem ucall_get8 (c) : (ucall c).get 8 = c.get 13 := by
  simp [ucall, Core.wr_get_ne, Core.wr_get_self, alu_add]
theorem ucall_get9 (c) : (ucall c).get 9 = c.get 10 := by
  simp [ucall, Core.wr_get_ne, Core.wr_get_self, alu_add]
theorem ucall_get10 (c) : (ucall c).get 10 = c.get 11 := by
  simp [ucall, Core.wr_get_ne, Core.wr_get_self, alu_add]
theorem ucall_get11 (c) : (ucall c).get 11 = c.get 11 + (c.get 12 - c.get 13) := by
  simp [ucall, Core.wr_get_ne, Core.wr_get_self, alu_add, alu_sub]
theorem ucall_get12 (c) : (ucall c).get 12 = c.get 13 := by
  simp [ucall, Core.wr_get_ne, Core.wr_get_self, alu_add]
theorem ucall_get (c) (r : Reg) (h1 : r ≠ 1) (h2 : r ≠ 2) (h8 : r ≠ 8) (h9 : r ≠ 9) (h10 : r ≠ 10)
    (h11 : r ≠ 11) (h12 : r ≠ 12) : (ucall c).get r = c.get r := by
  simp [ucall, Core.wr_get_ne, h1, h2, h8, h9, h10, h11, h12]

theorem prerun (c : Core) (ram : Word → BitVec 8) (hpc : c.pc = 0x8001d3f2) (hq : Quiet c)
    (hsp : (c.get 2).toNat % 4 = 0)
    (hs : 0x80029bc8 + 0x10 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000)
    (hk : (c.get 13).toNat ≤ (c.get 12).toNat) :
    QRun B img 14 ⟨c, ram⟩ ⟨ucall c, psave c ram⟩ := by
  have F := pfp_FP c hsp hs
  let PS := psave c ram
  let d := alu .sub (c.get 12) (c.get 13)
  let c1 := c.wr 2 (pfp c) 0x8001d3f4
  let W1 := ramWrite ram (pfp c + 0xc#32) (c.get 1) .w
  let W2 := ramWrite W1 (pfp c + 0x8#32) (c.get 8) .w
  let u4 := (c1.goto 0x8001d3fa).wr 9 (alu .add 0 (c.get 10)) 0x8001d3fc
  let u5 := u4.wr 10 d 0x8001d400
  let u7 := (u5.goto 0x8001d404).wr 8 (alu .add 0 (c.get 13)) 0x8001d406
  let u8 := u7.wr 12 (alu .add (c.get 11) d) 0x8001d40a
  let u9 := u8.wr 10 (alu .add 0 (c.get 11)) 0x8001d40c
  let u10 := u9.wr 11 (alu .add 0 (alu .add (c.get 11) d)) 0x8001d40e
  let u11 := u10.wr 12 (alu .add 0 (c.get 13)) 0x8001d410
  let u12 := u11.wr 1 (0x8001d410 + 0x4000#32) 0x8001d414
  have q1 : Quiet c1 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) hq
  have qg1 : ∀ p, Quiet (c1.goto p) := fun p => Quiet.of_sameCsr (Core.sameCsr_goto _ _) q1
  have q4 : Quiet u4 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) (qg1 _)
  have q5 : Quiet u5 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q4
  have qg5 : ∀ p, Quiet (u5.goto p) := fun p => Quiet.of_sameCsr (Core.sameCsr_goto _ _) q5
  have q7 : Quiet u7 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) (qg5 _)
  have q8 : Quiet u8 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q7
  have q9 : Quiet u9 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q8
  have q10 : Quiet u10 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q9
  have q11 : Quiet u11 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q10
  have q12 : Quiet u12 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q11
  have g2 : ∀ p, (c1.goto p).get 2 = pfp c := fun p => by simp [c1, Core.wr_get_self]
  have gk : ∀ p (r : Reg), r ≠ 2 → (c1.goto p).get r = c.get r := fun p r h => by
    simp [c1, Core.wr_get_ne, h]
  have s0 : DetStep B img ⟨c, ram⟩ ⟨c1, ram⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f8001d3f2) fun o => ?_
    rw [exec_opimm, hpc]; rfl
  have s1 : DetStep B img ⟨c1, ram⟩ ⟨c1.goto 0x8001d3f6, W1⟩ := by
    refine detStep_of (by show (0x8001d3f4 : Word).getLsbD 0 = false; decide) f8001d3f4 fun o => ?_
    rw [exec_store]
    have e2 : c1.get 2 = pfp c := by simp [c1, Core.wr_get_self]
    have e1 : c1.get 1 = c.get 1 := by simp [c1, Core.wr_get_ne]
    rw [e2, e1, interp_store_ram (w := .w) o (F.slot_al 0xc (by decide)) (F.slot_in 0xc (by decide))]; rfl
  have s2 : DetStep B img ⟨c1.goto 0x8001d3f6, W1⟩ ⟨c1.goto 0x8001d3f8, W2⟩ := by
    refine detStep_of (by show (0x8001d3f6 : Word).getLsbD 0 = false; decide) f8001d3f6 fun o => ?_
    rw [exec_store, g2, gk _ 8 (by decide),
      interp_store_ram (w := .w) o (F.slot_al 0x8 (by decide)) (F.slot_in 0x8 (by decide))]; rfl
  have s3 : DetStep B img ⟨c1.goto 0x8001d3f8, W2⟩ ⟨c1.goto 0x8001d3fa, PS⟩ := by
    refine detStep_of (by show (0x8001d3f8 : Word).getLsbD 0 = false; decide) f8001d3f8 fun o => ?_
    rw [exec_store, g2, gk _ 9 (by decide),
      interp_store_ram (w := .w) o (F.slot_al 0x4 (by decide)) (F.slot_in 0x4 (by decide))]; rfl
  have s4 : DetStep B img ⟨c1.goto 0x8001d3fa, PS⟩ ⟨u4, PS⟩ := by
    refine detStep_of (by show (0x8001d3fa : Word).getLsbD 0 = false; decide) f8001d3fa fun o => ?_
    rw [exec_op, Core.get_zero, gk _ 10 (by decide)]; rfl
  have s5 : DetStep B img ⟨u4, PS⟩ ⟨u5, PS⟩ := by
    refine detStep_of (by show (0x8001d3fc : Word).getLsbD 0 = false; decide) f8001d3fc fun o => ?_
    rw [exec_op]
    have h12 : u4.get 12 = c.get 12 := by simp [u4, Core.wr_get_ne, gk]
    have h13 : u4.get 13 = c.get 13 := by simp [u4, Core.wr_get_ne, gk]
    rw [h12, h13]; rfl
  have s6 : DetStep B img ⟨u5, PS⟩ ⟨u5.goto 0x8001d404, PS⟩ := by
    refine detStep_of (by show (0x8001d400 : Word).getLsbD 0 = false; decide) f8001d400 fun o => ?_
    rw [exec_branch]
    have h12 : u5.get 12 = c.get 12 := by simp [u5, u4, Core.wr_get_ne, gk]
    have h13 : u5.get 13 = c.get 13 := by simp [u5, u4, Core.wr_get_ne, gk]
    have hn : (c.get 12).ult (c.get 13) = false := by simp only [BitVec.ult, decide_eq_false_iff_not]; omega
    rw [h12, h13]; simp only [taken, hn, Bool.false_eq_true, ite_false]; rfl
  have s7 : DetStep B img ⟨u5.goto 0x8001d404, PS⟩ ⟨u7, PS⟩ := by
    refine detStep_of (by show (0x8001d404 : Word).getLsbD 0 = false; decide) f8001d404 fun o => ?_
    rw [exec_op, Core.get_zero]
    have : (u5.goto 0x8001d404).get 13 = c.get 13 := by simp [u5, u4, Core.wr_get_ne, gk]
    rw [this]; rfl
  have s8 : DetStep B img ⟨u7, PS⟩ ⟨u8, PS⟩ := by
    refine detStep_of (by show (0x8001d406 : Word).getLsbD 0 = false; decide) f8001d406 fun o => ?_
    rw [exec_op]
    have h11 : u7.get 11 = c.get 11 := by simp [u7, u5, u4, Core.wr_get_ne, gk]
    have h10 : u7.get 10 = d := by simp [u7, u5, Core.wr_get_ne, Core.wr_get_self]
    rw [h11, h10]; rfl
  have s9 : DetStep B img ⟨u8, PS⟩ ⟨u9, PS⟩ := by
    refine detStep_of (by show (0x8001d40a : Word).getLsbD 0 = false; decide) f8001d40a fun o => ?_
    rw [exec_op, Core.get_zero]
    have h11 : u8.get 11 = c.get 11 := by simp [u8, u7, u5, u4, Core.wr_get_ne, gk]
    rw [h11]; rfl
  have s10 : DetStep B img ⟨u9, PS⟩ ⟨u10, PS⟩ := by
    refine detStep_of (by show (0x8001d40c : Word).getLsbD 0 = false; decide) f8001d40c fun o => ?_
    rw [exec_op, Core.get_zero]
    have h12 : u9.get 12 = alu .add (c.get 11) d := by simp [u9, u8, Core.wr_get_ne, Core.wr_get_self]
    rw [h12]; rfl
  have s11 : DetStep B img ⟨u10, PS⟩ ⟨u11, PS⟩ := by
    refine detStep_of (by show (0x8001d40e : Word).getLsbD 0 = false; decide) f8001d40e fun o => ?_
    rw [exec_op, Core.get_zero]
    have h13 : u10.get 13 = c.get 13 := by simp [u10, u9, u8, u7, u5, u4, Core.wr_get_ne, gk]
    rw [h13]; rfl
  have s12 : DetStep B img ⟨u11, PS⟩ ⟨u12, PS⟩ := by
    refine detStep_of (by show (0x8001d410 : Word).getLsbD 0 = false; decide) f8001d410 fun o => ?_
    rw [exec_auipc]; rfl
  have s13 : DetStep B img ⟨u12, PS⟩ ⟨ucall c, PS⟩ := by
    refine detStep_of (by show (0x8001d414 : Word).getLsbD 0 = false; decide) f8001d414 fun o => ?_
    rw [exec_jalr]
    have h1 : u12.get 1 = 0x8001d410 + 0x4000#32 := by simp [u12, Core.wr_get_self]
    rw [h1, show (0x8001d410 : Word) + 0x4000#32 + 0xfffff80e#32 &&& ~~~1 = 0x80020c1e by decide,
      jump_ok _ _ (by decide)]; rfl
  exact .step hq s0 (.step q1 s1 (.step (qg1 _) s2 (.step (qg1 _) s3 (.step (qg1 _) s4 (.step q4 s5
    (.step q5 s6 (.step (qg5 _) s7 (.step q7 s8 (.step q8 s9 (.step q9 s10 (.step q10 s11
    (.step q11 s12 (.single q12 s13)))))))))))))

/-! ## After the call: 0x8001d418 .. 0x8001d426 -/

def ufin (e : Core) (R : Word → BitVec 8) (f : Word) : Core :=
  ((((e.goto 0x8001d41e).wr 1 (ramRead R (f + 0xc#32) .w) 0x8001d420).wr 8 (ramRead R (f + 0x8#32) .w)
    0x8001d422).wr 9 (ramRead R (f + 0x4#32) .w) 0x8001d424).wr 2 (f + 0x10#32) 0x8001d426
    |>.goto (ramRead R (f + 0xc#32) .w)

theorem ufin_sameCsr (e R f) : (ufin e R f).sameCsr e := by
  unfold ufin
  repeat (first | exact Core.sameCsr_goto _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_)

theorem ufin_get1 (e R f) : (ufin e R f).get 1 = ramRead R (f + 0xc#32) .w := by
  simp [ufin, Core.wr_get_ne, Core.wr_get_self]
theorem ufin_get2 (e R f) : (ufin e R f).get 2 = f + 0x10#32 := by
  simp [ufin, Core.wr_get_ne, Core.wr_get_self]
theorem ufin_get8 (e R f) : (ufin e R f).get 8 = ramRead R (f + 0x8#32) .w := by
  simp [ufin, Core.wr_get_ne, Core.wr_get_self]
theorem ufin_get9 (e R f) : (ufin e R f).get 9 = ramRead R (f + 0x4#32) .w := by
  simp [ufin, Core.wr_get_ne, Core.wr_get_self]
theorem ufin_get (e R f) (r : Reg) (h1 : r ≠ 1) (h2 : r ≠ 2) (h8 : r ≠ 8) (h9 : r ≠ 9) :
    (ufin e R f).get r = e.get r := by
  simp [ufin, Core.wr_get_ne, h1, h2, h8, h9]

theorem postrun (e : Core) (M : Word → BitVec 8) (p f k : Word) (hpc : e.pc = 0x8001d418) (hq : Quiet e)
    (h9 : e.get 9 = p) (h8 : e.get 8 = k) (h2 : e.get 2 = f) (F : FP16 f)
    (hal : p.toNat % 4 = 0) (hp : B.inRam p 12 = true)
    (hra : (ramRead (tstore M p k) (f + 0xc#32) .w).getLsbD 0 = false) :
    QRun B img 7 ⟨e, M⟩ ⟨ufin e (tstore M p k) f, tstore M p k⟩ := by
  have hp' := (B_ram _ _).mp hp
  let R := tstore M p k
  have qg : ∀ t, Quiet (e.goto t) := fun t => Quiet.of_sameCsr (Core.sameCsr_goto _ _) hq
  let d4 := (e.goto 0x8001d41e).wr 1 (ramRead R (f + 0xc#32) .w) 0x8001d420
  let d5 := d4.wr 8 (ramRead R (f + 0x8#32) .w) 0x8001d422
  let d6 := d5.wr 9 (ramRead R (f + 0x4#32) .w) 0x8001d424
  let d7 := d6.wr 2 (f + 0x10#32) 0x8001d426
  have q4 : Quiet d4 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) (qg _)
  have q5 : Quiet d5 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q4
  have q6 : Quiet d6 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q5
  have q7 : Quiet d7 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q6
  have dsp : ∀ (d : Core), d = e.goto 0x8001d41e ∨ d = d4 ∨ d = d5 ∨ d = d6 → d.get 2 = f := by
    intro d hd; rcases hd with rfl | rfl | rfl | rfl <;> simp [d6, d5, d4, Core.wr_get_ne, h2]
  have s0 : DetStep B img ⟨e, M⟩ ⟨e.goto 0x8001d41c, ramWrite M p 0 .w⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f8001d418) fun o => ?_
    rw [exec_store, h9, Core.get_zero, BitVec.add_zero,
      interp_store_ram (w := .w) o hal ((B_ram _ _).mpr ⟨hp'.1, show p.toNat + 4 ≤ _ by omega⟩), hpc]; rfl
  have s1 : DetStep B img ⟨e.goto 0x8001d41c, ramWrite M p 0 .w⟩ ⟨e.goto 0x8001d41e, R⟩ := by
    refine detStep_of (by show (0x8001d41c : Word).getLsbD 0 = false; decide) f8001d41c fun o => ?_
    rw [exec_store, Core.goto_get, Core.goto_get, h9, h8,
      interp_store_ram (w := .w) o (show (p + 0x4#32).toNat % 4 = 0 by bv_omega)
        ((B_ram _ _).mpr ⟨by bv_omega, show (p + 0x4#32).toNat + 4 ≤ _ by bv_omega⟩)]; rfl
  have s2 : DetStep B img ⟨e.goto 0x8001d41e, R⟩ ⟨d4, R⟩ := by
    refine detStep_of (by show (0x8001d41e : Word).getLsbD 0 = false; decide) f8001d41e fun o => ?_
    rw [exec_load, dsp _ (.inl rfl),
      interp_load_ram (w := .w) o (F.slot_al 0xc (by decide)) (F.slot_in 0xc (by decide))]; rfl
  have s3 : DetStep B img ⟨d4, R⟩ ⟨d5, R⟩ := by
    refine detStep_of (by show (0x8001d420 : Word).getLsbD 0 = false; decide) f8001d420 fun o => ?_
    rw [exec_load, dsp d4 (.inr (.inl rfl)),
      interp_load_ram (w := .w) o (F.slot_al 0x8 (by decide)) (F.slot_in 0x8 (by decide))]; rfl
  have s4 : DetStep B img ⟨d5, R⟩ ⟨d6, R⟩ := by
    refine detStep_of (by show (0x8001d422 : Word).getLsbD 0 = false; decide) f8001d422 fun o => ?_
    rw [exec_load, dsp d5 (.inr (.inr (.inl rfl))),
      interp_load_ram (w := .w) o (F.slot_al 0x4 (by decide)) (F.slot_in 0x4 (by decide))]; rfl
  have s5 : DetStep B img ⟨d6, R⟩ ⟨d7, R⟩ := by
    refine detStep_of (by show (0x8001d424 : Word).getLsbD 0 = false; decide) f8001d424 fun o => ?_
    rw [exec_opimm, dsp d6 (.inr (.inr (.inr rfl)))]; rfl
  have s6 : DetStep B img ⟨d7, R⟩ ⟨ufin e R f, R⟩ := by
    refine detStep_of (by show (0x8001d426 : Word).getLsbD 0 = false; decide) f8001d426 fun o => ?_
    rw [exec_jalr, Core.set_zero]
    have : d7.get 1 = ramRead R (f + 0xc#32) .w := by simp [d7, d6, d5, d4, Core.wr_get_ne, Core.wr_get_self]
    rw [this, BitVec.add_zero, Memmove.and_not_one _ hra, jump_ok _ _ hra]; rfl
  exact .step hq s0 (.step (qg _) s1 (.step (qg _) s2 (.step q4 s3 (.step q5 s4 (.step q6 s5
    (.single q7 s6))))))

/-- Where `moved` reads byte `j` of the front from. -/
theorem unpark_addr (buf len k : Word) (j : Nat) (hb : buf.toNat + len.toNat < 2 ^ 32)
    (hk : k.toNat ≤ len.toNat) (hj : j < k.toNat) :
    (buf + (len - k)) + ((buf + BitVec.ofNat 32 j) - buf) = buf + BitVec.ofNat 32 (len.toNat - k.toNat + j) := by
  have hlk : (len - k).toNat = len.toNat - k.toNat := sub_toNat _ _ hk
  have hs : (buf + (len - k)).toNat = buf.toNat + (len.toNat - k.toNat) := by
    rw [add_toNat' _ _ (by omega), hlk]
  have hx : (buf + BitVec.ofNat 32 j).toNat = buf.toNat + j := add_toNat _ _ (by omega)
  have hxd : ((buf + BitVec.ofNat 32 j) - buf).toNat = j := by rw [sub_toNat _ _ (by omega), hx]; omega
  apply BitVec.eq_of_toNat_eq
  rw [add_toNat' _ _ (by rw [hs, hxd]; omega), hs, hxd, add_toNat _ _ (by omega)]; omega

/-! ## `unpark_pending` -/

theorem unpark_from_copy : UnparkFromCopy := by
  intro hC m₀ E hk
  obtain ⟨c, R0⟩ := m₀
  have hpc : c.pc = 0x8001d3f2 := E.pc
  have hst := stack_nat (c.get 2) parkStack E.stack
  have hfr : parkStack = 0x40 := rfl
  rw [hfr] at hst
  have hs : 0x80029bc8 + 0x10 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000 := ⟨by omega, hst.2⟩
  have hp := (B_ram (c.get 10) 12).mp E.self
  have hb := (B_ram (c.get 11) (c.get 12).toNat).mp E.buf
  have hlen : (c.get 12).toNat = bufLen := E.len
  have hk : (c.get 13).toNat ≤ (c.get 12).toNat := by rw [hlen]; exact hk
  have hsep : (c.get 10).toNat + 12 ≤ (c.get 2).toNat - 0x40 ∧
      (c.get 11).toNat + (c.get 12).toNat ≤ (c.get 2).toNat - 0x40 := E.stackSep
  have hsep2 : (c.get 10).toNat + 12 ≤ (c.get 11).toNat ∨
      (c.get 11).toNat + (c.get 12).toNat ≤ (c.get 10).toNat := E.sep
  have F := pfp_FP c E.spAl hs
  have hfp := pfp_toNat c (by omega)
  let R := psave c R0
  let S := c.get 11 + (c.get 12 - c.get 13)
  have hS : S.toNat = (c.get 11).toNat + ((c.get 12).toNat - (c.get 13).toNat) := by
    show (c.get 11 + (c.get 12 - c.get 13)).toNat = _
    rw [add_toNat' _ _ (by rw [sub_toNat _ _ hk]; omega), sub_toNat _ _ hk]
  have r1 := prerun c R0 hpc E.quiet E.spAl hs hk
  let K := ucall c
  have qK : Quiet K := Quiet.of_sameCsr (ucall_sameCsr c) E.quiet
  have hf16 : 0x30 ≤ (pfp c).toNat := by omega
  have env : CopyEnv ⟨K, R⟩ := by
    refine ⟨rfl, qK, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (K.get 12).toNat ≤ bufLen; rw [ucall_get12, ← hlen]; exact hk
    · show B.inRam (K.get 10) (K.get 12).toNat = true
      rw [ucall_get10, ucall_get12, B_ram]; omega
    · show B.inRam (K.get 11) (K.get 12).toNat = true
      rw [ucall_get11, ucall_get12, B_ram]
      show 0x80029bc8 ≤ S.toNat ∧ S.toNat + (c.get 13).toNat ≤ 0x81000000
      rw [hS]; omega
    · show B.inRam (K.get 2 - BitVec.ofNat 32 memmoveFrame) memmoveFrame = true
      rw [ucall_get2, B_ram, show memmoveFrame = 0x30 from rfl, sub_frame _ hf16]; omega
    · show (K.get 10).toNat + (K.get 12).toNat ≤ (K.get 2).toNat - memmoveFrame
      rw [ucall_get10, ucall_get12, ucall_get2, show memmoveFrame = 0x30 from rfl]; omega
    · show (K.get 11).toNat + (K.get 12).toNat ≤ (K.get 2).toNat - memmoveFrame
      rw [ucall_get11, ucall_get12, ucall_get2]
      show S.toNat + (c.get 13).toNat ≤ (pfp c).toNat - 0x30
      rw [hS]; omega
    · show (K.get 1).getLsbD 0 = false; rw [ucall_get1]; decide
    · show (K.get 2).toNat % 4 = 0; rw [ucall_get2]; exact F.al
  obtain ⟨kc, ⟨e, M⟩, rc2, P⟩ := hC _ env
  have Pregs : ∀ r : Reg, r.val ∉ [5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31] → e.get r = K.get r :=
    P.regs
  have Pram : ∀ x, ¬ ((pfp c).toNat - 0x30 ≤ x.toNat ∧ x.toNat < (pfp c).toNat) →
      M x = Memmove.moved R (c.get 11) S (c.get 13).toNat x := by
    intro x hx
    have := P.ram x (show ¬ (((ucall c).get 2).toNat - memmoveFrame ≤ x.toNat ∧
      x.toNat < ((ucall c).get 2).toNat) by rw [ucall_get2]; exact hx)
    refine this.trans ?_
    show Memmove.moved R ((ucall c).get 10) ((ucall c).get 11) ((ucall c).get 12).toNat x = _
    rw [ucall_get10, ucall_get11, ucall_get12]
  have g8 : e.get 8 = (c.get 13) := (Pregs 8 (by decide)).trans (ucall_get8 c)
  have g9 : e.get 9 = c.get 10 := (Pregs 9 (by decide)).trans (ucall_get9 c)
  have g2 : e.get 2 = pfp c := (Pregs 2 (by decide)).trans (ucall_get2 c)
  have epc : e.pc = 0x8001d418 := P.pc.trans (ucall_get1 c)
  have qe : Quiet e := Quiet.of_sameCsr P.csr qK
  have keep : ∀ x : Word, (x.toNat < (c.get 10).toNat ∨ (c.get 10).toNat + 8 ≤ x.toNat) →
      ¬ ((pfp c).toNat - 0x30 ≤ x.toNat ∧ x.toNat < (pfp c).toNat) →
      ¬ ((c.get 11).toNat ≤ x.toNat ∧ x.toNat < (c.get 11).toNat + (c.get 13).toNat) → tstore M (c.get 10) (c.get 13) x = R x := by
    intro x h1 h2 h3
    rw [tstore_other M (c.get 10) (c.get 13) x (by omega) h1, Pram x h2, Memmove.moved, if_neg h3]
  have slot : ∀ j : Nat, j = 0xc ∨ j = 0x8 ∨ j = 0x4 →
      ramRead (tstore M (c.get 10) (c.get 13)) (pfp c + BitVec.ofNat 32 j) .w = ramRead R (pfp c + BitVec.ofNat 32 j) .w := by
    intro j hj
    have hj' : j + 4 ≤ 0x10 := by rcases hj with rfl | rfl | rfl <;> decide
    have ej : (pfp c + BitVec.ofNat 32 j).toNat = (pfp c).toNat + j := add_toNat _ j (by omega)
    apply rd_congr _ (by omega)
    intro x h1 h2
    exact keep x (.inr (by omega)) (by omega) (by omega)
  have hra : (ramRead (tstore M (c.get 10) (c.get 13)) (pfp c + 0xc#32) .w).getLsbD 0 = false := by
    rw [slot 0xc (by decide), psave_c c R0 hs]; exact E.ra
  have r2 := postrun e M (c.get 10) (pfp c) (c.get 13) epc qe g9 g8 g2 F E.selfAl E.self hra
  refine ⟨_, _, (r1.trans rc2).trans r2, ?_⟩
  have hcons : consumed (tstore M (c.get 10) (c.get 13)) (c.get 10) = 0 := by
    show (ramRead (tstore M (c.get 10) (c.get 13)) (c.get 10) .w).toNat = 0
    rw [tstore_consumed M _ (c.get 13) (by omega)]; rfl
  have hfill : filled (tstore M (c.get 10) (c.get 13)) (c.get 10) = (c.get 13).toNat := by
    show (ramRead (tstore M (c.get 10) (c.get 13)) (c.get 10 + 4) .w).toNat = (c.get 13).toNat
    exact congrArg BitVec.toNat (tstore_filled M (c.get 10) (c.get 13))
  let T := ufin e (tstore M (c.get 10) (c.get 13)) (pfp c)
  refine ⟨?_, ?_, ?_, ?_, hcons, hfill, ?_, ?_, ?_⟩
  · show T.pc = c.get 1
    exact (slot 0xc (by decide)).trans (psave_c c R0 hs)
  · exact (ufin_sameCsr _ _ _).trans (P.csr.trans (ucall_sameCsr c))
  · exact (ufin_get2 _ _ _).trans (pfp_add c)
  · intro r hr
    show T.get r = c.get r
    by_cases h1 : r = 1
    · subst h1; exact (ufin_get1 _ _ _).trans ((slot 0xc (by decide)).trans (psave_c c R0 hs))
    by_cases h2 : r = 2
    · subst h2; exact (ufin_get2 _ _ _).trans (pfp_add c)
    by_cases h8 : r = 8
    · subst h8; exact (ufin_get8 _ _ _).trans ((slot 0x8 (by decide)).trans (psave_8 c R0 hs))
    by_cases h9 : r = 9
    · subst h9; exact (ufin_get9 _ _ _).trans ((slot 0x4 (by decide)).trans (psave_4 c R0))
    have hcs : r.val ∉ [5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31] := fun hm =>
      hr (by simp only [callerSaved, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢; omega)
    have h10 : r ≠ 10 := fun e => hr (by subst e; decide)
    have h11 : r ≠ 11 := fun e => hr (by subst e; decide)
    have h12 : r ≠ 12 := fun e => hr (by subst e; decide)
    rw [ufin_get _ _ _ r h1 h2 h8 h9, Pregs r hcs, ucall_get c r h1 h2 h8 h9 h10 h11 h12]
  · intro j hj
    have hj : j < (c.get 13).toNat := hj
    show tstore M (c.get 10) (c.get 13) (c.get 11 + BitVec.ofNat 32 j) =
      R0 (c.get 11 + BitVec.ofNat 32 ((c.get 12).toNat - (c.get 13).toNat + j))
    have ex : (c.get 11 + BitVec.ofNat 32 j).toNat = (c.get 11).toNat + j := add_toNat _ _ (by omega)
    have hin : (c.get 11).toNat ≤ (c.get 11 + BitVec.ofNat 32 j).toNat ∧
        (c.get 11 + BitVec.ofNat 32 j).toNat < (c.get 11).toNat + (c.get 13).toNat := by rw [ex]; omega
    rw [tstore_other M (c.get 10) (c.get 13) _ (by omega) (by rw [ex]; omega), Pram _ (by rw [ex]; omega),
      Memmove.moved, if_pos hin, unpark_addr (c.get 11) (c.get 12) (c.get 13) j (by omega) hk hj]
    have ek : (c.get 11 + BitVec.ofNat 32 ((c.get 12).toNat - (c.get 13).toNat + j)).toNat =
        (c.get 11).toNat + ((c.get 12).toNat - (c.get 13).toNat + j) := add_toNat _ _ (by omega)
    have hx : (c.get 11 + BitVec.ofNat 32 ((c.get 12).toNat - (c.get 13).toNat + j)).toNat < (c.get 2).toNat - 0x10 := by
      rw [ek]; omega
    exact psave_other c R0 hs _ (.inl hx)
  · intro x hx
    show tstore M (c.get 10) (c.get 13) x = R0 x
    have h1 : ¬ ((c.get 10).toNat ≤ x.toNat ∧ x.toNat < (c.get 10).toNat + 12) := hx.1
    have h2 : ¬ ((c.get 11).toNat ≤ x.toNat ∧ x.toNat < (c.get 11).toNat + (c.get 12).toNat) := hx.2.1
    have h3 : ¬ ((c.get 2).toNat - 0x40 ≤ x.toNat ∧ x.toNat < (c.get 2).toNat) := hx.2.2
    rw [keep x (by omega) (by omega) (by omega)]
    exact psave_other c R0 hs x (by omega)
  · show (tstore M (c.get 10) (c.get 13) (c.get 10 + 8)).toNat = (R0 (c.get 10 + 8)).toNat
    have e8 : (c.get 10 + 8).toNat = (c.get 10).toNat + 8 := add_toNat _ 8 (by omega)
    rw [keep (c.get 10 + 8) (by omega) (by omega) (by omega)]
    exact congrArg BitVec.toNat (psave_other c R0 hs (c.get 10 + 8) (.inl (by omega)))

end E5R.Rmk.Deframer.Unpark
