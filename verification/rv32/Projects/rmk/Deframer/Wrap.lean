/-
  `cobs::dec::decode_in_place` (0x8001e006), the 18-instruction wrapper `next` calls, proved
  against the COBS decoder's contract as an explicit hypothesis.

  Original e5r code, Apache-2.0.

  PROVED here, CONDITIONAL ON `CobsReportContract` (a hypothesis here, discharged in
  CobsDischarge.lean by `cobs_report`;
  the decoder `decode_in_place_report` at 0x8001e02e is the COBS worker's): `wrap`: from every
  machine meeting `WrapEnv` (the calling environment `next` sets up), a quiet run reaches a machine
  meeting `WrapPost`: back at ra, ABI frame, writes confined to the data, the 8-byte result and 0x30
  stack bytes, and whenever the first result word is -1 (what `next` takes as Ok) the second is at
  most n.
-/
import Projects.rmk.Deframer.TailNoCopy
import Projects.rmk.Deframer.NextFetch

set_option maxRecDepth 100000

namespace E5R.Rmk.Deframer.Wrap
open E5R E5R.Rmk.NextFetch E5R.Rmk.Deframer.Tail

/-- The wrapper's calling environment: a0 = out (8 bytes), a1 = data, a2 = n. -/
structure WrapEnv (m : Machine) : Prop where
  pc : m.core.pc = 0x8001e006
  quiet : Quiet m.core
  n : (m.core.get 12).toNat ≤ bufLen
  data : B.inRam (m.core.get 11) (m.core.get 12).toNat = true
  out : B.inRam (m.core.get 10) 8 = true
  outAl : (m.core.get 10).toNat % 4 = 0
  stack : 0x80029bc8 + 0x30 ≤ (m.core.get 2).toNat ∧ (m.core.get 2).toNat ≤ 0x81000000
  spAl : (m.core.get 2).toNat % 4 = 0
  sepD : (m.core.get 11).toNat + (m.core.get 12).toNat ≤ (m.core.get 2).toNat - 0x30 ∨
    (m.core.get 2).toNat ≤ (m.core.get 11).toNat
  sepO : (m.core.get 10).toNat + 8 ≤ (m.core.get 2).toNat - 0x30 ∨ (m.core.get 2).toNat ≤ (m.core.get 10).toNat
  sepDO : (m.core.get 11).toNat + (m.core.get 12).toNat ≤ (m.core.get 10).toNat ∨
    (m.core.get 10).toNat + 8 ≤ (m.core.get 11).toNat
  ra : (m.core.get 1).getLsbD 0 = false

structure WrapPost (m₀ m : Machine) : Prop where
  pc : m.core.pc = m₀.core.get 1
  regs : ∀ r : Reg, r.val ∉ callerSaved → m.core.get r = m₀.core.get r
  csr : m.core.sameCsr m₀.core
  ram : ∀ x : Word, ¬ ((m₀.core.get 11).toNat ≤ x.toNat ∧ x.toNat < (m₀.core.get 11).toNat + (m₀.core.get 12).toNat) →
    ¬ ((m₀.core.get 10).toNat ≤ x.toNat ∧ x.toNat < (m₀.core.get 10).toNat + 8) →
    ¬ ((m₀.core.get 2).toNat - 0x30 ≤ x.toNat ∧ x.toNat < (m₀.core.get 2).toNat) → m.ram x = m₀.ram x
  ok : ramRead m.ram (m₀.core.get 10) .w = 0xffffffff#32 →
    (ramRead m.ram (m₀.core.get 10 + 0x4#32) .w).toNat ≤ (m₀.core.get 12).toNat

/-! ## To the decoder: 0x8001e006 .. 0x8001e014 -/

/-- RAM after `sw ra, 0x1c(sp); sw s0, 0x18(sp)`. -/
def wsave (c : Core) (ram : Word → BitVec 8) : Word → BitVec 8 :=
  ramWrite (ramWrite ram (fp c + 0x1c#32) (c.get 1) .w) (fp c + 0x18#32) (c.get 8) .w

/-- At the decoder's entry: a0 = fp + 0xc (its 12-byte report), s0 = out, ra = 0x8001e018. -/
def wcall (c : Core) : Core :=
  (c.wr 2 (fp c) 0x8001e008).goto 0x8001e00c
    |>.wr 8 (alu .add 0 (c.get 10)) 0x8001e00e
    |>.wr 10 (alu .add (fp c) 0xc#32) 0x8001e010
    |>.wr 1 (0x8001e010 + 0x0#32) 0x8001e014
    |>.wr 1 0x8001e018 0x8001e02e

theorem wcall_sameCsr (c) : (wcall c).sameCsr c := by
  unfold wcall
  repeat (first | exact Core.sameCsr_wr _ _ _ _ | exact Core.sameCsr_goto _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_)

theorem wcall_get1 (c) : (wcall c).get 1 = 0x8001e018 := by simp [wcall, Core.wr_get_self]
theorem wcall_get2 (c) : (wcall c).get 2 = fp c := by simp [wcall, Core.wr_get_ne, Core.wr_get_self]
theorem wcall_get8 (c) : (wcall c).get 8 = c.get 10 := by
  simp [wcall, Core.wr_get_ne, Core.wr_get_self, alu_add]
theorem wcall_get10 (c) : (wcall c).get 10 = fp c + 0xc#32 := by
  simp [wcall, Core.wr_get_ne, Core.wr_get_self, alu_add]
theorem wcall_get (c) (r : Reg) (h1 : r ≠ 1) (h2 : r ≠ 2) (h8 : r ≠ 8) (h10 : r ≠ 10) :
    (wcall c).get r = c.get r := by
  simp [wcall, Core.wr_get_ne, h1, h2, h8, h10]

theorem prerun (c : Core) (ram : Word → BitVec 8) (hpc : c.pc = 0x8001e006) (hq : Quiet c)
    (hsp : (c.get 2).toNat % 4 = 0)
    (hs : 0x80029bc8 + 0x20 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000) :
    QRun B img 7 ⟨c, ram⟩ ⟨wcall c, wsave c ram⟩ := by
  have F := fp_FP c hsp hs
  let c1 := c.wr 2 (fp c) 0x8001e008
  let W1 := ramWrite ram (fp c + 0x1c#32) (c.get 1) .w
  let c3 := (c1.goto 0x8001e00c).wr 8 (alu .add 0 (c.get 10)) 0x8001e00e
  let c4 := c3.wr 10 (alu .add (fp c) 0xc#32) 0x8001e010
  let c5 := c4.wr 1 (0x8001e010 + 0x0#32) 0x8001e014
  have q1 : Quiet c1 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) hq
  have qg : ∀ p, Quiet (c1.goto p) := fun p => Quiet.of_sameCsr (Core.sameCsr_goto _ _) q1
  have q3 : Quiet c3 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) (qg _)
  have q4 : Quiet c4 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q3
  have q5 : Quiet c5 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q4
  have g2 : ∀ p, (c1.goto p).get 2 = fp c := fun p => by simp [c1, Core.wr_get_self]
  have gk : ∀ p (r : Reg), r ≠ 2 → (c1.goto p).get r = c.get r := fun p r h => by
    simp [c1, Core.wr_get_ne, h]
  have s0 : DetStep B img ⟨c, ram⟩ ⟨c1, ram⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f8001e006) fun o => ?_
    rw [exec_opimm, hpc]; rfl
  have s1 : DetStep B img ⟨c1, ram⟩ ⟨c1.goto 0x8001e00a, W1⟩ := by
    refine detStep_of (by show (0x8001e008 : Word).getLsbD 0 = false; decide) f8001e008 fun o => ?_
    rw [exec_store]
    have e2 : c1.get 2 = fp c := by simp [c1, Core.wr_get_self]
    have e1 : c1.get 1 = c.get 1 := by simp [c1, Core.wr_get_ne]
    rw [e2, e1, interp_store_ram (w := .w) o (F.slot_al 0x1c (by decide)) (F.slot_in 0x1c (by decide))]; rfl
  have s2 : DetStep B img ⟨c1.goto 0x8001e00a, W1⟩ ⟨c1.goto 0x8001e00c, wsave c ram⟩ := by
    refine detStep_of (by show (0x8001e00a : Word).getLsbD 0 = false; decide) f8001e00a fun o => ?_
    rw [exec_store, g2, gk _ 8 (by decide),
      interp_store_ram (w := .w) o (F.slot_al 0x18 (by decide)) (F.slot_in 0x18 (by decide))]; rfl
  have s3 : DetStep B img ⟨c1.goto 0x8001e00c, wsave c ram⟩ ⟨c3, wsave c ram⟩ := by
    refine detStep_of (by show (0x8001e00c : Word).getLsbD 0 = false; decide) f8001e00c fun o => ?_
    rw [exec_op, Core.get_zero, gk _ 10 (by decide)]; rfl
  have s4 : DetStep B img ⟨c3, wsave c ram⟩ ⟨c4, wsave c ram⟩ := by
    refine detStep_of (by show (0x8001e00e : Word).getLsbD 0 = false; decide) f8001e00e fun o => ?_
    rw [exec_opimm]
    have : c3.get 2 = fp c := by simp [c3, Core.wr_get_ne, g2]
    rw [this]; rfl
  have s5 : DetStep B img ⟨c4, wsave c ram⟩ ⟨c5, wsave c ram⟩ := by
    refine detStep_of (by show (0x8001e010 : Word).getLsbD 0 = false; decide) f8001e010 fun o => ?_
    rw [exec_auipc]; rfl
  have s6 : DetStep B img ⟨c5, wsave c ram⟩ ⟨wcall c, wsave c ram⟩ := by
    refine detStep_of (by show (0x8001e014 : Word).getLsbD 0 = false; decide) f8001e014 fun o => ?_
    rw [exec_jalr]
    have h1 : c5.get 1 = 0x8001e010 + 0x0#32 := by simp [c5, Core.wr_get_self]
    rw [h1, show (0x8001e010 : Word) + 0x0#32 + 0x1e#32 &&& ~~~1 = 0x8001e02e by decide,
      jump_ok _ _ (by decide)]; rfl
  exact .step hq s0 (.step q1 s1 (.step (qg _) s2 (.step (qg _) s3 (.step q3 s4 (.step q4 s5
    (.single q5 s6))))))

/-! ## After the decoder: 0x8001e018 .. 0x8001e02c -/

/-- out[0] = (r0 - 1) | r1, out[1] = r2. -/
def wstore (M : Word → BitVec 8) (out f : Word) : Word → BitVec 8 :=
  ramWrite (ramWrite M out (alu .or (alu .add (ramRead M (f + 0xc#32) .w) 0xffffffff#32)
    (ramRead M (f + 0x10#32) .w)) .w) (out + 0x4#32) (ramRead M (f + 0x14#32) .w) .w

def wfin (e : Core) (M : Word → BitVec 8) (out f : Word) : Core :=
  let R := wstore M out f
  let r0 := ramRead M (f + 0xc#32) .w
  e.wr 10 r0 0x8001e01a
    |>.wr 11 (ramRead M (f + 0x10#32) .w) 0x8001e01c
    |>.wr 12 (ramRead M (f + 0x14#32) .w) 0x8001e01e
    |>.wr 10 (alu .add r0 0xffffffff#32) 0x8001e020
    |>.wr 10 (alu .or (alu .add r0 0xffffffff#32) (ramRead M (f + 0x10#32) .w)) 0x8001e022
    |>.goto 0x8001e026
    |>.wr 1 (ramRead R (f + 0x1c#32) .w) 0x8001e028
    |>.wr 8 (ramRead R (f + 0x18#32) .w) 0x8001e02a
    |>.wr 2 (f + 0x20#32) 0x8001e02c
    |>.goto (ramRead R (f + 0x1c#32) .w)

theorem wfin_sameCsr (e M out f) : (wfin e M out f).sameCsr e := by
  unfold wfin
  repeat (first | exact Core.sameCsr_wr _ _ _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_)

theorem wfin_get1 (e M out f) : (wfin e M out f).get 1 = ramRead (wstore M out f) (f + 0x1c#32) .w := by
  simp [wfin, Core.wr_get_ne, Core.wr_get_self]
theorem wfin_get2 (e M out f) : (wfin e M out f).get 2 = f + 0x20#32 := by
  simp [wfin, Core.wr_get_ne, Core.wr_get_self]
theorem wfin_get8 (e M out f) : (wfin e M out f).get 8 = ramRead (wstore M out f) (f + 0x18#32) .w := by
  simp [wfin, Core.wr_get_ne, Core.wr_get_self]
theorem wfin_get (e M out f) (r : Reg) (h1 : r ≠ 1) (h2 : r ≠ 2) (h8 : r ≠ 8) (h10 : r ≠ 10)
    (h11 : r ≠ 11) (h12 : r ≠ 12) : (wfin e M out f).get r = e.get r := by
  simp [wfin, Core.wr_get_ne, h1, h2, h8, h10, h11, h12]

theorem postrun (e : Core) (M : Word → BitVec 8) (out f : Word) (hpc : e.pc = 0x8001e018) (hq : Quiet e)
    (h8 : e.get 8 = out) (h2 : e.get 2 = f) (F : FP f)
    (hal : out.toNat % 4 = 0) (ho : B.inRam out 8 = true)
    (hra : (ramRead (wstore M out f) (f + 0x1c#32) .w).getLsbD 0 = false) :
    QRun B img 11 ⟨e, M⟩ ⟨wfin e M out f, wstore M out f⟩ := by
  have ho' := (B_ram _ _).mp ho
  let R := wstore M out f
  let r0 := ramRead M (f + 0xc#32) .w
  let r1 := ramRead M (f + 0x10#32) .w
  let r2 := ramRead M (f + 0x14#32) .w
  let W1 := ramWrite M out (alu .or (alu .add r0 0xffffffff#32) r1) .w
  let x1 := e.wr 10 r0 0x8001e01a
  let x2 := x1.wr 11 r1 0x8001e01c
  let x3 := x2.wr 12 r2 0x8001e01e
  let x4 := x3.wr 10 (alu .add r0 0xffffffff#32) 0x8001e020
  let x5 := x4.wr 10 (alu .or (alu .add r0 0xffffffff#32) r1) 0x8001e022
  let x8 := (x5.goto 0x8001e026).wr 1 (ramRead R (f + 0x1c#32) .w) 0x8001e028
  let x9 := x8.wr 8 (ramRead R (f + 0x18#32) .w) 0x8001e02a
  let x10 := x9.wr 2 (f + 0x20#32) 0x8001e02c
  have q1 : Quiet x1 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) hq
  have q2 : Quiet x2 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q1
  have q3 : Quiet x3 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q2
  have q4 : Quiet x4 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q3
  have q5 : Quiet x5 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q4
  have qg : ∀ p, Quiet (x5.goto p) := fun p => Quiet.of_sameCsr (Core.sameCsr_goto _ _) q5
  have q8 : Quiet x8 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) (qg _)
  have q9 : Quiet x9 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q8
  have q10 : Quiet x10 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q9
  have sp2 : ∀ d : Core, d = x1 ∨ d = x2 ∨ d = x5 ∨ d = x5.goto 0x8001e024 ∨ d = x5.goto 0x8001e026 ∨
      d = x8 ∨ d = x9 → d.get 2 = f := by
    intro d hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [x9, x8, x5, x4, x3, x2, x1, Core.wr_get_ne, h2]
  have g8 : ∀ p, (x5.goto p).get 8 = out := fun p => by simp [x5, x4, x3, x2, x1, Core.wr_get_ne, h8]
  have s0 : DetStep B img ⟨e, M⟩ ⟨x1, M⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f8001e018) fun o => ?_
    rw [exec_load, h2, interp_load_ram (w := .w) o (F.slot_al 0xc (by decide)) (F.slot_in 0xc (by decide)), hpc]
    rfl
  have s1 : DetStep B img ⟨x1, M⟩ ⟨x2, M⟩ := by
    refine detStep_of (by show (0x8001e01a : Word).getLsbD 0 = false; decide) f8001e01a fun o => ?_
    rw [exec_load, sp2 x1 (.inl rfl),
      interp_load_ram (w := .w) o (F.slot_al 0x10 (by decide)) (F.slot_in 0x10 (by decide))]; rfl
  have s2 : DetStep B img ⟨x2, M⟩ ⟨x3, M⟩ := by
    refine detStep_of (by show (0x8001e01c : Word).getLsbD 0 = false; decide) f8001e01c fun o => ?_
    rw [exec_load, sp2 x2 (.inr (.inl rfl)),
      interp_load_ram (w := .w) o (F.slot_al 0x14 (by decide)) (F.slot_in 0x14 (by decide))]; rfl
  have s3 : DetStep B img ⟨x3, M⟩ ⟨x4, M⟩ := by
    refine detStep_of (by show (0x8001e01e : Word).getLsbD 0 = false; decide) f8001e01e fun o => ?_
    rw [exec_opimm]
    have : x3.get 10 = r0 := by simp [x3, x2, x1, Core.wr_get_ne, Core.wr_get_self]
    rw [this]; rfl
  have s4 : DetStep B img ⟨x4, M⟩ ⟨x5, M⟩ := by
    refine detStep_of (by show (0x8001e020 : Word).getLsbD 0 = false; decide) f8001e020 fun o => ?_
    rw [exec_op]
    have h10 : x4.get 10 = alu .add r0 0xffffffff#32 := by simp [x4, Core.wr_get_self]
    have h11 : x4.get 11 = r1 := by simp [x4, x3, x2, Core.wr_get_ne, Core.wr_get_self]
    rw [h10, h11]; rfl
  have s5 : DetStep B img ⟨x5, M⟩ ⟨x5.goto 0x8001e024, W1⟩ := by
    refine detStep_of (by show (0x8001e022 : Word).getLsbD 0 = false; decide) f8001e022 fun o => ?_
    rw [exec_store]
    have h8' : x5.get 8 = out := by simp [x5, x4, x3, x2, x1, Core.wr_get_ne, h8]
    have h10 : x5.get 10 = alu .or (alu .add r0 0xffffffff#32) r1 := by simp [x5, Core.wr_get_self]
    rw [h8', h10, BitVec.add_zero,
      interp_store_ram (w := .w) o hal ((B_ram _ _).mpr ⟨ho'.1, show out.toNat + 4 ≤ _ by omega⟩)]; rfl
  have s6 : DetStep B img ⟨x5.goto 0x8001e024, W1⟩ ⟨x5.goto 0x8001e026, R⟩ := by
    refine detStep_of (by show (0x8001e024 : Word).getLsbD 0 = false; decide) f8001e024 fun o => ?_
    rw [exec_store, g8]
    have h12 : (x5.goto 0x8001e024).get 12 = r2 := by simp [x5, x4, x3, Core.wr_get_ne, Core.wr_get_self]
    rw [h12, interp_store_ram (w := .w) o (show (out + 0x4#32).toNat % 4 = 0 by bv_omega)
        ((B_ram _ _).mpr ⟨by bv_omega, show (out + 0x4#32).toNat + 4 ≤ _ by bv_omega⟩)]; rfl
  have s7 : DetStep B img ⟨x5.goto 0x8001e026, R⟩ ⟨x8, R⟩ := by
    refine detStep_of (by show (0x8001e026 : Word).getLsbD 0 = false; decide) f8001e026 fun o => ?_
    rw [exec_load, sp2 _ (.inr (.inr (.inr (.inr (.inl rfl))))),
      interp_load_ram (w := .w) o (F.slot_al 0x1c (by decide)) (F.slot_in 0x1c (by decide))]; rfl
  have s8 : DetStep B img ⟨x8, R⟩ ⟨x9, R⟩ := by
    refine detStep_of (by show (0x8001e028 : Word).getLsbD 0 = false; decide) f8001e028 fun o => ?_
    rw [exec_load, sp2 x8 (.inr (.inr (.inr (.inr (.inr (.inl rfl)))))),
      interp_load_ram (w := .w) o (F.slot_al 0x18 (by decide)) (F.slot_in 0x18 (by decide))]; rfl
  have s9 : DetStep B img ⟨x9, R⟩ ⟨x10, R⟩ := by
    refine detStep_of (by show (0x8001e02a : Word).getLsbD 0 = false; decide) f8001e02a fun o => ?_
    rw [exec_opimm, sp2 x9 (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))]; rfl
  have s10 : DetStep B img ⟨x10, R⟩ ⟨wfin e M out f, R⟩ := by
    refine detStep_of (by show (0x8001e02c : Word).getLsbD 0 = false; decide) f8001e02c fun o => ?_
    rw [exec_jalr, Core.set_zero]
    have : x10.get 1 = ramRead R (f + 0x1c#32) .w := by simp [x10, x9, x8, Core.wr_get_ne, Core.wr_get_self]
    rw [this, BitVec.add_zero, Memmove.and_not_one _ hra, jump_ok _ _ hra]; rfl
  exact .step hq s0 (.step q1 s1 (.step q2 s2 (.step q3 s3 (.step q4 s4 (.step q5 s5 (.step (qg _) s6
    (.step (qg _) s7 (.step q8 s8 (.step q9 s9 (.single q10 s10))))))))))

theorem wstore_other (M : Word → BitVec 8) (out f x : Word) (ho : out.toNat + 8 ≤ 2 ^ 32)
    (hx : x.toNat < out.toNat ∨ out.toNat + 8 ≤ x.toNat) : wstore M out f x = M x := by
  unfold wstore
  have e4 : (out + 0x4#32).toNat = out.toNat + 4 := add_toNat out 4 (by omega)
  rw [wr_byte_other _ _ _ _ (by omega) (by omega), wr_byte_other _ _ _ _ (by omega) (by omega)]

theorem wstore_0 (M : Word → BitVec 8) (out f : Word) (ho : out.toNat + 8 ≤ 2 ^ 32) :
    ramRead (wstore M out f) out .w =
      alu .or (alu .add (ramRead M (f + 0xc#32) .w) 0xffffffff#32) (ramRead M (f + 0x10#32) .w) := by
  unfold wstore
  have e4 : (out + 0x4#32).toNat = out.toNat + 4 := add_toNat out 4 (by omega)
  rw [rd_wr_other _ _ _ _ (by omega) (by omega) (by omega), ramRead_ramWrite_w]

theorem wstore_1 (M : Word → BitVec 8) (out f : Word) :
    ramRead (wstore M out f) (out + 0x4#32) .w = ramRead M (f + 0x14#32) .w := by
  unfold wstore; rw [ramRead_ramWrite_w]

theorem add_m1 (r : Word) : alu .add r 0xffffffff#32 = r - 1 := by rw [alu_add]; bv_omega

theorem slot_off (f : Word) : f + 0xc#32 + 4 = f + 0x10#32 := by rw [BitVec.add_assoc]; rfl
theorem slot_off8 (f : Word) : f + 0xc#32 + 8 = f + 0x14#32 := by rw [BitVec.add_assoc]; rfl

/-! ## The wrapper -/

theorem wrap (hR : CobsReportContract) (m₀ : Machine) (E : WrapEnv m₀) :
    ∃ k m, QRun B img k m₀ m ∧ WrapPost m₀ m := by
  obtain ⟨c, R0⟩ := m₀
  have hpc : c.pc = 0x8001e006 := E.pc
  have hs3 : 0x80029bc8 + 0x30 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000 := E.stack
  have hs : 0x80029bc8 + 0x20 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000 := ⟨by omega, hs3.2⟩
  have hd := (B_ram (c.get 11) (c.get 12).toNat).mp E.data
  have ho := (B_ram (c.get 10) 8).mp E.out
  have hn : (c.get 12).toNat ≤ bufLen := E.n
  have sepD : (c.get 11).toNat + (c.get 12).toNat ≤ (c.get 2).toNat - 0x30 ∨ (c.get 2).toNat ≤ (c.get 11).toNat :=
    E.sepD
  have sepO : (c.get 10).toNat + 8 ≤ (c.get 2).toNat - 0x30 ∨ (c.get 2).toNat ≤ (c.get 10).toNat := E.sepO
  have sepDO : (c.get 11).toNat + (c.get 12).toNat ≤ (c.get 10).toNat ∨ (c.get 10).toNat + 8 ≤ (c.get 11).toNat :=
    E.sepDO
  have F := fp_FP c E.spAl hs
  have hfp := fp_toNat c (by omega)
  let R := wsave c R0
  have r1 := prerun c R0 hpc E.quiet E.spAl hs
  let K := wcall c
  have qK : Quiet K := Quiet.of_sameCsr (wcall_sameCsr c) E.quiet
  have eo : (fp c + 0xc#32).toNat = (fp c).toNat + 0xc := add_toNat _ _ (by omega)
  have env : CobsEnv ⟨K, R⟩ := by
    refine ⟨rfl, qK, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show ((wcall c).get 12).toNat ≤ bufLen
      rw [wcall_get _ 12 (by decide) (by decide) (by decide) (by decide)]; exact hn
    · show B.inRam ((wcall c).get 11) ((wcall c).get 12).toNat = true
      rw [wcall_get _ 12 (by decide) (by decide) (by decide) (by decide),
        wcall_get _ 11 (by decide) (by decide) (by decide) (by decide)]; exact E.data
    · show B.inRam ((wcall c).get 10) 12 = true
      rw [wcall_get10, B_ram, eo]; omega
    · show ((wcall c).get 10).toNat % 4 = 0
      rw [wcall_get10, eo]; have := F.al; omega
    · show B.inRam ((wcall c).get 2 - BitVec.ofNat 32 cobsFrame) cobsFrame = true
      rw [wcall_get2, B_ram, show cobsFrame = 0x10 from rfl,
        BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by simp; omega))]; simp; omega
    · show ((wcall c).get 2).toNat % 4 = 0; rw [wcall_get2]; exact F.al
    · show _ ∧ _ ∧ _
      rw [wcall_get _ 12 (by decide) (by decide) (by decide) (by decide),
        wcall_get _ 11 (by decide) (by decide) (by decide) (by decide), wcall_get10, wcall_get2, eo,
        show cobsFrame = 0x10 from rfl]
      omega
    · show ((wcall c).get 1).getLsbD 0 = false; rw [wcall_get1]; decide
  obtain ⟨kc, ⟨e, M⟩, rc, P⟩ := hR _ env
  have Pregs : ∀ r : Reg, r.val ∉ callerSaved → e.get r = (wcall c).get r := P.regs
  have Pram : ∀ x : Word, ¬ ((c.get 11).toNat ≤ x.toNat ∧ x.toNat < (c.get 11).toNat + (c.get 12).toNat) →
      ¬ ((fp c).toNat + 0xc ≤ x.toNat ∧ x.toNat < (fp c).toNat + 0xc + 12) →
      ¬ ((fp c).toNat - 0x10 ≤ x.toNat ∧ x.toNat < (fp c).toNat) → M x = R x := by
    intro x h1 h2 h3
    refine P.ram x ?_ ?_ ?_
    · show ¬ (((wcall c).get 11).toNat ≤ x.toNat ∧ x.toNat < ((wcall c).get 11).toNat + ((wcall c).get 12).toNat)
      rw [wcall_get _ 12 (by decide) (by decide) (by decide) (by decide),
        wcall_get _ 11 (by decide) (by decide) (by decide) (by decide)]; exact h1
    · show ¬ (((wcall c).get 10).toNat ≤ x.toNat ∧ x.toNat < ((wcall c).get 10).toNat + 12)
      rw [wcall_get10, eo]; exact h2
    · show ¬ (((wcall c).get 2).toNat - cobsFrame ≤ x.toNat ∧ x.toNat < ((wcall c).get 2).toNat)
      rw [wcall_get2]; exact h3
  have g8 : e.get 8 = c.get 10 := (Pregs 8 (by decide)).trans (wcall_get8 c)
  have g2 : e.get 2 = fp c := (Pregs 2 (by decide)).trans (wcall_get2 c)
  have epc : e.pc = 0x8001e018 := P.pc.trans (wcall_get1 c)
  have qe : Quiet e := Quiet.of_sameCsr P.csr qK
  -- the two save slots survive the decoder and the result stores
  have slot : ∀ j : Nat, j = 0x1c ∨ j = 0x18 →
      ramRead (wstore M (c.get 10) (fp c)) (fp c + BitVec.ofNat 32 j) .w = ramRead R (fp c + BitVec.ofNat 32 j) .w := by
    intro j hj
    have hj' : 0x18 ≤ j ∧ j + 4 ≤ 0x20 := by rcases hj with rfl | rfl <;> decide
    have ej : (fp c + BitVec.ofNat 32 j).toNat = (fp c).toNat + j := add_toNat _ j (by omega)
    apply rd_congr _ (by omega)
    intro x h1 h2
    rw [wstore_other M _ _ x (by omega) (by omega)]
    exact Pram x (by omega) (by omega) (by omega)
  have ws1c : ramRead R (fp c + 0x1c#32) .w = c.get 1 := by
    show ramRead (ramWrite (ramWrite R0 (fp c + 0x1c#32) (c.get 1) .w) (fp c + 0x18#32) (c.get 8) .w)
      (fp c + 0x1c#32) .w = c.get 1
    rw [rd_wr_other _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega), ramRead_ramWrite_w]
  have ws18 : ramRead R (fp c + 0x18#32) .w = c.get 8 := by
    show ramRead (ramWrite (ramWrite R0 (fp c + 0x1c#32) (c.get 1) .w) (fp c + 0x18#32) (c.get 8) .w)
      (fp c + 0x18#32) .w = c.get 8
    rw [ramRead_ramWrite_w]
  have hra : (ramRead (wstore M (c.get 10) (fp c)) (fp c + 0x1c#32) .w).getLsbD 0 = false := by
    rw [slot 0x1c (by decide), ws1c]; exact E.ra
  have r2 := postrun e M (c.get 10) (fp c) epc qe g8 g2 F E.outAl E.out hra
  refine ⟨_, _, (r1.trans rc).trans r2, ?_⟩
  let T := wfin e M (c.get 10) (fp c)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show T.pc = c.get 1
    exact (slot 0x1c (by decide)).trans ws1c
  · intro r hr
    show T.get r = c.get r
    by_cases h1 : r = 1
    · subst h1; exact (wfin_get1 _ _ _ _).trans ((slot 0x1c (by decide)).trans ws1c)
    by_cases h2 : r = 2
    · subst h2; exact (wfin_get2 _ _ _ _).trans (fp_add c)
    by_cases h8 : r = 8
    · subst h8; exact (wfin_get8 _ _ _ _).trans ((slot 0x18 (by decide)).trans ws18)
    have h10 : r ≠ 10 := fun e => hr (by subst e; decide)
    have h11 : r ≠ 11 := fun e => hr (by subst e; decide)
    have h12 : r ≠ 12 := fun e => hr (by subst e; decide)
    rw [wfin_get _ _ _ _ r h1 h2 h8 h10 h11 h12, Pregs r hr, wcall_get c r h1 h2 h8 h10]
  · exact (wfin_sameCsr _ _ _ _).trans (P.csr.trans (wcall_sameCsr c))
  · intro x h1 h2 h3
    have h1 : ¬ ((c.get 11).toNat ≤ x.toNat ∧ x.toNat < (c.get 11).toNat + (c.get 12).toNat) := h1
    have h2 : ¬ ((c.get 10).toNat ≤ x.toNat ∧ x.toNat < (c.get 10).toNat + 8) := h2
    have h3 : ¬ ((c.get 2).toNat - 0x30 ≤ x.toNat ∧ x.toNat < (c.get 2).toNat) := h3
    show wstore M (c.get 10) (fp c) x = R0 x
    rw [wstore_other M _ _ x (by omega) (by omega), Pram x h1 (by omega) (by omega)]
    show ramWrite (ramWrite R0 (fp c + 0x1c#32) (c.get 1) .w) (fp c + 0x18#32) (c.get 8) .w x = R0 x
    have e1c : (fp c + 0x1c#32).toNat = (fp c).toNat + 0x1c := add_toNat _ _ (by omega)
    have e18 : (fp c + 0x18#32).toNat = (fp c).toNat + 0x18 := add_toNat _ _ (by omega)
    rw [wr_byte_other _ _ _ _ (by omega) (by omega), wr_byte_other _ _ _ _ (by omega) (by omega)]
  · intro hok
    show (ramRead (wstore M (c.get 10) (fp c)) (c.get 10 + 0x4#32) .w).toNat ≤ (c.get 12).toNat
    rw [wstore_1]
    have hok' := hok
    simp only at hok'
    rw [wstore_0 M _ _ (by omega), add_m1] at hok'
    have := P.ok
    simp only at this
    rw [wcall_get10, wcall_get _ 12 (by decide) (by decide) (by decide) (by decide), slot_off,
      slot_off8] at this
    exact this hok'

end E5R.Rmk.Deframer.Wrap
