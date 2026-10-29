/-
  `cobs::dec::decode_in_place_report` (pinned RMK image, entry 0x8001e02e):
  calling environment, result layout, and the blocks every path shares.

  Original e5r code, Apache-2.0.

  ABI, read from the bytes (0x8001e02e..0x8001e148) and from its caller
  `cobs::dec::decode_in_place` (0x8001e006, which passes a0 = sp+0xc of its own
  frame):
    a0 = address of the 12-byte result (`Result<DecodeReport, DecodeError>`),
    a1 = buffer, a2 = length; the buffer is decoded in place.
  Frame: `addi sp,sp,-16`; s0..s3 saved at sp'+12, +8, +4, +0 (sp' = sp - 16).
  Every exit goes through 0x8001e102, which stores a word at a0 + a6 (a6 = 4 or 8)
  and the tag at a0, restores s0..s3 and returns:
    empty input        (0x8001e0f8): [a0] = 1, [a0+4] = 0
    target too small   (0x8001e0fe): [a0] = 1, [a0+4] = 2
    invalid frame      (0x8001e116): [a0] = 1, [a0+4] = 1, [a0+8] = bytes written so far
    success            (0x8001e0ee): [a0] = 0, [a0+4] = source bytes used, [a0+8] = bytes decoded
  The two calls of `core::panicking::panic_bounds_check` (0x8001e12a, 0x8001e140)
  are the decoder's panic sites.
-/
import Projects.rmk.Cobs.Fetch
import Projects.rmk.Run

set_option maxRecDepth 100000

namespace E5R.Rmk.Cobs
open E5R E5R.Rmk E5R.Rmk.CobsFetch

/-- The decoder's entry. -/
def entry : Word := 0x8001e02e
/-- `core::panicking::panic_bounds_check`, called by the decoder's two bounds checks. -/
def boundsPanic : Word := 0x8001f83a
/-- The firmware's buffer length (RYNK_BUFFER_SIZE): the contract's input bound. -/
def bufLen : Nat := 488

theorem B_ram (a : Word) (n : Nat) :
    B.inRam a n = true ↔ 0x80029bc8 ≤ a.toNat ∧ a.toNat + n ≤ 0x81000000 := by
  rw [Board.inRam_iff]; simp [QemuVirtRv32.board, QemuVirtRv32.dramEnd]

/-! ## One machine step, in three shapes -/

theorem dstep {m : Machine} {p : Word} {i len c'} (hd : fetchDecode img p = some (i, len))
    (hp : m.core.pc = p) (he : exec m.core len i = .done c')
    (hal : p.getLsbD 0 = false := by decide) :
    DetStep B img m ⟨c', m.ram⟩ :=
  detStep_of (by rw [hp]; exact hal) (by rw [hp]; exact hd) fun o => by rw [he]; rfl

theorem dstep_store {m : Machine} {p : Word} {i len wd a v c'} (hd : fetchDecode img p = some (i, len))
    (hp : m.core.pc = p)
    (he : exec m.core len i = .store wd a v false (.done c'))
    (hA : a.toNat % wd.bytes = 0) (hin : B.inRam a wd.bytes = true)
    (hal : p.getLsbD 0 = false := by decide) :
    DetStep B img m ⟨c', ramWrite m.ram a v wd⟩ :=
  detStep_of (by rw [hp]; exact hal) (by rw [hp]; exact hd) fun o => by rw [he, interp_store_ram o hA hin]; rfl

theorem dstep_load {m : Machine} {p : Word} {i len wd a k c'} (hd : fetchDecode img p = some (i, len))
    (hp : m.core.pc = p)
    (he : exec m.core len i = .load wd a false k)
    (hA : a.toNat % wd.bytes = 0) (hin : B.inRam a wd.bytes = true)
    (hk : k (ramRead m.ram a wd) = .done c')
    (hal : p.getLsbD 0 = false := by decide) :
    DetStep B img m ⟨c', m.ram⟩ :=
  detStep_of (by rw [hp]; exact hal) (by rw [hp]; exact hd) fun o => by rw [he, interp_load_ram o hA hin, hk]; rfl

/-! ## The calling environment -/

/-- The call `decode_in_place_report(a0 = out, a1 = buf, a2 = len)`: result slot,
    buffer and the 16-byte frame in model RAM and pairwise disjoint, the result
    slot and sp word-aligned, `len ≤ 488`, a quiet core, an even return address. -/
structure CobsEnv (m : Machine) : Prop where
  pc : m.core.pc = entry
  quiet : Quiet m.core
  out : B.inRam (m.core.get 10) 12 = true
  outAl : (m.core.get 10).toNat % 4 = 0
  buf : B.inRam (m.core.get 11) (m.core.get 12).toNat = true
  len : (m.core.get 12).toNat ≤ bufLen
  frame : B.inRam (m.core.get 2 - 16) 16 = true
  spAl : (m.core.get 2).toNat % 4 = 0
  outBuf : (m.core.get 10).toNat + 12 ≤ (m.core.get 11).toNat ∨
    (m.core.get 11).toNat + (m.core.get 12).toNat ≤ (m.core.get 10).toNat
  outFrame : (m.core.get 10).toNat + 12 ≤ (m.core.get 2).toNat - 16 ∨
    (m.core.get 2).toNat ≤ (m.core.get 10).toNat
  bufFrame : (m.core.get 11).toNat + (m.core.get 12).toNat ≤ (m.core.get 2).toNat - 16 ∨
    (m.core.get 2).toNat ≤ (m.core.get 11).toNat
  ra : (m.core.get 1).getLsbD 0 = false

/-- Bytes a call may write: the result slot, the buffer, the frame. -/
def Writable (m₀ : Machine) (x : Word) : Prop :=
  ((m₀.core.get 10).toNat ≤ x.toNat ∧ x.toNat < (m₀.core.get 10).toNat + 12) ∨
  ((m₀.core.get 11).toNat ≤ x.toNat ∧ x.toNat < (m₀.core.get 11).toNat + (m₀.core.get 12).toNat) ∨
  ((m₀.core.get 2).toNat - 16 ≤ x.toNat ∧ x.toNat < (m₀.core.get 2).toNat)

/-- The registers the decoder may change: a0-a7 and t0-t6 (caller-saved). -/
def clobbered : List Nat := [5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]

/-- What every return guarantees: back at ra with sp, callee-saved registers and
    CSRs as at entry, and RAM unchanged outside the result slot, buffer and frame. -/
structure Returns (m₀ m : Machine) : Prop where
  pc : m.core.pc = m₀.core.get 1
  regs : ∀ r : Reg, r.val ∉ clobbered → m.core.get r = m₀.core.get r
  csr : m.core.sameCsr m₀.core
  ram : ∀ x, ¬ Writable m₀ x → m.ram x = m₀.ram x

def word (ram : Word → BitVec 8) (a : Word) : Nat := (ramRead ram a .w).toNat

/-! ## Prologue: 0x8001e02e..0x8001e03a -/

/-- RAM after the four saves (sp' = sp - 16). -/
def saved (c : Core) (R : Word → BitVec 8) : Word → BitVec 8 :=
  let sp' := c.get 2 + 0xfffffff0#32
  ramWrite (ramWrite (ramWrite (ramWrite R (sp' + 0xc#32) (c.get 8) .w) (sp' + 0x8#32) (c.get 9) .w)
    (sp' + 0x4#32) (c.get 18) .w) (sp' + 0x0#32) (c.get 19) .w

/-- The core at the empty-input test 0x8001e03a (sp lowered, a6 = 4). -/
def pro (c : Core) : Core :=
  ((((((c.wr 2 (c.get 2 + 0xfffffff0#32) 0x8001e030).goto 0x8001e032).goto 0x8001e034).goto 0x8001e036).goto
    0x8001e038).wr 16 4 0x8001e03a)

theorem pro_sameCsr (c : Core) : (pro c).sameCsr c :=
  (Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_goto _ _).trans
    ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_goto _ _).trans (Core.sameCsr_wr _ _ _ _)))))

theorem pro_get (c : Core) (r : Reg) (h2 : r ≠ 2) (h16 : r ≠ 16) : (pro c).get r = c.get r := by
  simp [pro, Core.wr_get_ne, h2, h16]

theorem pro_sp (c : Core) : (pro c).get 2 = c.get 2 + 0xfffffff0#32 := by
  simp [pro, Core.wr_get_ne, Core.wr_get_self]

theorem pro_a6 (c : Core) : (pro c).get 16 = 4 := by
  simp [pro, Core.wr_get_self]

/-- The frame's four words: aligned, in model RAM. -/
theorem slot (sp : Word) (hs : B.inRam (sp - 16) 16 = true) (ha : sp.toNat % 4 = 0) (off : Word)
    (hk : off = 0x0#32 ∨ off = 0x4#32 ∨ off = 0x8#32 ∨ off = 0xc#32) :
    (sp + 0xfffffff0#32 + off).toNat % 4 = 0 ∧ B.inRam (sp + 0xfffffff0#32 + off) 4 = true := by
  rw [B_ram] at hs ⊢
  have : (sp - 16).toNat = sp.toNat - 16 := by bv_omega
  rcases hk with rfl | rfl | rfl | rfl <;> refine ⟨?_, ?_, ?_⟩ <;> bv_omega

theorem prologue (c : Core) (R : Word → BitVec 8) (hpc : c.pc = entry) (hq : Quiet c)
    (hs : B.inRam (c.get 2 - 16) 16 = true) (ha : (c.get 2).toNat % 4 = 0) :
    QRun B img 6 ⟨c, R⟩ ⟨pro c, saved c R⟩ := by
  obtain ⟨a12, r12⟩ := slot _ hs ha 0xc#32 (by decide)
  obtain ⟨a8, r8⟩ := slot _ hs ha 0x8#32 (by decide)
  obtain ⟨a4, r4⟩ := slot _ hs ha 0x4#32 (by decide)
  obtain ⟨a0, r0⟩ := slot _ hs ha 0x0#32 (by decide)
  let sp' := c.get 2 + 0xfffffff0#32
  let c1 := c.wr 2 sp' 0x8001e030
  let c2 := c1.goto 0x8001e032
  let c3 := c2.goto 0x8001e034
  let c4 := c3.goto 0x8001e036
  let c5 := c4.goto 0x8001e038
  have g2 : ∀ d : Core, (d = c1 ∨ d = c2 ∨ d = c3 ∨ d = c4 ∨ d = c5) → d.get 2 = sp' := by
    intro d hd; rcases hd with rfl | rfl | rfl | rfl | rfl <;> simp [c5, c4, c3, c2, c1, Core.wr_get_self]
  have gs : ∀ d : Core, (d = c1 ∨ d = c2 ∨ d = c3 ∨ d = c4 ∨ d = c5) → ∀ r : Reg, r ≠ 2 → d.get r = c.get r := by
    intro d hd r hr; rcases hd with rfl | rfl | rfl | rfl | rfl <;> simp [c5, c4, c3, c2, c1, Core.wr_get_ne, hr]
  have q1 : Quiet c1 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) hq
  let R1 := ramWrite R (sp' + 0xc#32) (c.get 8) .w
  let R2 := ramWrite R1 (sp' + 0x8#32) (c.get 9) .w
  let R3 := ramWrite R2 (sp' + 0x4#32) (c.get 18) .w
  have s0 : DetStep B img ⟨c, R⟩ ⟨c1, R⟩ :=
    dstep f8001e02e hpc (by rw [exec_opimm, hpc]; rfl)
  have s1 : DetStep B img ⟨c1, R⟩ ⟨c2, R1⟩ := by
    have := dstep_store (m := ⟨c1, R⟩) f8001e030 rfl (exec_store _ _ _ _ _ _)
      (by rw [g2 c1 (by simp)]; exact a12) (by rw [g2 c1 (by simp)]; exact r12)
    rwa [g2 c1 (by simp), gs c1 (by simp) 8 (by decide)] at this
  have s2 : DetStep B img ⟨c2, R1⟩ ⟨c3, R2⟩ := by
    have := dstep_store (m := ⟨c2, R1⟩) f8001e032 rfl (exec_store _ _ _ _ _ _)
      (by rw [g2 c2 (by simp)]; exact a8) (by rw [g2 c2 (by simp)]; exact r8)
    rwa [g2 c2 (by simp), gs c2 (by simp) 9 (by decide)] at this
  have s3 : DetStep B img ⟨c3, R2⟩ ⟨c4, R3⟩ := by
    have := dstep_store (m := ⟨c3, R2⟩) f8001e034 rfl (exec_store _ _ _ _ _ _)
      (by rw [g2 c3 (by simp)]; exact a4) (by rw [g2 c3 (by simp)]; exact r4)
    rwa [g2 c3 (by simp), gs c3 (by simp) 18 (by decide)] at this
  have s4 : DetStep B img ⟨c4, R3⟩ ⟨c5, saved c R⟩ := by
    have := dstep_store (m := ⟨c4, R3⟩) f8001e036 rfl (exec_store _ _ _ _ _ _)
      (by rw [g2 c4 (by simp)]; exact a0) (by rw [g2 c4 (by simp)]; exact r0)
    rwa [g2 c4 (by simp), gs c4 (by simp) 19 (by decide)] at this
  have s5 : DetStep B img ⟨c5, saved c R⟩ ⟨pro c, saved c R⟩ :=
    dstep f8001e038 rfl (by rw [exec_opimm]; rfl)
  have qs : ∀ d : Core, d.sameCsr c1 → Quiet d := fun d h => Quiet.of_sameCsr h q1
  exact .step hq s0 (.step q1 s1 (.step (qs _ (Core.sameCsr_goto _ _)) s2
    (.step (qs _ ((Core.sameCsr_goto _ _).trans (Core.sameCsr_goto _ _))) s3
    (.step (qs _ ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_goto _ _).trans (Core.sameCsr_goto _ _)))) s4
    (.single (qs _ ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_goto _ _).trans
      ((Core.sameCsr_goto _ _).trans (Core.sameCsr_goto _ _))))) s5)))))

/-! ## RAM frames for word writes -/

theorem ramWrite_w_out (R : Word → BitVec 8) (a v x : Word) (ha : a.toNat + 4 ≤ 2 ^ 32)
    (hx : ¬ (a.toNat ≤ x.toNat ∧ x.toNat < a.toNat + 4)) : ramWrite R a v .w x = R x :=
  ramWrite_w_other R a v x fun k hk e => hx (by subst e; constructor <;> bv_omega)

theorem ramRead_w_out (R : Word → BitVec 8) (a v b : Word) (ha : a.toNat + 4 ≤ 2 ^ 32)
    (hb : b.toNat + 4 ≤ 2 ^ 32) (h : a.toNat + 4 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat) :
    ramRead (ramWrite R a v .w) b .w = ramRead R b .w :=
  ramRead_w_congr b fun k hk => ramWrite_w_out R a v _ ha (by bv_omega)

theorem extend_w (v : Word) : extend .w true v = v := rfl

/-- An even return address survives `jalr`'s clearing of bit 0. -/
theorem clear0 (x : Word) (h : x.getLsbD 0 = false) : x &&& ~~~1 = x := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_and, BitVec.getElem_not]
  rcases i with _ | i
  · rw [← BitVec.getLsbD_eq_getElem, h]; simp
  · have : (1 : Word)[i + 1] = false := by rw [← BitVec.getLsbD_eq_getElem]; simp [BitVec.getLsbD_one]
    rw [this]; simp

/-! ## The shared exit: 0x8001e102..0x8001e114 -/

/-- RAM after the exit's two stores: the word `t2` at `a0 + a6`, the tag `a1` at `a0`. -/
def exitRam (e : Core) (R : Word → BitVec 8) : Word → BitVec 8 :=
  ramWrite (ramWrite R (e.get 16 + e.get 10 + 0x0#32) (e.get 7) .w) (e.get 10 + 0x0#32) (e.get 11) .w

/-- The core back at the caller. -/
def exitCore (e : Core) (R : Word → BitVec 8) : Core :=
  let W := exitRam e R
  let sp' := e.get 2
  ((((((e.wr 16 (e.get 16 + e.get 10) 0x8001e104).goto 0x8001e108).goto 0x8001e10a).wr 8
    (ramRead W (sp' + 0xc#32) .w) 0x8001e10c).wr 9 (ramRead W (sp' + 0x8#32) .w) 0x8001e10e).wr 18
    (ramRead W (sp' + 0x4#32) .w) 0x8001e110 |>.wr 19 (ramRead W (sp' + 0x0#32) .w) 0x8001e112
    |>.wr 2 (sp' + 0x10#32) 0x8001e114).goto (e.get 1)

theorem exit_run (e : Core) (R : Word → BitVec 8) (hpc : e.pc = 0x8001e102) (hq : Quiet e)
    (hra : (e.get 1).getLsbD 0 = false)
    (hA1 : (e.get 16 + e.get 10 + 0x0#32).toNat % 4 = 0) (hR1 : B.inRam (e.get 16 + e.get 10 + 0x0#32) 4 = true)
    (hA2 : (e.get 10 + 0x0#32).toNat % 4 = 0) (hR2 : B.inRam (e.get 10 + 0x0#32) 4 = true)
    (hs : ∀ off : Word, (off = 0x0#32 ∨ off = 0x4#32 ∨ off = 0x8#32 ∨ off = 0xc#32) →
      (e.get 2 + off).toNat % 4 = 0 ∧ B.inRam (e.get 2 + off) 4 = true) :
    QRun B img 9 ⟨e, R⟩ ⟨exitCore e R, exitRam e R⟩ := by
  let W1 := ramWrite R (e.get 16 + e.get 10 + 0x0#32) (e.get 7) .w
  let W := exitRam e R
  let sp' := e.get 2
  let e1 := e.wr 16 (e.get 16 + e.get 10) 0x8001e104
  let e2 := e1.goto 0x8001e108
  let e3 := e2.goto 0x8001e10a
  let e4 := e3.wr 8 (ramRead W (sp' + 0xc#32) .w) 0x8001e10c
  let e5 := e4.wr 9 (ramRead W (sp' + 0x8#32) .w) 0x8001e10e
  let e6 := e5.wr 18 (ramRead W (sp' + 0x4#32) .w) 0x8001e110
  let e7 := e6.wr 19 (ramRead W (sp' + 0x0#32) .w) 0x8001e112
  let e8 := e7.wr 2 (sp' + 0x10#32) 0x8001e114
  have k1 : e1.sameCsr e := Core.sameCsr_wr _ _ _ _
  have k2 : e2.sameCsr e := (Core.sameCsr_goto _ _).trans k1
  have k3 : e3.sameCsr e := (Core.sameCsr_goto _ _).trans k2
  have k4 : e4.sameCsr e := (Core.sameCsr_wr _ _ _ _).trans k3
  have k5 : e5.sameCsr e := (Core.sameCsr_wr _ _ _ _).trans k4
  have k6 : e6.sameCsr e := (Core.sameCsr_wr _ _ _ _).trans k5
  have k7 : e7.sameCsr e := (Core.sameCsr_wr _ _ _ _).trans k6
  have k8 : e8.sameCsr e := (Core.sameCsr_wr _ _ _ _).trans k7
  have q : ∀ d : Core, d.sameCsr e → Quiet d := fun d h => Quiet.of_sameCsr h hq
  have sp2 : ∀ d : Core, (d = e1 ∨ d = e2 ∨ d = e3 ∨ d = e4 ∨ d = e5 ∨ d = e6 ∨ d = e7) → d.get 2 = sp' := by
    intro d hd; rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne, sp']
  have s1 : DetStep B img ⟨e, R⟩ ⟨e1, R⟩ := dstep f8001e102 hpc (by rw [exec_op, hpc]; rfl)
  have s2 : DetStep B img ⟨e1, R⟩ ⟨e2, W1⟩ := by
    have h16 : e1.get 16 = e.get 16 + e.get 10 := by simp [e1, Core.wr_get_self]
    have h7 : e1.get 7 = e.get 7 := by simp [e1, Core.wr_get_ne]
    have := dstep_store (m := ⟨e1, R⟩) f8001e104 rfl (exec_store _ _ _ _ _ _)
      (by rw [h16]; exact hA1) (by rw [h16]; exact hR1)
    rwa [h16, h7] at this
  have s3 : DetStep B img ⟨e2, W1⟩ ⟨e3, W⟩ := by
    have h10 : e2.get 10 = e.get 10 := by simp [e2, e1, Core.wr_get_ne]
    have h11 : e2.get 11 = e.get 11 := by simp [e2, e1, Core.wr_get_ne]
    have := dstep_store (m := ⟨e2, W1⟩) f8001e108 rfl (exec_store _ _ _ _ _ _)
      (by rw [h10]; exact hA2) (by rw [h10]; exact hR2)
    rwa [h10, h11] at this
  have ld : ∀ (d d' : Core) (p : Word) (off : Word) (rd : Reg) (hd : fetchDecode img p = some (Instr.load .w true rd 2 off, 2))
      (hp : d.pc = p) (h2 : d.get 2 = sp') (ho : off = 0x0#32 ∨ off = 0x4#32 ∨ off = 0x8#32 ∨ off = 0xc#32)
      (he : d' = d.wr rd (ramRead W (sp' + off) .w) (p + 2)) (hal : p.getLsbD 0 = false),
      DetStep B img ⟨d, W⟩ ⟨d', W⟩ := by
    intro d d' p off rd hd hp h2 ho he hal
    obtain ⟨a, r⟩ := hs off ho
    exact dstep_load hd hp (exec_load _ _ _ _ _ _ _) (by rw [h2]; exact a) (by rw [h2]; exact r)
      (by rw [h2, hp, he, extend_w]) hal
  have s4 : DetStep B img ⟨e3, W⟩ ⟨e4, W⟩ := ld e3 e4 _ _ 8 f8001e10a rfl (sp2 e3 (by simp)) (by simp) rfl (by decide)
  have s5 : DetStep B img ⟨e4, W⟩ ⟨e5, W⟩ := ld e4 e5 _ _ 9 f8001e10c rfl (sp2 e4 (by simp)) (by simp) rfl (by decide)
  have s6 : DetStep B img ⟨e5, W⟩ ⟨e6, W⟩ := ld e5 e6 _ _ 18 f8001e10e rfl (sp2 e5 (by simp)) (by simp) rfl (by decide)
  have s7 : DetStep B img ⟨e6, W⟩ ⟨e7, W⟩ := ld e6 e7 _ _ 19 f8001e110 rfl (sp2 e6 (by simp)) (by simp) rfl (by decide)
  have s8 : DetStep B img ⟨e7, W⟩ ⟨e8, W⟩ :=
    dstep f8001e112 rfl (by rw [exec_opimm, sp2 e7 (by simp)]; rfl)
  have s9 : DetStep B img ⟨e8, W⟩ ⟨exitCore e R, W⟩ := by
    have h1 : e8.get 1 = e.get 1 := by simp [e8, e7, e6, e5, e4, e3, e2, e1, Core.wr_get_ne]
    refine dstep f8001e114 rfl ?_
    rw [exec_jalr, Core.set_zero, h1, BitVec.add_zero, clear0 _ hra, jump_ok _ _ hra]
    rfl
  exact .step hq s1 (.step (q _ k1) s2 (.step (q _ k2) s3 (.step (q _ k3) s4 (.step (q _ k4) s5
    (.step (q _ k5) s6 (.step (q _ k6) s7 (.step (q _ k7) s8 (.single (q _ k8) s9))))))))

/-! ## From the exit to the caller: `Returns` and the result words -/

/-- The callee-saved values the frame holds, read from RAM `S`. -/
def SlotsHold (c : Core) (S : Word → BitVec 8) : Prop :=
  ramRead S (c.get 2 + 0xfffffff0#32 + 0xc#32) .w = c.get 8 ∧
  ramRead S (c.get 2 + 0xfffffff0#32 + 0x8#32) .w = c.get 9 ∧
  ramRead S (c.get 2 + 0xfffffff0#32 + 0x4#32) .w = c.get 18 ∧
  ramRead S (c.get 2 + 0xfffffff0#32 + 0x0#32) .w = c.get 19

theorem saved_hold (c : Core) (R : Word → BitVec 8) (hs : B.inRam (c.get 2 - 16) 16 = true) :
    SlotsHold c (saved c R) := by
  rw [B_ram] at hs
  have e : (c.get 2 - 16).toNat = (c.get 2).toNat - 16 := by bv_omega
  unfold saved
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ramRead_w_out, ramRead_w_out, ramRead_w_out, ramRead_ramWrite_w] <;> bv_omega
  · rw [ramRead_w_out, ramRead_w_out, ramRead_ramWrite_w] <;> bv_omega
  · rw [ramRead_w_out, ramRead_ramWrite_w] <;> bv_omega
  · rw [ramRead_ramWrite_w]

theorem saved_out (c : Core) (R : Word → BitVec 8) (hs : B.inRam (c.get 2 - 16) 16 = true) (x : Word)
    (hx : ¬ ((c.get 2).toNat - 16 ≤ x.toNat ∧ x.toNat < (c.get 2).toNat)) : saved c R x = R x := by
  rw [B_ram] at hs
  have e : (c.get 2 - 16).toNat = (c.get 2).toNat - 16 := by bv_omega
  unfold saved
  rw [ramWrite_w_out, ramWrite_w_out, ramWrite_w_out, ramWrite_w_out] <;> bv_omega

/-- Every exit, given what the body guarantees: `S` holds the saved registers in the
    frame and equals the entry RAM outside the buffer and the frame; `e` is at
    0x8001e102 with sp, ra and a0 as the prologue left them and a6 ∈ {4, 8}. -/
theorem finish (c : Core) (R S : Word → BitVec 8) (e : Core) (h : CobsEnv ⟨c, R⟩)
    (hpc : e.pc = 0x8001e102) (hq : Quiet e) (hcs : e.sameCsr c)
    (h2 : e.get 2 = c.get 2 + 0xfffffff0#32) (h1 : e.get 1 = c.get 1) (h10 : e.get 10 = c.get 10)
    (h16 : e.get 16 = 4 ∨ e.get 16 = 8)
    (hk : ∀ r : Reg, r.val ∉ clobbered → r.val ∉ [2, 8, 9, 18, 19] → e.get r = c.get r)
    (hS : SlotsHold c S)
    (hSo : ∀ x, ¬ ((c.get 11).toNat ≤ x.toNat ∧ x.toNat < (c.get 11).toNat + (c.get 12).toNat) →
      ¬ ((c.get 2).toNat - 16 ≤ x.toNat ∧ x.toNat < (c.get 2).toNat) → S x = R x) :
    ∃ m, QRun B img 9 ⟨e, S⟩ m ∧ Returns ⟨c, R⟩ m ∧
      ramRead m.ram (c.get 10) .w = e.get 11 ∧
      ramRead m.ram (c.get 10 + e.get 16) .w = e.get 7 ∧
      (e.get 16 = 4 → ramRead m.ram (c.get 10 + 8#32) .w = ramRead S (c.get 10 + 8#32) .w) := by
  have hf := h.frame; have ho := h.out; have hoa := h.outAl; have hsa := h.spAl
  have hof := h.outFrame
  rw [B_ram] at hf ho
  have esp : (c.get 2 - 16).toNat = (c.get 2).toNat - 16 := by bv_omega
  have hoff : (e.get 16).toNat = 4 ∨ (e.get 16).toNat = 8 := by rcases h16 with e | e <;> simp [e]
  have run := exit_run e S hpc hq (by rw [h1]; exact h.ra)
    (by rw [h10]; bv_omega) (by rw [h10, B_ram]; constructor <;> bv_omega)
    (by rw [h10]; bv_omega) (by rw [h10, B_ram]; constructor <;> bv_omega)
    (fun off hoff' => by rw [h2]; exact slot _ h.frame hsa off hoff')
  refine ⟨_, run, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp [exitCore, h1]
  · intro r hr
    have W : ∀ b : Word, b.toNat + 4 ≤ 2 ^ 32 →
        (b.toNat + 4 ≤ (c.get 10).toNat ∨ (c.get 10).toNat + 12 ≤ b.toNat) →
        ramRead (exitRam e S) b .w = ramRead S b .w := by
      intro b hb hb'
      unfold exitRam; rw [h10]
      rw [ramRead_w_out, ramRead_w_out] <;> bv_omega
    obtain ⟨s8, s9, s18, s19⟩ := hS
    have sp' : e.get 2 = c.get 2 + 0xfffffff0#32 := h2
    by_cases r2 : r = 2
    · subst r2; simp [exitCore, Core.wr_get_self, h2]; bv_omega
    by_cases r8 : r = 8
    · subst r8; simp only [exitCore, Core.goto_get, Core.wr_get_ne _ _ _ _ _ (show (8 : Reg) ≠ 2 by decide),
        Core.wr_get_ne _ _ _ _ _ (show (8 : Reg) ≠ 19 by decide), Core.wr_get_ne _ _ _ _ _ (show (8 : Reg) ≠ 18 by decide),
        Core.wr_get_ne _ _ _ _ _ (show (8 : Reg) ≠ 9 by decide), Core.wr_get_self _ (8 : Reg) _ _ (by decide)]
      rw [sp', W _ (by bv_omega) (by bv_omega), s8]
    by_cases r9 : r = 9
    · subst r9; simp only [exitCore, Core.goto_get, Core.wr_get_ne _ _ _ _ _ (show (9 : Reg) ≠ 2 by decide),
        Core.wr_get_ne _ _ _ _ _ (show (9 : Reg) ≠ 19 by decide), Core.wr_get_ne _ _ _ _ _ (show (9 : Reg) ≠ 18 by decide),
        Core.wr_get_self _ (9 : Reg) _ _ (by decide)]
      rw [sp', W _ (by bv_omega) (by bv_omega), s9]
    by_cases r18 : r = 18
    · subst r18; simp only [exitCore, Core.goto_get, Core.wr_get_ne _ _ _ _ _ (show (18 : Reg) ≠ 2 by decide),
        Core.wr_get_ne _ _ _ _ _ (show (18 : Reg) ≠ 19 by decide), Core.wr_get_self _ (18 : Reg) _ _ (by decide)]
      rw [sp', W _ (by bv_omega) (by bv_omega), s18]
    by_cases r19 : r = 19
    · subst r19; simp only [exitCore, Core.goto_get, Core.wr_get_ne _ _ _ _ _ (show (19 : Reg) ≠ 2 by decide),
        Core.wr_get_self _ (19 : Reg) _ _ (by decide)]
      rw [sp', W _ (by bv_omega) (by bv_omega), s19]
    have r16 : r ≠ 16 := fun e => hr (by subst e; decide)
    simp only [exitCore, Core.goto_get, Core.wr_get_ne _ _ _ _ _ r2, Core.wr_get_ne _ _ _ _ _ r19,
      Core.wr_get_ne _ _ _ _ _ r18, Core.wr_get_ne _ _ _ _ _ r9, Core.wr_get_ne _ _ _ _ _ r8,
      Core.wr_get_ne _ _ _ _ _ r16]
    exact hk r hr (by
      intro hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with e | e | e | e | e
      · exact r2 (Fin.ext e)
      · exact r8 (Fin.ext e)
      · exact r9 (Fin.ext e)
      · exact r18 (Fin.ext e)
      · exact r19 (Fin.ext e))
  · simp only [exitCore]
    exact (Core.sameCsr_goto _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
      ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans
      ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_wr _ _ _ _).trans hcs))))))))
  · intro x hx
    simp only [Writable, not_or] at hx
    obtain ⟨xo, xb, xf⟩ := hx
    show exitRam e S x = R x
    unfold exitRam; rw [h10]
    rw [ramWrite_w_out, ramWrite_w_out]
    · exact hSo x xb xf
    all_goals bv_omega
  · show ramRead (exitRam e S) (c.get 10) .w = e.get 11
    unfold exitRam; simp only [h10, BitVec.add_zero]; rw [ramRead_ramWrite_w]
  · show ramRead (exitRam e S) (c.get 10 + e.get 16) .w = e.get 7
    unfold exitRam; simp only [h10, BitVec.add_zero]; rw [ramRead_w_out, BitVec.add_comm, ramRead_ramWrite_w]
    all_goals bv_omega
  · intro h4
    show ramRead (exitRam e S) (c.get 10 + 8#32) .w = _
    unfold exitRam; rw [h10, h4]
    rw [ramRead_w_out, ramRead_w_out] <;> bv_omega

end E5R.Rmk.Cobs
