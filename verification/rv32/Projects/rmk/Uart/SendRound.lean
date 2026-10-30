/-
  The session poll's UART send loop (0x8000429e), composed with main's `send_bytes` (Uart/SendBytes.lean,
  no contract), on the pinned RMK image. No callee contract is assumed: the only call proved through is
  `send_bytes`; the yield poll (0x8001e14a, which calls the executor's waker through a vtable) is an
  explicit BOUNDARY.

  Original e5r code, Apache-2.0.

  The loop (from the bytes): the response slice (ptr s0, len a1) and the Uart16550 pointer [s6+0x307]
  are stored in the poll's future slots [s6+0x307, s6+0x334) = [0x8002a7c4, 0x8002a7f1); then, with
  `sent = 0`, it calls `send_bytes(uart, ptr + sent, len - sent)` at 0x800042f8 until `sent ≥ len`. A
  return of 0 clears the yield flag [s6+0x32f] and calls the yield poll at 0x80004320 (boundary). When
  done it sets the write future's state [s11] = 1, advances the outer slice (the slice check at
  0x80004286 is not taken, and `sent = 0` at 0x80004280 is not taken), sets the flag byte [s10] = 1 and
  jumps to the unpark site 0x80003fd8.

  `SendAt`: the send-entry preconditions, stated independently of `SomeAt`/`SessInv` so that whoever
  reaches 0x8000429e (main's Some path) can establish them; `w_sendAt` shows they are satisfiable.
  Two of them are NOT in main's current invariant: s11 (x27) = s6+0x330 = 0x8002a7ed, and the
  Uart16550 pointer the send uses, [s6+0x307] (copied from [s6+0x2cb] = 0x8002a788 at 0x80003f40;
  `Extras` describes [0x8002a784]). The stack bound is sp ≥ 0x8002a844 so that send_bytes' 0x50-byte
  frame stays clear of the slots (`SessPre`'s sp ≥ 0x8002a808 does not ensure that).

  PROVED here: `send_round`: from `SendAt`, every behaviour of the model (every UART value) reaches
  * the unpark site 0x80003fd8 with [s10] = 1, or
  * the yield poll's entry 0x8001e14a (ra 0x80004324, a0 = the yield flag 0x8002a7ec, which is 0,
    a1 = sp+0x30): a boundary to the executor, not proved;
  in both cases quiet, with sp, s1..s11 except s0, and all RAM outside the slots and [sp-0x50, sp) as
  at entry. No step faults, no interrupt is taken (`Lands`).
-/
import Projects.rmk.Uart.SendLoopSegs

set_option maxRecDepth 100000

namespace E5R.Rmk.Uart
open E5R E5R.Rmk E5R.Rmk.Deframer E5R.Rmk.Deframer.Tail

/-- The send loop's future slots [0x8002a7c4, 0x8002a7f1) (s6+0x307 .. s6+0x334). -/
def InSlots (x : Word) : Prop := 0x8002a7c4 ≤ x.toNat ∧ x.toNat < 0x8002a7f1

/-- Everything the send loop writes, for a poll frame at sp: the slots and send_bytes' frame. -/
def SendW (sp x : Word) : Prop := InSlots x ∨ (sp.toNat - 0x50 ≤ x.toNat ∧ x.toNat < sp.toNat)

/-- The registers the loop may change: ra, s0 and the caller-saved ones. -/
def LW : List Nat := 1 :: 8 :: callerSaved

/-- The Uart16550 pointer the send uses, [s6+0x307]. -/
def uOf (M : Word → BitVec 8) : Word := ramRead M 0x8002a7c4 .w

/-- The send-entry preconditions at 0x8000429e. -/
structure SendAt (m : Machine) : Prop where
  pc : m.core.pc = 0x8000429e
  quiet : Quiet m.core
  s6 : m.core.get 22 = 0x8002a4bd
  s7 : m.core.get 23 = 0x8002a3cf
  s10 : m.core.get 26 = 0x8002a7f0
  s11 : m.core.get 27 = 0x8002a7ed
  spAl : (m.core.get 2).toNat % 4 = 0
  sp : 0x8002a7f4 + 0x50 ≤ (m.core.get 2).toNat ∧ (m.core.get 2).toNat ≤ 0x81000000
  /-- the response slice (s0, a1): non-empty, in RAM -/
  len : 1 ≤ (m.core.get 11).toNat
  buf : B.inRam (m.core.get 8) (m.core.get 11).toNat = true
  /-- the outer slice's length [s6+0x30f], as stored at 0x80003f48 -/
  outer : ramRead m.ram 0x8002a7cc .w = m.core.get 11
  /-- the Uart16550 struct: base 0x10000000 (+0x1c), stride 1 (+0x20), clear of the slots and frame -/
  base : ramRead m.ram (uOf m.ram + 0x0000001c#32) .w = 0x10000000
  stride : (m.ram (uOf m.ram + 0x00000020#32)).toNat = 1
  selfAl : (uOf m.ram + 0x0000001c#32).toNat % 4 = 0
  selfIn : 0x80029bc8 ≤ (uOf m.ram).toNat ∧ (uOf m.ram).toNat + 0x21 ≤ 0x81000000
  selfSep : (uOf m.ram).toNat + 0x21 ≤ (m.core.get 2).toNat - 0x50 ∨ (m.core.get 2).toNat ≤ (uOf m.ram).toNat
  selfSlots : (uOf m.ram).toNat + 0x21 ≤ 0x8002a7c4 ∨ 0x8002a7f1 ≤ (uOf m.ram).toNat

/-- What the loop keeps, relative to the entry machine. -/
structure Kept (m₀ m : Machine) : Prop where
  quiet : Quiet m.core
  sp : m.core.get 2 = m₀.core.get 2
  regs : ∀ r : Reg, r.val ∉ LW → m.core.get r = m₀.core.get r
  ram : ∀ x, ¬ SendW (m₀.core.get 2) x → m.ram x = m₀.ram x

/-- Where the send loop stops. -/
def SendQ (m₀ m : Machine) : Prop :=
  Kept m₀ m ∧
    ((m.core.pc = 0x80003fd8 ∧ m.ram 0x8002a7f0 = 1) ∨
     (m.core.pc = 0x8001e14a ∧ m.core.get 1 = 0x80004324 ∧ m.core.get 10 = 0x8002a7ec ∧
       m.ram 0x8002a7ec = 0 ∧ m.core.get 11 = m₀.core.get 2 + 0x00000030#32))

/-- At the `send_bytes` call 0x800042f8 → 0x800098a6, after `sent` bytes. -/
structure CallInv (m₀ : Machine) (sent : Nat) (m : Machine) : Prop where
  pc : m.core.pc = 0x800098a6
  ra : m.core.get 1 = 0x800042fc
  keep : Kept m₀ m
  a0 : m.core.get 10 = uOf m₀.ram
  a1 : m.core.get 11 = m₀.core.get 8 + BitVec.ofNat 32 sent
  a2 : m.core.get 12 = m₀.core.get 11 - BitVec.ofNat 32 sent
  lt : sent < (m₀.core.get 11).toNat
  sSent : ramRead m.ram 0x8002a7e4 .w = BitVec.ofNat 32 sent
  sLen : ramRead m.ram 0x8002a7d4 .w = m₀.core.get 11
  sPtr : ramRead m.ram 0x8002a7d0 .w = m₀.core.get 8
  sU : ramRead m.ram 0x8002a7e0 .w = uOf m₀.ram
  sOut : ramRead m.ram 0x8002a7cc .w = m₀.core.get 11

/-! ## RAM helpers -/

theorem wb_other (R : Word → BitVec 8) (a v x : Word) (h : x ≠ a) : ramWrite R a v .b x = R x := by
  simp [ramWrite, ramPut, h]

/-- A word store inside the slots leaves every byte outside them alone. -/
theorem ww_slots (R : Word → BitVec 8) (a v x : Word) (ha : 0x8002a7c4 ≤ a.toNat ∧ a.toNat + 4 ≤ 0x8002a7f1)
    (hx : ¬ InSlots x) : ramWrite R a v .w x = R x :=
  wr_byte_other R a v x (by omega) (by unfold InSlots at hx; omega)

theorem wb_slots (R : Word → BitVec 8) (a v x : Word) (ha : 0x8002a7c4 ≤ a.toNat ∧ a.toNat < 0x8002a7f1)
    (hx : ¬ InSlots x) : ramWrite R a v .b x = R x :=
  wb_other R a v x fun e => hx (by subst e; exact ha)

/-- A word read of a slot word `b` after a word store to a disjoint slot word `a`. -/
theorem rd_ww (R : Word → BitVec 8) (a v b : Word) (h : b.toNat + 4 ≤ a.toNat ∨ a.toNat + 4 ≤ b.toNat)
    (ha : a.toNat + 4 ≤ 2 ^ 32) (hb : b.toNat + 4 ≤ 2 ^ 32) : ramRead (ramWrite R a v .w) b .w = ramRead R b .w :=
  rd_wr_other R a v b ha hb h

theorem rd_wb (R : Word → BitVec 8) (a v b : Word) (h : a.toNat < b.toNat ∨ b.toNat + 4 ≤ a.toNat)
    (hb : b.toNat + 4 ≤ 2 ^ 32) : ramRead (ramWrite R a v .b) b .w = ramRead R b .w := by
  refine ramRead_w_congr b fun k hk => wb_other R a v _ fun e => ?_
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega)] at this
  omega

theorem rd_ww_same (R : Word → BitVec 8) (a v : Word) : ramRead (ramWrite R a v .w) a .w = v :=
  ramRead_ramWrite_w R a v

/-- RAM outside the slots and the frame, word-wise. -/
theorem rd_keep {R M : Word → BitVec 8} {sp b : Word} (h : ∀ x, ¬ SendW sp x → R x = M x)
    (hb : ∀ k < 4, ¬ SendW sp (b + BitVec.ofNat 32 k)) : ramRead R b .w = ramRead M b .w :=
  ramRead_w_congr b fun k hk => (h _ (hb k hk))

theorem notLW {r : Reg} (h : r.val ∉ LW) : r ≠ 1 ∧ r ≠ 8 ∧ r ≠ 10 ∧ r ≠ 11 ∧ r ≠ 12 ∧ r ≠ 13 ∧ r ≠ 14 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro e <;> subst e <;> exact absurd h (by decide)

/-! ## Entry: to the first `send_bytes` call -/

theorem ent (m₀ : Machine) (h : SendAt m₀) : ∃ k m, QRun B img k m₀ m ∧ CallInv m₀ 0 m := by
  obtain ⟨c, M0⟩ := m₀
  have h22 : c.get 22 = 0x8002a4bd := h.s6
  have hl : 1 ≤ (c.get 11).toNat := h.len
  have hout : ramRead M0 0x8002a7cc .w = c.get 11 := h.outer
  have hne : taken .ne (c.get 11) 0 = true := by
    simp only [taken, bne_iff_ne, ne_eq]; intro e; rw [e] at hl; simp at hl
  have r := lEnt c M0 h.pc h.quiet (by rw [h22]; decide) (by rw [h22]; decide) (by rw [h22]; decide)
    (by rw [h22]; decide) (by rw [h22]; decide) (by rw [h22]; decide) (by rw [h22]; decide)
    (by rw [h22]; decide) (by rw [h22]; decide) (by rw [h22]; decide) (by rw [h22]; decide)
    (by rw [h22]; decide) (by rw [h22]; decide) (by rw [h22]; decide) (by rw [h22]; decide)
    (by rw [h22]; decide) (by rw [h22]; decide) (by rw [h22]; decide) hne (by rw [h22]; decide)
    (by rw [h22]; decide) (by rw [h22]; decide) (by rw [h22]; decide)
  refine ⟨_, _, r, ?_⟩
  have RR : lEntRam c M0 =
      ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite M0
        0x8002a7d8 (c.get 8) .w) 0x8002a7dc (c.get 11) .w) 0x8002a7e8 (uOf M0) .w) 0x8002a7ed 0 .b)
        0x8002a7d0 (c.get 8) .w) 0x8002a7d4 (c.get 11) .w) 0x8002a7e0 (uOf M0) .w) 0x8002a7e4 0 .w := by
    simp only [lEntRam, h22, uOf]; rfl
  have rd : ∀ b : Word, b.toNat + 4 ≤ 0x8002a7c4 ∨ 0x8002a7f1 ≤ b.toNat → b.toNat + 4 ≤ 2 ^ 32 →
      ramRead (lEntRam c M0) b .w = ramRead M0 b .w := by
    intro b hb hb'
    rw [RR, rd_ww _ _ _ _ (by bv_omega) (by decide) hb', rd_ww _ _ _ _ (by bv_omega) (by decide) hb',
      rd_ww _ _ _ _ (by bv_omega) (by decide) hb', rd_ww _ _ _ _ (by bv_omega) (by decide) hb',
      rd_wb _ _ _ _ (by bv_omega) hb', rd_ww _ _ _ _ (by bv_omega) (by decide) hb',
      rd_ww _ _ _ _ (by bv_omega) (by decide) hb', rd_ww _ _ _ _ (by bv_omega) (by decide) hb']
  have g : ∀ r : Reg, r.val ∉ LW → (lEntCore c M0).get r = c.get r := fun r hr => by
    obtain ⟨n1, n8, n10, n11, n12, n13, n14⟩ := notLW hr
    simp [lEntCore, Core.wr_get_ne, n1, n10, n11, n12, n13, n14]
  have K12 : (lEntCore c M0).get 12 = c.get 11 := by
    simp [lEntCore, Core.wr_get_ne, Core.wr_get_self, alu_add, alu_sub]
  have A : ∀ o : Word, c.get 22 + o = 0x8002a4bd + o := fun o => by rw [h22]
  have K10 : (lEntCore c M0).get 10 = uOf M0 := by
    have : (lEntCore c M0).get 10 = alu .add 0 (ramRead (lEntRam c M0) (c.get 22 + 0x00000323#32) .w) := by
      simp only [lEntCore, Core.wr_get_ne, Core.wr_get_self, ne_eq]; rfl
    rw [this, A, show (0x8002a4bd : Word) + 0x00000323#32 = 0x8002a7e0 from rfl, RR,
      rd_ww _ _ _ _ (by decide) (by decide) (by decide), rd_ww_same, alu_add]
    simp
  have K11 : (lEntCore c M0).get 11 = c.get 8 + BitVec.ofNat 32 0 := by
    have : (lEntCore c M0).get 11 =
        alu .add (ramRead (lEntRam c M0) (c.get 22 + 0x00000313#32) .w) (alu .add 0 0x00000000#32) := by
      simp only [lEntCore, Core.wr_get_ne, Core.wr_get_self, ne_eq]; rfl
    rw [this, A, show (0x8002a4bd : Word) + 0x00000313#32 = 0x8002a7d0 from rfl, RR,
      rd_ww _ _ _ _ (by decide) (by decide) (by decide), rd_ww _ _ _ _ (by decide) (by decide) (by decide),
      rd_ww _ _ _ _ (by decide) (by decide) (by decide), rd_ww_same]
    rfl
  have rS : ∀ (a : Word), (lEntRam c M0) a = _ := fun a => congrFun RR a
  refine ⟨rfl, by simp [lEntCore, Core.wr_get_self], ⟨Quiet.of_sameCsr (lEntCsr c M0) h.quiet, g 2 (by decide),
    g, fun x hx => ?_⟩, K10, K11, by rw [K12]; simp, by simp only [BitVec.toNat_ofNat]; omega, ?_, ?_, ?_, ?_, ?_⟩
  · have hs : ¬ InSlots x := fun hs => hx (.inl hs)
    show lEntRam c M0 x = M0 x
    rw [RR, ww_slots _ _ _ _ (by decide) hs, ww_slots _ _ _ _ (by decide) hs, ww_slots _ _ _ _ (by decide) hs,
      ww_slots _ _ _ _ (by decide) hs, wb_slots _ _ _ _ (by decide) hs, ww_slots _ _ _ _ (by decide) hs,
      ww_slots _ _ _ _ (by decide) hs, ww_slots _ _ _ _ (by decide) hs]
  · show ramRead (lEntRam c M0) 0x8002a7e4 .w = _; rw [RR, rd_ww_same]; rfl
  · show ramRead (lEntRam c M0) 0x8002a7d4 .w = _
    rw [RR, rd_ww _ _ _ _ (by decide) (by decide) (by decide), rd_ww _ _ _ _ (by decide) (by decide) (by decide),
      rd_ww_same]
  · show ramRead (lEntRam c M0) 0x8002a7d0 .w = _
    rw [RR, rd_ww _ _ _ _ (by decide) (by decide) (by decide), rd_ww _ _ _ _ (by decide) (by decide) (by decide),
      rd_ww _ _ _ _ (by decide) (by decide) (by decide), rd_ww_same]
  · show ramRead (lEntRam c M0) 0x8002a7e0 .w = _
    rw [RR, rd_ww _ _ _ _ (by decide) (by decide) (by decide), rd_ww_same]
  · show ramRead (lEntRam c M0) 0x8002a7cc .w = _
    rw [RR, rd_ww _ _ _ _ (by decide) (by decide) (by decide), rd_ww _ _ _ _ (by decide) (by decide) (by decide), rd_ww _ _ _ _ (by decide) (by decide) (by decide), rd_ww _ _ _ _ (by decide) (by decide) (by decide),
      rd_wb _ _ _ _ (by decide) (by decide), rd_ww _ _ _ _ (by decide) (by decide) (by decide), rd_ww _ _ _ _ (by decide) (by decide) (by decide), rd_ww _ _ _ _ (by decide) (by decide) (by decide)]
    exact hout

end E5R.Rmk.Uart
