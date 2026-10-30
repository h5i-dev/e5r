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
import Projects.rmk.Uart.SendBytes
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


theorem wb_same (R : Word → BitVec 8) (a v : Word) : ramWrite R a v .b a = byteOf v 0 := by
  simp [ramWrite, ramPut]

/-- Slot words lie below send_bytes' frame. -/
theorem slot_keep {m₀ : Machine} (h : SendAt m₀) {R M : Word → BitVec 8}
    (hR : ∀ x, ¬ ((m₀.core.get 2).toNat - 0x50 ≤ x.toNat ∧ x.toNat < (m₀.core.get 2).toNat) → R x = M x)
    (b : Word) (hb : 0x8002a7c4 ≤ b.toNat ∧ b.toNat + 4 ≤ 0x8002a7f1) : ramRead R b .w = ramRead M b .w := by
  have := h.sp
  refine ramRead_w_congr b fun k hk => hR _ ?_
  intro ⟨h1, h2⟩
  have : (b + BitVec.ofNat 32 k).toNat = b.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 32), Nat.mod_eq_of_lt (by omega)]
  omega

/-! ## The call: `CallInv` gives `send_bytes`'s `SendEnv` -/

theorem env {m₀ m : Machine} {sent : Nat} (h : SendAt m₀) (I : CallInv m₀ sent m) : SendEnv m := by
  have hsp := h.sp
  have hsep := h.selfSep
  have hsl := h.selfSlots
  have hin := h.selfIn
  have hb := h.buf
  have hlt := I.lt
  have sp2 : m.core.get 2 = m₀.core.get 2 := I.keep.sp
  have nW : ∀ o : Nat, o < 0x21 → ¬ SendW (m₀.core.get 2) (uOf m₀.ram + BitVec.ofNat 32 o) := by
    intro o ho hw
    have : (uOf m₀.ram + BitVec.ofNat 32 o).toNat = (uOf m₀.ram).toNat + o := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : o < 2 ^ 32), Nat.mod_eq_of_lt (by omega)]
    unfold SendW InSlots at hw
    omega
  refine ⟨I.pc, I.keep.quiet, by rw [I.ra]; decide, by rw [sp2]; exact h.spAl, by rw [sp2]; omega, ?_, ?_,
    by rw [I.a0]; exact h.selfAl, by rw [I.a0]; exact hin, by rw [I.a0, sp2]; exact hsep, .inr ?_⟩
  · rw [I.a0, ← h.base]
    refine ramRead_w_congr _ fun k hk => ?_
    rw [BitVec.add_assoc, show (0x0000001c#32 : Word) + BitVec.ofNat 32 k = BitVec.ofNat 32 (0x1c + k) by
      rw [BitVec.ofNat_add]]
    exact I.keep.ram _ (nW _ (by omega))
  · rw [I.a0, show (0x00000020#32 : Word) = BitVec.ofNat 32 0x20 from rfl, I.keep.ram _ (nW _ (by decide))]
    exact h.stride
  · rw [I.a1, I.a2]
    rw [B_ram] at hb ⊢
    have e1 : (m₀.core.get 8 + BitVec.ofNat 32 sent).toNat = (m₀.core.get 8).toNat + sent := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : sent < 2 ^ 32), Nat.mod_eq_of_lt (by omega)]
    have e2 : (m₀.core.get 11 - BitVec.ofNat 32 sent).toNat = (m₀.core.get 11).toNat - sent := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [e1, e2]; omega


/-! ## After `send_bytes` returns -/

theorem after {m₀ m : Machine} {sent : Nat} (h : SendAt m₀) (I : CallInv m₀ sent m)
    (IH : ∀ sent' m'', sent < sent' → CallInv m₀ sent' m'' → Lands B img (SendQ m₀) m'')
    (m' : Machine) (P : SendPost m m') : Lands B img (SendQ m₀) m' := by
  obtain ⟨e, M⟩ := m'
  have hsp := h.sp
  have hlt := I.lt
  have epc : e.pc = 0x800042fc := P.pc.trans I.ra
  have qe : Quiet e := P.quiet
  have e2 : e.get 2 = m₀.core.get 2 := P.sp.trans I.keep.sp
  have eS : ∀ r : Reg, r.val ∉ LW → e.get r = m₀.core.get r := fun r hr =>
    (P.saved r fun hc => hr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc))).trans (I.keep.regs r hr)
  have e22 : e.get 22 = 0x8002a4bd := (eS 22 (by decide)).trans h.s6
  have e23 : e.get 23 = 0x8002a3cf := (eS 23 (by decide)).trans h.s7
  have e26 : e.get 26 = 0x8002a7f0 := (eS 26 (by decide)).trans h.s10
  have e27 : e.get 27 = 0x8002a7ed := (eS 27 (by decide)).trans h.s11
  have fr : ∀ x, ¬ ((m₀.core.get 2).toNat - 0x50 ≤ x.toNat ∧ x.toNat < (m₀.core.get 2).toNat) → M x = m.ram x :=
    fun x hx => P.ram x (by rw [I.keep.sp]; exact hx)
  have eM : ∀ x, ¬ SendW (m₀.core.get 2) x → M x = m₀.ram x := fun x hx =>
    (fr x fun hf => hx (.inr hf)).trans (I.keep.ram x hx)
  have sl : ∀ b : Word, 0x8002a7c4 ≤ b.toNat ∧ b.toNat + 4 ≤ 0x8002a7f1 → ramRead M b .w = ramRead m.ram b .w :=
    slot_keep h fr
  have m12 : (m.core.get 12).toNat = (m₀.core.get 11).toNat - sent := by
    rw [I.a2, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hc := P.count
  rw [m12] at hc
  by_cases hz : taken .eq (e.get 10) 0 = true
  · -- nothing sent: the yield future's flag cleared, the yield poll called (boundary)
    have r := lZero e M epc qe hz (by rw [e22]; decide) (by rw [e22]; decide)
    refine lands_of_qrun r ⟨⟨Quiet.of_sameCsr (lZeroCsr e M) qe, ?_, fun r hr => ?_, fun x hx => ?_⟩,
      .inr ⟨rfl, ?_, ?_, ?_, ?_⟩⟩
    · show (lZeroCore e M).get 2 = _; simp [lZeroCore, Core.wr_get_ne, e2]
    · obtain ⟨n1, n8, n10, n11, n12, n13, n14⟩ := notLW hr
      show (lZeroCore e M).get r = _; simp [lZeroCore, Core.wr_get_ne, n1, n10, n11, eS r hr]
    · show lZeroRam e M x = _
      simp only [lZeroRam, e22]
      rw [wb_slots _ _ _ _ (by decide) fun hs => hx (.inl hs)]; exact eM x hx
    · show (lZeroCore e M).get 1 = _; simp [lZeroCore, Core.wr_get_self]
    · show (lZeroCore e M).get 10 = _; simp [lZeroCore, Core.wr_get_ne, Core.wr_get_self, e23]; rfl
    · show lZeroRam e M 0x8002a7ec = 0
      simp only [lZeroRam, e22]; rw [show (0x8002a4bd : Word) + 0x0000032f#32 = 0x8002a7ec from rfl, wb_same]; rfl
    · show (lZeroCore e M).get 11 = _; simp [lZeroCore, Core.wr_get_ne, Core.wr_get_self, e2]; rfl
  -- k ≥ 1 bytes sent: sent' = sent + k
  have hk : 1 ≤ (e.get 10).toNat ∧ (e.get 10).toNat ≤ (m₀.core.get 11).toNat - sent := by
    rcases hc with h0 | h1
    · exfalso; apply hz; simp only [taken, beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by rw [h0]; rfl)
    · exact ⟨h1.1, h1.2.1⟩
  have r1 := lAdd e M epc qe (Bool.eq_false_iff.mpr hz) (by rw [e22]; decide) (by rw [e22]; decide)
    (by rw [e22]; decide) (by rw [e22]; decide)
  refine lands_of_qrun_lands r1 ?_
  have rS : ramRead M (e.get 22 + 0x00000327#32) .w = BitVec.ofNat 32 sent := by
    rw [e22]; show ramRead M 0x8002a7e4 .w = _; rw [sl _ (by decide)]; exact I.sSent
  have sw : e.get 10 + BitVec.ofNat 32 sent = BitVec.ofNat 32 (sent + (e.get 10).toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : sent < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  have A10 : (lAddCore e M).get 10 = BitVec.ofNat 32 (sent + (e.get 10).toNat) := by
    rw [show (lAddCore e M).get 10 = alu .add (e.get 10) (ramRead M (e.get 22 + 0x00000327#32) .w) by
      simp [lAddCore, Core.wr_get_self], rS, alu_add, sw]
  have AR : lAddRam e M = ramWrite M 0x8002a7e4 (BitVec.ofNat 32 (sent + (e.get 10).toNat)) .w := by
    simp only [lAddRam]; rw [rS, alu_add, sw, e22]; rfl
  have AS : ∀ r : Reg, r ≠ 10 → r ≠ 11 → (lAddCore e M).get r = e.get r := fun r a b => by
    simp [lAddCore, Core.wr_get_ne, a, b]
  have A22 : (lAddCore e M).get 22 = 0x8002a4bd := (AS 22 (by decide) (by decide)).trans e22
  have qA : Quiet (lAddCore e M) := Quiet.of_sameCsr (lAddCsr e M) qe
  -- slot words other than `sent` read through the store
  have rA : ∀ b : Word, (b = 0x8002a7cc ∨ b = 0x8002a7d0 ∨ b = 0x8002a7d4 ∨ b = 0x8002a7e0) →
      ramRead (lAddRam e M) b .w = ramRead m.ram b .w := by
    intro b hb
    rw [AR, rd_ww _ _ _ _ (by rcases hb with rfl | rfl | rfl | rfl <;> decide) (by decide)
      (by rcases hb with rfl | rfl | rfl | rfl <;> decide),
      sl _ (by rcases hb with rfl | rfl | rfl | rfl <;> decide)]
  have rLen : ramRead (lAddRam e M) (0x8002a4bd + 0x00000317#32) .w = m₀.core.get 11 := by
    rw [show (0x8002a4bd : Word) + 0x00000317#32 = 0x8002a7d4 from rfl, rA _ (by decide), I.sLen]
  have hs : sent < sent + (e.get 10).toNat ∧ sent + (e.get 10).toNat ≤ (m₀.core.get 11).toNat := by omega
  generalize sent + (e.get 10).toNat = s' at A10 AR hs
  have kA : ∀ r : Reg, r.val ∉ LW → (lAddCore e M).get r = m₀.core.get r := fun r hr => by
    obtain ⟨n1, n8, n10, n11, n12, n13, n14⟩ := notLW hr; rw [AS r n10 n11]; exact eS r hr
  have ramA : ∀ x, ¬ SendW (m₀.core.get 2) x → lAddRam e M x = m₀.ram x := fun x hx => by
    rw [AR, ww_slots _ _ _ _ (by decide) fun hs => hx (.inl hs)]; exact eM x hx
  have A2 : (lAddCore e M).get 2 = m₀.core.get 2 := (AS 2 (by decide) (by decide)).trans e2
  by_cases hd : s' < (m₀.core.get 11).toNat
  · -- more to send: back to the call with sent' = s'
    have hw : taken .geu ((lAddCore e M).get 10) (ramRead (lAddRam e M) ((lAddCore e M).get 22 + 0x00000317#32) .w)
        = false := by
      rw [A10, A22, rLen]; simp only [taken, BitVec.ult, Bool.not_eq_false', decide_eq_true_eq, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]; exact hd
    have r2 := lMore (lAddCore e M) (lAddRam e M) rfl qA (by rw [A22]; decide) (by rw [A22]; decide) hw
      (by rw [A22]; decide) (by rw [A22]; decide) (by rw [A22]; decide) (by rw [A22]; decide)
    have MS : ∀ r : Reg, r ≠ 1 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 →
        (lMoreCore (lAddCore e M) (lAddRam e M)).get r = (lAddCore e M).get r := fun r a b c d f g => by
      simp [lMoreCore, Core.wr_get_ne, a, b, c, d, f, g]
    refine lands_of_qrun_lands r2 (IH s' _ hs.1 ⟨rfl, by simp [lMoreCore, Core.wr_get_self],
      ⟨Quiet.of_sameCsr (lMoreCsr _ _) qA, (MS 2 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)).trans A2, fun r hr => ?_, fun x hx => ramA x hx⟩, ?_, ?_, ?_, hd, ?_, ?_, ?_, ?_, ?_⟩)
    · obtain ⟨n1, n8, n10, n11, n12, n13, n14⟩ := notLW hr
      exact (MS r n1 n10 n11 n12 n13 n14).trans (kA r hr)
    · show (lMoreCore (lAddCore e M) (lAddRam e M)).get 10 = _
      rw [show (lMoreCore (lAddCore e M) (lAddRam e M)).get 10 =
          alu .add 0 (ramRead (lAddRam e M) ((lAddCore e M).get 22 + 0x00000323#32) .w) by
        simp [lMoreCore, Core.wr_get_ne, Core.wr_get_self],
        A22, show (0x8002a4bd : Word) + 0x00000323#32 = 0x8002a7e0 from rfl, rA _ (by decide), I.sU, alu_add]
      simp
    · show (lMoreCore (lAddCore e M) (lAddRam e M)).get 11 = _
      rw [show (lMoreCore (lAddCore e M) (lAddRam e M)).get 11 =
          alu .add (ramRead (lAddRam e M) ((lAddCore e M).get 22 + 0x00000313#32) .w) ((lAddCore e M).get 10) by
        simp [lMoreCore, Core.wr_get_ne, Core.wr_get_self],
        A22, show (0x8002a4bd : Word) + 0x00000313#32 = 0x8002a7d0 from rfl, rA _ (by decide), I.sPtr, alu_add, A10]
    · show (lMoreCore (lAddCore e M) (lAddRam e M)).get 12 = _
      rw [show (lMoreCore (lAddCore e M) (lAddRam e M)).get 12 =
          alu .sub (ramRead (lAddRam e M) ((lAddCore e M).get 22 + 0x00000317#32) .w) ((lAddCore e M).get 10) by
        simp [lMoreCore, Core.wr_get_ne, Core.wr_get_self], A22, rLen, alu_sub, A10]
    · show ramRead (lAddRam e M) 0x8002a7e4 .w = _; rw [AR, rd_ww_same]
    · show ramRead (lAddRam e M) 0x8002a7d4 .w = _; rw [rA _ (by decide)]; exact I.sLen
    · show ramRead (lAddRam e M) 0x8002a7d0 .w = _; rw [rA _ (by decide)]; exact I.sPtr
    · show ramRead (lAddRam e M) 0x8002a7e0 .w = _; rw [rA _ (by decide)]; exact I.sU
    · show ramRead (lAddRam e M) 0x8002a7cc .w = _; rw [rA _ (by decide)]; exact I.sOut
  · -- done: sent' = len; [s11] = 1, the outer slice advanced (no slice panic), [s10] = 1, the unpark site
    have hE : s' = (m₀.core.get 11).toNat := by omega
    have A10' : (lAddCore e M).get 10 = m₀.core.get 11 := by rw [A10, hE, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hw : taken .geu ((lAddCore e M).get 10) (ramRead (lAddRam e M) ((lAddCore e M).get 22 + 0x00000317#32) .w)
        = true := by
      rw [A10', A22, rLen]; simp [taken, BitVec.ult]
    have hnz : taken .eq ((lAddCore e M).get 10) 0 = false := by
      rw [A10']; simp only [taken, beq_eq_false_iff_ne, ne_eq]; intro h0; have := h.len; rw [h0] at this; simp at this
    have A27 : (lAddCore e M).get 27 = 0x8002a7ed := (AS 27 (by decide) (by decide)).trans e27
    have r2 := lDn1 (lAddCore e M) (lAddRam e M) rfl qA (by rw [A22]; decide) (by rw [A22]; decide) hw
      (by rw [A27]; decide) (by rw [A27]; decide) hnz
    refine lands_of_qrun_lands r2 ?_
    have DS : ∀ r : Reg, r ≠ 11 → r ≠ 12 → (lDn1Core (lAddCore e M) (lAddRam e M)).get r = (lAddCore e M).get r :=
      fun r a b => by simp [lDn1Core, Core.wr_get_ne, a, b]
    have DR : lDn1Ram (lAddCore e M) (lAddRam e M) = ramWrite (lAddRam e M) 0x8002a7ed 1 .b := by
      simp only [lDn1Ram]; rw [A27]; rfl
    have qD := Quiet.of_sameCsr (lDn1Csr (lAddCore e M) (lAddRam e M)) qA
    have Dpc : (lDn1Core (lAddCore e M) (lAddRam e M)).pc = 0x80004282 := rfl
    generalize lDn1Core (lAddCore e M) (lAddRam e M) = D at DS r2 qD Dpc
    generalize lDn1Ram (lAddCore e M) (lAddRam e M) = RD at DR r2
    have D10 : D.get 10 = m₀.core.get 11 := (DS 10 (by decide) (by decide)).trans A10'
    have D22 : D.get 22 = 0x8002a4bd := (DS 22 (by decide) (by decide)).trans A22
    have D26 : D.get 26 = 0x8002a7f0 := (DS 26 (by decide) (by decide)).trans ((AS 26 (by decide) (by decide)).trans e26)
    have rOut : ramRead RD (D.get 22 + 0x0000030f#32) .w = m₀.core.get 11 := by
      rw [D22, DR, show (0x8002a4bd : Word) + 0x0000030f#32 = 0x8002a7cc from rfl, rd_wb _ _ _ _ (by decide) (by decide),
        rA _ (by decide), I.sOut]
    have hlt' : taken .ltu (ramRead RD (D.get 22 + 0x0000030f#32) .w) (D.get 10) = false := by
      rw [rOut, D10]; simp [taken, BitVec.ult]
    have heq : taken .eq (alu .sub (ramRead RD (D.get 22 + 0x0000030f#32) .w) (D.get 10)) 0 = true := by
      rw [rOut, D10, alu_sub]; simp [taken]
    have r3 := lDn2 D RD Dpc qD (by rw [D22]; decide) (by rw [D22]; decide) hlt' (by rw [D22]; decide)
      (by rw [D22]; decide) (by rw [D22]; decide) (by rw [D22]; decide) (by rw [D22]; decide) (by rw [D22]; decide)
      heq (by rw [D26]; decide) (by rw [D26]; decide)
    have FS : ∀ r : Reg, r ≠ 8 → r ≠ 10 → r ≠ 11 → (lDn2Core D RD).get r = D.get r := fun r a b c => by
      simp [lDn2Core, Core.wr_get_ne, a, b, c]
    refine lands_of_qrun r3 ⟨⟨Quiet.of_sameCsr (lDn2Csr D RD) qD, ?_, fun r hr => ?_, fun x hx => ?_⟩, .inl ⟨rfl, ?_⟩⟩
    · rw [FS 2 (by decide) (by decide) (by decide), DS 2 (by decide) (by decide)]; exact A2
    · obtain ⟨n1, n8, n10, n11, n12, n13, n14⟩ := notLW hr
      rw [FS r n8 n10 n11, DS r n11 n12]; exact kA r hr
    · have hs : ¬ InSlots x := fun hs => hx (.inl hs)
      show lDn2Ram D RD x = _
      simp only [lDn2Ram]
      rw [D26, D22, wb_slots _ _ _ _ (by decide) hs, ww_slots _ _ _ _ (by decide) hs, ww_slots _ _ _ _ (by decide) hs,
        DR, wb_slots _ _ _ _ (by decide) hs]
      exact ramA x hx
    · show lDn2Ram D RD 0x8002a7f0 = 1
      simp only [lDn2Ram]; rw [D26, wb_same]; rfl


/-! ## The loop and the headline -/

/-- From the `send_bytes` call after `sent` bytes: by strong induction on `len - sent` (every return of
    k ≥ 1 bytes strictly decreases it; a return of 0 stops at the yield boundary). -/
theorem send_loop {m₀ : Machine} (h : SendAt m₀) :
    ∀ n sent m, (m₀.core.get 11).toNat - sent = n → CallInv m₀ sent m → Lands B img (SendQ m₀) m := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro sent m hn I
    refine lands_seq (fun m' P => after h I (fun sent' m'' hs I' => ?_) m' P) (send_bytes m (env h I))
    exact ih _ (by have := I'.lt; omega) sent' m'' rfl I'

/-- **The UART send loop**: from `SendAt` at 0x8000429e, every behaviour of the model (every value the
    UART registers return) reaches the unpark site 0x80003fd8 with [s10] = 1, or the yield poll's entry
    0x8001e14a (a boundary to the executor), keeping sp, every register but ra, s0 and the caller-saved
    ones, and all RAM outside the send slots and [sp-0x50, sp). No fault, no interrupt taken. -/
theorem send_round (m₀ : Machine) (h : SendAt m₀) : Lands B img (SendQ m₀) m₀ := by
  obtain ⟨k, m, r, I⟩ := ent m₀ h
  exact lands_of_qrun_lands r (send_loop h _ 0 m rfl I)

/-! ## `SendAt` is satisfiable -/

/-- A core at the send entry: interrupts off, s0 = 0x8002a7b1 (encode_frame's buffer), a1 = 7,
    s6/s7/s10/s11 as the poll sets them, sp = 0x80100000. -/
def wCore : Core where
  pc := 0x8000429e
  x := fun r => if r.val = 2 then 0x80100000 else if r.val = 8 then 0x8002a7b1 else if r.val = 11 then 7
    else if r.val = 22 then 0x8002a4bd else if r.val = 23 then 0x8002a3cf else if r.val = 26 then 0x8002a7f0
    else if r.val = 27 then 0x8002a7ed else 0
  mie_ := false
  mpie := false
  mpp := 3
  mieReg := 0
  mtvec := 0x800000f8
  mepc := 0
  mcause := 0
  mscratch := 0
  resv := false

/-- RAM: [0x8002a7c4] = 0x80090000 (the send's struct pointer), [0x8002a7cc] = 7 (the outer length), the
    struct with base 0x10000000 at +0x1c and stride 1 at +0x20; for the session's `Extras` (SendToLoop):
    [0x8002a784] = 0x80090000 (the reader's struct pointer, the same struct) and the task flag pointer
    [sp+0x24] = 0x80090100. -/
def wRam (a : Word) : BitVec 8 :=
  if a = 0x8002a7c6 then 0x09 else if a = 0x8002a7c7 then 0x80 else if a = 0x8002a7cc then 7
  else if a = 0x8009001f then 0x10 else if a = 0x80090020 then 1
  else if a = 0x8002a786 then 0x09 else if a = 0x8002a787 then 0x80
  else if a = 0x80100025 then 0x01 else if a = 0x80100026 then 0x09 else if a = 0x80100027 then 0x80 else 0

theorem w_sendAt : SendAt ⟨wCore, wRam⟩ := by
  refine ⟨rfl, fun code => by simp [irqEnabled, wCore], by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

end E5R.Rmk.Uart
