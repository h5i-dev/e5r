/-
  The Rynk session loop, one round, on the pinned RMK image: from a strengthened session invariant
  at the loop head, every behaviour of the model (any UART value) comes back to the loop head with
  the invariant, or stops at an EXPLICIT boundary.

  Original e5r code, Apache-2.0.

  `SessInv` = `SessPre` and the RAM facts the None path reads, with their addresses placed outside
  everything the proved steps write (`SW`):
  * the Uart16550 struct that the word at 0x8002a784 points to holds base 0x10000000 (+0x1c) and
    stride 1 (+0x20);
  * the task flag pointer at sp+0x24 points into RAM, outside the deframer;
  * 0x148 stack bytes lie above sp;
  * s10 (x26) = 0x8002a7f0, the empty-response flag byte address (kept by recv_step, none_step and
    unpark_step: their posts now export x26).

  PROVED here:
  * `none_of_recv`: `SessInv` at the loop head and recv_step's None outcome give `NoneAt`;
  * `session_round`: `SessInv` ⇒ `Lands1 … LoopQ`: at least one step is taken, none faults or
    takes an interrupt (per-step obligations of `Lands`), and every behaviour reaches either the
    loop head with `SessInv`, or one of three boundaries, each not proved:
    * 0x80003ff2 / 0x80004428: the read future, which yields to the executor;
    * 0x80003e70 with `SomeAt` (the message, parked ≤ 484, discarding ≤ 1, the extras): the Some
      point, where the dispatch and response gap begins;
  * `unpark_round`: from the unpark call site (`UnparkAt` and the same extras), back to the loop
    head with `SessInv`. This is the end of the Some gap.

  NOT PROVED, and nowhere assumed as a fact:
  * that `SessInv` holds when the task first reaches the loop head (initialization);
  * the dispatch and response path 0x80003e70..0x80003fd8;
  * the read future and the executor beyond the two boundaries, including that interrupts stay
    off (Quiet) across executor polls.
-/
import Projects.rmk.Deframer.NonePath
import Projects.rmk.Deframer.CopyDischarge

set_option maxRecDepth 100000

namespace E5R.Rmk.Deframer.SessionI
open E5R E5R.Rmk E5R.Rmk.Deframer.Tail E5R.Rmk.Deframer.Session E5R.Rmk.Deframer.NoneP

/-- Everything the proved session steps may write, for a session at sp (the poll's own segments;
    the dispatch and encode_frame calls are covered by their contracts' `Kept`, not by `SW`). -/
def SW (sp : Word) (x : Word) : Prop :=
  (0x8002a78c ≤ x.toNat ∧ x.toNat < 0x8002a798) ∨ (0x8002a590 ≤ x.toNat ∧ x.toNat < 0x8002a778) ∨
  (sp.toNat - 0x70 ≤ x.toNat ∧ x.toNat < sp.toNat) ∨ (0x8002a798 ≤ x.toNat ∧ x.toNat < 0x8002a7b0) ∨
  (0x8002a580 ≤ x.toNat ∧ x.toNat < 0x8002a590) ∨ (0x8002a7b0 ≤ x.toNat ∧ x.toNat < 0x8002a7f4) ∨
  (sp.toNat + 0x140 ≤ x.toNat ∧ x.toNat < sp.toNat + 0x148)

/-- The Uart16550 struct pointer word. -/
def uPtr : Word := 0x8002a784

structure Extras (m : Machine) : Prop where
  /-- the poll frame up to sp+0x148 (the flag pointer at sp+0x24, encode_frame's argument byte at
      sp+0x140) is RAM -/
  spTop : (m.core.get 2).toNat + 0x148 ≤ 0x81000000
  uBase : ramRead m.ram (ramRead m.ram uPtr .w + 0x0000001c#32) .w = 0x10000000
  uBaseIn : (ramRead m.ram uPtr .w + 0x0000001c#32).toNat % 4 = 0 ∧
    B.inRam (ramRead m.ram uPtr .w + 0x0000001c#32) 4 = true
  uStride : (m.ram (ramRead m.ram uPtr .w + 0x00000020#32)).toNat = 1
  uStrideIn : B.inRam (ramRead m.ram uPtr .w + 0x00000020#32) 1 = true
  /-- the struct's five bytes 0x1c..0x20 lie outside every written range and the flag byte -/
  uSep : ∀ k < 5, ¬ SW (m.core.get 2) (ramRead m.ram uPtr .w + 0x0000001c#32 + BitVec.ofNat 32 k) ∧
    ramRead m.ram uPtr .w + 0x0000001c#32 + BitVec.ofNat 32 k ≠ ramRead m.ram (m.core.get 2 + 0x00000024#32) .w
  flagIn : B.inRam (ramRead m.ram (m.core.get 2 + 0x00000024#32) .w) 1 = true
  flagSep : (ramRead m.ram (m.core.get 2 + 0x00000024#32) .w).toNat < dfr.toNat ∨
    dfr.toNat + 12 ≤ (ramRead m.ram (m.core.get 2 + 0x00000024#32) .w).toNat
  /-- the flag byte is neither the struct pointer word nor the flag pointer word -/
  flagNot : ∀ k < 4, ramRead m.ram (m.core.get 2 + 0x00000024#32) .w ≠ uPtr + BitVec.ofNat 32 k ∧
    ramRead m.ram (m.core.get 2 + 0x00000024#32) .w ≠ m.core.get 2 + 0x00000024#32 + BitVec.ofNat 32 k
  /-- s10 (x26) holds s6+0x333 = 0x8002a7f0, the address the Some path's empty response stores its
      flag byte to (set at 0x80003b38 before the loop; kept by every proved step) -/
  s10 : m.core.get 26 = 0x8002a7f0

def SessInv (m : Machine) : Prop := SessPre m ∧ Extras m

theorem recvW_SW (sp x : Word) (h : RecvW sp x) : SW sp x := by
  unfold RecvW at h; unfold SW
  rw [show dfr.toNat = 0x8002a78c from rfl, show bufA.toNat = 0x8002a590 from rfl,
    show msgA.toNat = 0x8002a580 from rfl, show bufLen = 488 from rfl] at h
  omega

/-- A word read entirely outside `SW` survives the receive step. -/
theorem rd_keep (sp : Word) (M M0 : Word → BitVec 8) (hk : ∀ x, ¬ SW sp x → M x = M0 x) (a : Word)
    (ha : ∀ k < 4, ¬ SW sp (a + BitVec.ofNat 32 k)) : ramRead M a .w = ramRead M0 a .w :=
  ramRead_w_congr a fun k hk' => hk _ (ha k hk')

theorem none_of_recv (m₀ m : Machine) (h : SessInv m₀) (hr : RecvOut m₀ m)
    (hn : m.core.pc = 0x80003f7c ∧ Inv m.ram dfr bufLen ∧ consumed m.ram dfr = 0 ∧
      m.core.get 18 = bufA + BitVec.ofNat 32 (filled m.ram dfr) ∧
      (m.core.get 20).toNat = bufLen - filled m.ram dfr ∧ discarding m.ram dfr ≤ 1 ∧
      (m.core.get 25).toNat = discarding m.ram dfr ∧ (m.core.get 21).toNat ≤ (m.core.get 24).toNat ∧
      (m.core.get 24).toNat - (m.core.get 21).toNat = filled m.ram dfr ∧
      m.core.get 19 = ramRead m₀.ram 0x8002a784 .w) :
    NoneAt m := by
  obtain ⟨hpc, hinv, hc0, hs2, hs4, hdisc, hs9, hs58a, hs58b, hs3⟩ := hn
  have E := h.2
  have hP := h.1
  have hsp : m.core.get 2 = m₀.core.get 2 := hr.sp
  have keep : ∀ x, ¬ SW (m₀.core.get 2) x → m.ram x = m₀.ram x :=
    fun x hx => hr.ram x (fun h' => hx (recvW_SW _ _ h'))
  have hs3' : m.core.get 19 = ramRead m₀.ram uPtr .w := hs3
  have uS := E.uSep
  have sp24 : ∀ k < 4, ¬ SW (m₀.core.get 2) (m₀.core.get 2 + 0x00000024#32 + BitVec.ofNat 32 k) := by
    intro k hk hw
    have h1 := hP.sp
    have h2 := E.spTop
    unfold SW at hw
    have : (m₀.core.get 2 + 0x00000024#32 + BitVec.ofNat 32 k).toNat = (m₀.core.get 2).toNat + 0x24 + k := by
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat]; simp only [BitVec.toNat_ofNat]; omega
    rw [this] at hw; omega
  have hF : ramRead m.ram (m.core.get 2 + 0x00000024#32) .w = ramRead m₀.ram (m₀.core.get 2 + 0x00000024#32) .w := by
    rw [hsp]; exact rd_keep _ _ _ keep _ sp24
  have hB : ramRead m.ram (m.core.get 19 + 0x0000001c#32) .w = ramRead m₀.ram (ramRead m₀.ram uPtr .w + 0x0000001c#32) .w := by
    rw [hs3']; exact rd_keep _ _ _ keep _ fun k hk => (uS k (by omega)).1
  have s20 : ramRead m₀.ram uPtr .w + 0x00000020#32 = ramRead m₀.ram uPtr .w + 0x0000001c#32 + BitVec.ofNat 32 4 := by
    rw [BitVec.add_assoc]; rfl
  have hS : m.ram (m.core.get 19 + 0x00000020#32) = m₀.ram (ramRead m₀.ram uPtr .w + 0x00000020#32) := by
    rw [hs3', s20]; exact keep _ (uS 4 (by decide)).1
  have fut : ∀ y : Word, ¬ SW (m₀.core.get 2) y → (y.toNat < 0x8002a7b0 ∨ 0x8002a7ca ≤ y.toNat) := by
    intro y hy; unfold SW at hy; omega
  refine ⟨hpc, hr.quiet, hr.s6, hr.s7, by rw [hsp]; exact hP.spAl, by rw [hsp]; exact ⟨hP.sp.1, by have := E.spTop; omega⟩,
    hinv, hc0, hs2, hs4, hdisc, hs9, ⟨hs58a, hs58b⟩, by rw [hB]; exact E.uBase,
    by rw [hs3']; exact E.uBaseIn, by rw [hS]; exact E.uStride, by rw [hs3']; exact E.uStrideIn, ?_,
    by rw [hF]; exact E.flagIn, by rw [hF]; exact E.flagSep⟩
  intro k hk
  rw [hs3']
  refine ⟨fut _ (uS k (by omega)).1, ?_⟩
  rw [s20]; exact fut _ (uS 4 (by decide)).1

/-- The Some point 0x80003e70 (back from `RynkMessage::from_decoded`), with what `recv_step`
proves there and the invariant's extras. -/
structure SomeAt (m : Machine) : Prop where
  pc : m.core.pc = 0x80003e70
  quiet : Quiet m.core
  s6 : m.core.get 22 = s6v
  s7 : m.core.get 23 = s7v
  spAl : (m.core.get 2).toNat % 4 = 0
  sp : 0x8002a798 + 0x70 ≤ (m.core.get 2).toNat ∧ (m.core.get 2).toNat ≤ 0x81000000
  msg : ramRead m.ram msgA .w = bufA ∧
    3 ≤ (ramRead m.ram (msgA + 4) .w).toNat ∧ (ramRead m.ram (msgA + 4) .w).toNat ≤ bufLen ∧
    2 < (ramRead m.ram (msgA + 0xc) .w).toNat ∧ (ramRead m.ram (msgA + 0xc) .w).toNat ≤ bufLen
  emptied : consumed m.ram dfr = 0 ∧ filled m.ram dfr = 0
  parked : (ramRead m.ram 0x8002a798 .w).toNat + 4 ≤ bufLen
  disc : discarding m.ram dfr ≤ 1
  ext : Extras m

/-- Where one round may stop: the loop head with the invariant, or an explicit boundary. -/
def LoopQ (m : Machine) : Prop :=
  (m.core.pc = 0x80003e1a ∧ SessInv m) ∨ m.core.pc = 0x80003ff2 ∨ m.core.pc = 0x80004428 ∨ SomeAt m

theorem lands1_of_qrun_lands {P : Machine → Prop} {k : Nat} {m m' : Machine}
    (h : QRun B img (k + 1) m m') (hl : Lands B img P m') : Lands1 B img P m := by
  obtain ⟨m₁, hq, hd, hrest⟩ := qrun_first h
  refine ⟨hq, (fun o f e => by rw [hd o] at e; cases e), fun x evs hx => ?_⟩
  obtain ⟨rfl, -⟩ := quiet_step hq hd hx
  exact lands_of_qrun_lands hrest hl

/-- The invariant's extras survive a round that writes only `SW` and the flag byte, at the same sp. -/
theorem extras_keep (m₀ x : Machine) (E : Extras m₀)
    (hS0 : 0x8002a798 + 0x70 ≤ (m₀.core.get 2).toNat ∧ (m₀.core.get 2).toNat ≤ 0x81000000) (hsp : x.core.get 2 = m₀.core.get 2)
    (h26 : x.core.get 26 = m₀.core.get 26) (keep : ∀ y, ¬ SW (m₀.core.get 2) y → y ≠ ramRead m₀.ram (m₀.core.get 2 + 0x00000024#32) .w →
      x.ram y = m₀.ram y) : Extras x := by
  have h1 := hS0
  have h2 := E.spTop
  have sp24 : ∀ k < 4, ¬ SW (m₀.core.get 2) (m₀.core.get 2 + 0x00000024#32 + BitVec.ofNat 32 k) := by
    intro k hk hw
    unfold SW at hw
    have : (m₀.core.get 2 + 0x00000024#32 + BitVec.ofNat 32 k).toNat = (m₀.core.get 2).toNat + 0x24 + k := by
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat]; simp only [BitVec.toNat_ofNat]; omega
    rw [this] at hw; omega
  have up : ∀ k < 4, ¬ SW (m₀.core.get 2) (uPtr + BitVec.ofNat 32 k) := by
    intro k hk hw
    unfold SW at hw
    have : (uPtr + BitVec.ofNat 32 k).toNat = 0x8002a784 + k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, show uPtr.toNat = 0x8002a784 from rfl]; omega
    rw [this] at hw; omega
  have fN := E.flagNot
  have hF : ramRead x.ram (x.core.get 2 + 0x00000024#32) .w = ramRead m₀.ram (m₀.core.get 2 + 0x00000024#32) .w := by
    rw [hsp]; exact ramRead_w_congr _ fun k hk => keep _ (sp24 k hk) (fun e => (fN k hk).2 e.symm)
  have hU : ramRead x.ram uPtr .w = ramRead m₀.ram uPtr .w :=
    ramRead_w_congr _ fun k hk => keep _ (up k hk) (fun e => (fN k hk).1 e.symm)
  have uS := E.uSep
  have s20 : ramRead m₀.ram uPtr .w + 0x00000020#32 = ramRead m₀.ram uPtr .w + 0x0000001c#32 + BitVec.ofNat 32 4 := by
    rw [BitVec.add_assoc]; rfl
  refine ⟨by rw [hsp]; exact E.spTop, ?_, by rw [hU]; exact E.uBaseIn, ?_, by rw [hU]; exact E.uStrideIn,
    by rw [hU, hF, hsp]; exact E.uSep, by rw [hF]; exact E.flagIn, by rw [hF]; exact E.flagSep,
    by rw [hF, hsp]; exact E.flagNot, h26.trans E.s10⟩
  · rw [hU, ← E.uBase]; exact ramRead_w_congr _ fun k hk => keep _ (uS k (by omega)).1 (uS k (by omega)).2
  · rw [hU, s20, keep _ (uS 4 (by decide)).1 (uS 4 (by decide)).2, ← s20]; exact E.uStride

/-- **One round of the session loop.** -/
theorem session_round (m₀ : Machine) (h : SessInv m₀) : Lands1 B img LoopQ m₀ := by
  obtain ⟨k, m, r, R⟩ := recv_step' m₀ h.1
  have hpc0 : m₀.core.pc = 0x80003e1a := h.1.pc
  cases k with
  | zero =>
    cases r
    rcases R.out with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [hpc0] at e <;> exact absurd e (by decide)
  | succ j =>
    refine lands1_of_qrun_lands r ?_
    rcases R.out with ⟨hpc, g1, g2, g3, g4, g5, c0, f0, pk, ds⟩ | hn
    · exact .done (.inr (.inr (.inr ⟨hpc, R.quiet, R.s6, R.s7, by rw [R.sp]; exact h.1.spAl,
        by rw [R.sp]; exact h.1.sp, ⟨g1, g2, g3, g4, g5⟩, ⟨c0, f0⟩, pk, ds,
        extras_keep m₀ m h.2 h.1.sp R.sp R.s10 fun y hy _ => R.ram y fun h' => hy (recvW_SW _ _ h')⟩)))
    · have NA := none_of_recv m₀ m h R hn
      refine lands_seq ?_ (none_step m NA)
      rintro x (⟨hS, hxsp, hxram, hx26⟩ | hb | hb)
      · refine .done (.inl ⟨hS.pc, hS, extras_keep m₀ x h.2 h.1.sp (hxsp.trans R.sp) (hx26.trans R.s10) ?_⟩)
        intro y hy hyF
        have hm : ∀ y, ¬ SW (m₀.core.get 2) y → m.ram y = m₀.ram y :=
          fun y hy' => R.ram y (fun h' => hy' (recvW_SW _ _ h'))
        have hFm : ramRead m.ram (m.core.get 2 + 0x00000024#32) .w = ramRead m₀.ram (m₀.core.get 2 + 0x00000024#32) .w := by
          rw [R.sp]
          have h1 := h.1.sp
          have h2 := h.2.spTop
          refine ramRead_w_congr _ fun k hk => hm _ fun hw => ?_
          unfold SW at hw
          have : (m₀.core.get 2 + 0x00000024#32 + BitVec.ofNat 32 k).toNat = (m₀.core.get 2).toNat + 0x24 + k := by
            rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat]; simp only [BitVec.toNat_ofNat]; omega
          rw [this] at hw; omega
        rw [hxram y ?_, hm y hy]
        intro hw
        unfold NW at hw
        rw [hFm, R.sp] at hw
        rcases hw with hw | hw | hw | hw | hw
        · exact hy (.inl hw)
        · exact hy (.inr (.inl hw))
        · exact hy (.inr (.inr (.inr (.inr (.inr (.inl ⟨hw.1, by have := hw.2; omega⟩))))))
        · apply hy; refine .inr (.inr (.inl ?_)); rw [hw]
          have h1 := h.1.sp
          constructor <;> bv_omega
        · exact hyF hw
      · exact .done (.inr (.inl hb))
      · exact .done (.inr (.inr (.inl hb)))

/-- **The end of the Some gap.** From the unpark call site with the same extras, back to the loop
head with `SessInv`. -/
theorem unpark_round (m₀ : Machine) (h : UnparkAt m₀) (E : Extras m₀) :
    ∃ k m, QRun B img k m₀ m ∧ m.core.pc = 0x80003e1a ∧ SessInv m := by
  obtain ⟨k, m, r, hS, hsp, h26, -, hram⟩ := unpark_step' m₀ h
  have h1 := h.sp
  have h2 := E.spTop
  refine ⟨k, m, r, hS.pc, hS, extras_keep m₀ m E h.sp hsp h26 fun y hy _ => hram y fun hw => hy ?_⟩
  unfold SW
  rcases hw with hw | hw | hw
  · exact .inl hw
  · exact .inr (.inl hw)
  · exact .inr (.inr (.inl ⟨by omega, hw.2⟩))

end E5R.Rmk.Deframer.SessionI
