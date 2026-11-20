/-
  The session task's initialization, 0x80003b38 -> 0x80003e1a, on the pinned RMK image: from an
  explicit entry state, every behaviour reaches the session loop head with `SessInv`.

  Original e5r code, Apache-2.0.

  The code sets s10 = s6+0x333 and s11 = s6+0x330, stores the RynkService pointer (s7+0xf1) and the
  two Uart16550 pointers (the async fn's arguments at sp+0x1c and sp+0x18) into the session statics
  (0x8002a780/784/788 and copies at 0x8002a79c/7a0/7a4), copies four service fields to
  0x8002a510.., calls `TopicSubscribers::new` (0x80017552) on 0x8002a530, `memset(bufA, 0, 0x1e8)`,
  and zeroes the deframer (consumed, filled, discarding) and the byte 0x8002a7aa.

  PROVED here: `init_round`: from `InitAt` (pc 0x80003b38, quiet, s6/s7, the stack, the argument
  words, the flag pointer word at sp+0x24 = 0x8002a7c9, and the two UART structs' base/stride; the
  values observed on QEMU virt), assuming the NAMED, undischarged `TopicsNewContract`, every
  behaviour reaches 0x80003e1a with `SessInv`. `memset` is discharged by `Init.memset_words`.

  NOT PROVED: `TopicsNewContract` (760 bytes; RefCell borrows of three PubSub channel statics inside
  critical sections, panics if a channel is borrowed or has too many subscribers); that the task's
  first poll reaches 0x80003b38 with `InitAt` (the executor, main's statics, the poll prologue).
-/
import Projects.rmk.Init.InitSegs
import Projects.rmk.Init.Memset
import Projects.rmk.Deframer.SomeRound

set_option maxRecDepth 100000

namespace E5R.Rmk.Init
open E5R E5R.Rmk E5R.Rmk.Deframer E5R.Rmk.Deframer.Tail E5R.Rmk.Deframer.Session E5R.Rmk.Deframer.SessionI

/-- The entry of the initialization, with the values observed on QEMU virt. -/
structure InitAt (m : Machine) : Prop where
  pc : m.core.pc = 0x80003b38
  quiet : Quiet m.core
  s6 : m.core.get 22 = s6v
  s7 : m.core.get 23 = s7v
  spAl : (m.core.get 2).toNat % 4 = 0
  sp : 0x8002a798 + 0x70 ≤ (m.core.get 2).toNat ∧ (m.core.get 2).toNat + 0x148 ≤ 0x81000000
  /-- the stack lies above the PubSub statics `TopicSubscribers::new` writes (observed sp 0x80fffe10) -/
  spHi : 0x8002b040 ≤ (m.core.get 2).toNat
  rx : ramRead m.ram (m.core.get 2 + 0x0000001c#32) .w = 0x8002a1c0
  txp : ramRead m.ram (m.core.get 2 + 0x00000018#32) .w = 0x8002a1e4
  flag : ramRead m.ram (m.core.get 2 + 0x00000024#32) .w = 0x8002a7c9
  rxBase : ramRead m.ram 0x8002a1dc .w = 0x10000000
  rxStride : (m.ram 0x8002a1e0).toNat = 1
  txBase : ramRead m.ram 0x8002a200 .w = 0x10000000
  txStride : (m.ram 0x8002a204).toNat = 1

/-- The call of `TopicSubscribers::new` at 0x80003df4. -/
structure TopicsEnv (m : Machine) : Prop where
  pc : m.core.pc = 0x80017552
  quiet : Quiet m.core
  ra : m.core.get 1 = 0x80003df8
  self : m.core.get 10 = 0x8002a530
  spAl : (m.core.get 2).toNat % 4 = 0
  sp : 0x8002a798 + 0x70 ≤ (m.core.get 2).toNat ∧ (m.core.get 2).toNat + 0x148 ≤ 0x81000000

/-- What `TopicSubscribers::new` may write: its struct (to msgA), the PubSub statics above the
    session, and its 0x40-byte frame. -/
def TW (sp x : Word) : Prop :=
  (0x8002a530 ≤ x.toNat ∧ x.toNat < 0x8002a580) ∨ (0x8002a800 ≤ x.toNat ∧ x.toNat < 0x8002b000) ∨
  (sp.toNat - 0x40 ≤ x.toNat ∧ x.toNat < sp.toNat)

/-- NOT PROVED: `TopicSubscribers::new` returns, quiet, with the ABI frame, writing only `TW`. -/
def TopicsNewContract : Prop :=
  ∀ m₀, TopicsEnv m₀ → Lands B img (fun m => m.core.pc = 0x80003df8 ∧ Quiet m.core ∧
    (∀ r : Reg, r.val ∉ callerSaved → m.core.get r = m₀.core.get r) ∧
    ∀ x, ¬ TW (m₀.core.get 2) x → m.ram x = m₀.ram x) m₀

/-- Everything the initialization writes (relative to the entry sp). -/
def IW (sp x : Word) : Prop :=
  (0x8002a510 ≤ x.toNat ∧ x.toNat < 0x8002a580) ∨ (0x8002a590 ≤ x.toNat ∧ x.toNat < 0x8002a778) ∨
  (0x8002a780 ≤ x.toNat ∧ x.toNat < 0x8002a7b0) ∨ (0x8002a800 ≤ x.toNat ∧ x.toNat < 0x8002b000) ∨
  (sp.toNat - 0x40 ≤ x.toNat ∧ x.toNat < sp.toNat)


/-- The later writes (after the pointer stores): `IW` without the three pointer words. -/
def JW (sp x : Word) : Prop :=
  (0x8002a510 ≤ x.toNat ∧ x.toNat < 0x8002a580) ∨ (0x8002a590 ≤ x.toNat ∧ x.toNat < 0x8002a778) ∨
  (0x8002a78c ≤ x.toNat ∧ x.toNat < 0x8002a7b0) ∨ (0x8002a800 ≤ x.toNat ∧ x.toNat < 0x8002b000) ∨
  (sp.toNat - 0x40 ≤ x.toNat ∧ x.toNat < sp.toNat)

theorem jw_iw (sp x : Word) (h : JW sp x) : IW sp x := by unfold JW at h; unfold IW; omega

/-- The state between the pointer stores and the loop head. -/
structure IS (c : Core) (M : Word → BitVec 8) (m : Machine) : Prop where
  quiet : Quiet m.core
  sp : m.core.get 2 = c.get 2
  s6 : m.core.get 22 = s6v
  s7 : m.core.get 23 = s7v
  s10 : m.core.get 26 = 0x8002a7f0
  frame : ∀ x, ¬ IW (c.get 2) x → m.ram x = M x
  svc : ramRead m.ram 0x8002a780 .w = 0x8002a4c0
  rxp : ramRead m.ram 0x8002a784 .w = 0x8002a1c0
  txp : ramRead m.ram 0x8002a788 .w = 0x8002a1e4

theorem w3_keep (R R' : Word → BitVec 8) (sp : Word) (hs : 0x8002a798 + 0x70 ≤ sp.toNat) (hk : ∀ x, ¬ JW sp x → R' x = R x) (a : Word)
    (ha : 0x8002a780 ≤ a.toNat ∧ a.toNat + 4 ≤ 0x8002a78c) : ramRead R' a .w = ramRead R a .w :=
  ramRead_w_congr _ fun k hk' => hk _ (by
    have : (a + BitVec.ofNat 32 k).toNat = a.toNat + k := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    unfold JW; rw [this]; omega)

theorem is_step {c : Core} {M : Word → BitVec 8} {e e' : Core} {R R' : Word → BitVec 8}
    (hs : 0x8002a798 + 0x70 ≤ (c.get 2).toNat) (h : IS c M ⟨e, R⟩)
    (q : Quiet e') (g2 : e'.get 2 = e.get 2) (g22 : e'.get 22 = e.get 22) (g23 : e'.get 23 = e.get 23)
    (g26 : e'.get 26 = e.get 26) (hk : ∀ x, ¬ JW (c.get 2) x → R' x = R x) : IS c M ⟨e', R'⟩ :=
  ⟨q, g2.trans h.sp, g22.trans h.s6, g23.trans h.s7, g26.trans h.s10,
    fun x hx => (hk x fun hj => hx (jw_iw _ _ hj)).trans (h.frame x hx),
    (w3_keep _ _ _ hs hk _ (by decide)).trans h.svc, (w3_keep _ _ _ hs hk _ (by decide)).trans h.rxp,
    (w3_keep _ _ _ hs hk _ (by decide)).trans h.txp⟩

theorem rd_lit (M : Word → BitVec 8) (a v b : Word) (wd : Width) (ha : a.toNat + 4 ≤ 2 ^ 32)
    (hb : b.toNat + 4 ≤ 2 ^ 32) (h : b.toNat + 4 ≤ a.toNat ∨ a.toNat + 4 ≤ b.toNat) :
    ramRead (ramWrite M a v wd) b .w = ramRead M b .w := rd_wr_far M a v b wd ha hb h

/-- **The initialization**, against the named `TopicsNewContract`; `memset` is proved. -/
theorem init_round (hT : TopicsNewContract) (m₀ : Machine) (h : InitAt m₀) :
    Lands B img (fun m => m.core.pc = 0x80003e1a ∧ SessInv m) m₀ := by
  obtain ⟨c, M⟩ := m₀
  have h22 : c.get 22 = s6v := h.s6
  have h23 : c.get 23 = s7v := h.s7
  have hs : 0x8002a798 + 0x70 ≤ (c.get 2).toNat ∧ (c.get 2).toNat + 0x148 ≤ 0x81000000 := h.sp
  have hs1 := hs.1
  have hs2 := hs.2
  have hA : (c.get 2).toNat % 4 = 0 := h.spAl
  have hsH : 0x8002b040 ≤ (c.get 2).toNat := h.spHi
  -- the pointer copies and the argument loads
  have r1 := iA c M h.pc h.quiet (by rw [h22]; decide) (by rw [h22]; decide)
    (by rw [SomeP.spOff _ _ (by omega)]; omega) (SomeP.spIn _ _ _ (by omega) (by omega))
    (by rw [h22]; decide) (by rw [h22]; decide)
    (by rw [SomeP.spOff _ _ (by omega)]; omega) (SomeP.spIn _ _ _ (by omega) (by omega))
    (by rw [h22]; decide) (by rw [h22]; decide) (by rw [h22]; decide) (by rw [h22]; decide)
  have far : ∀ (o : Nat), o < 0x40 → ∀ (b : Word), 0x8002a000 ≤ b.toNat → b.toNat + 4 ≤ 0x8002a800 →
      (c.get 2 + BitVec.ofNat 32 o).toNat + 4 ≤ b.toNat ∨ b.toNat + 4 ≤ (c.get 2 + BitVec.ofNat 32 o).toNat := by
    intro o ho b hb1 hb2; rw [SomeP.spOff _ _ (by omega)]; omega
  have a10 : (iACore c M).get 10 = 0x8002a4c0 := by
    simp [iACore, Core.wr_get_ne, Core.wr_get_self, alu_add, h23]; rfl
  have a12 : (iACore c M).get 12 = 0x8002a1c0 := by
    simp only [iACore, Core.goto_get, Core.wr_get_ne _ _ _ _ _ (show (12 : Reg) ≠ 11 by decide),
      Core.wr_get_self _ _ _ _ (show (12 : Reg).val ≠ 0 by decide), h22]
    rw [rd_lit _ _ _ _ _ (by decide) (by rw [SomeP.spOff _ _ (by omega)]; omega)
      (by rw [show (s6v + 0x000002df#32).toNat = 0x8002a79c from rfl]; exact far 0x1c (by decide) 0x8002a79c (by decide) (by decide))]
    exact h.rx

  have a11 : (iACore c M).get 11 = 0x8002a1e4 := by
    simp only [iACore, Core.goto_get, Core.wr_get_self _ _ _ _ (show (11 : Reg).val ≠ 0 by decide), h22]
    rw [rd_lit _ _ _ _ _ (by decide) (by rw [SomeP.spOff _ _ (by omega)]; omega)
      (by rw [show (s6v + 0x000002e3#32).toNat = 0x8002a7a0 from rfl]; exact far 0x18 (by decide) 0x8002a7a0 (by decide) (by decide)),
      rd_lit _ _ _ _ _ (by decide) (by rw [SomeP.spOff _ _ (by omega)]; omega)
      (by rw [show (s6v + 0x000002df#32).toNat = 0x8002a79c from rfl]; exact far 0x18 (by decide) 0x8002a79c (by decide) (by decide))]
    exact h.txp
  have a2 : (iACore c M).get 2 = c.get 2 := by simp [iACore, Core.wr_get_ne]
  have a22 : (iACore c M).get 22 = s6v := by simp [iACore, Core.wr_get_ne, h22]
  have a23 : (iACore c M).get 23 = s7v := by simp [iACore, Core.wr_get_ne, h23]
  have a26 : (iACore c M).get 26 = 0x8002a7f0 := by simp [iACore, Core.wr_get_ne, Core.wr_get_self, alu_add, h22]; rfl
  have fA : ∀ x, ¬ IW (c.get 2) x → iARam c M x = M x := by
    intro x hx; unfold IW at hx; simp only [iARam, h22]
    rw [SomeP.wr_other _ _ _ _ _ (by decide) (by rw [show (s6v + 0x000002ee#32).toNat = 0x8002a7ab from rfl]; omega),
      SomeP.wr_other _ _ _ _ _ (by decide) (by rw [show (s6v + 0x000002e7#32).toNat = 0x8002a7a4 from rfl]; omega),
      SomeP.wr_other _ _ _ _ _ (by decide) (by rw [show (s6v + 0x000002e3#32).toNat = 0x8002a7a0 from rfl]; omega),
      SomeP.wr_other _ _ _ _ _ (by decide) (by rw [show (s6v + 0x000002df#32).toNat = 0x8002a79c from rfl]; omega)]
  have qA : Quiet (iACore c M) := Quiet.of_sameCsr (iACsr c M) h.quiet
  have pA : (iACore c M).pc = 0x80003da6 := rfl
  generalize iACore c M = A at r1 a10 a11 a12 a2 a22 a23 a26 qA pA
  generalize iARam c M = RA at r1 fA
  refine lands_of_qrun_lands r1 ?_
  -- the pointer stores
  have r2 := iB A RA pA qA (by rw [a22]; decide) (by rw [a22]; decide) (by rw [a22]; decide) (by rw [a22]; decide)
    (by rw [a22]; decide) (by rw [a22]; decide) (by rw [a10]; decide) (by rw [a10]; decide) (by rw [a10]; decide)
    (by rw [a10]; decide) (by rw [a10]; decide) (by rw [a10]; decide) (by rw [a10]; decide) (by rw [a10]; decide)
  have fB : ∀ x, ¬ IW (c.get 2) x → iBRam A RA x = M x := by
    intro x hx; refine Eq.trans ?_ (fA x hx); unfold IW at hx; simp only [iBRam, a22]
    rw [SomeP.wr_other _ _ _ _ _ (by decide) (by rw [show (s6v + 0x000002cb#32).toNat = 0x8002a788 from rfl]; omega),
      SomeP.wr_other _ _ _ _ _ (by decide) (by rw [show (s6v + 0x000002c7#32).toNat = 0x8002a784 from rfl]; omega),
      SomeP.wr_other _ _ _ _ _ (by decide) (by rw [show (s6v + 0x000002c3#32).toNat = 0x8002a780 from rfl]; omega)]
  have wB : ∀ v : Word, ramRead (iBRam A RA) 0x8002a780 .w = A.get 10 ∧ ramRead (iBRam A RA) 0x8002a784 .w = A.get 12 ∧
      ramRead (iBRam A RA) 0x8002a788 .w = A.get 11 := by
    intro _
    simp only [iBRam, a22]
    rw [show s6v + 0x000002c3#32 = (0x8002a780 : Word) from rfl, show s6v + 0x000002c7#32 = (0x8002a784 : Word) from rfl,
      show s6v + 0x000002cb#32 = (0x8002a788 : Word) from rfl]
    refine ⟨?_, ?_, ramRead_ramWrite_w _ _ _⟩
    · rw [rd_lit _ _ _ _ _ (by decide) (by decide) (by decide), rd_lit _ _ _ _ _ (by decide) (by decide) (by decide),
        ramRead_ramWrite_w]
    · rw [rd_lit _ _ _ _ _ (by decide) (by decide) (by decide), ramRead_ramWrite_w]
  obtain ⟨w0, w1, w2⟩ := wB 0
  have IB : IS c M ⟨iBCore A RA, iBRam A RA⟩ :=
    ⟨Quiet.of_sameCsr (iBCsr A RA) qA, by simp [iBCore, Core.wr_get_ne, a2], by simp [iBCore, Core.wr_get_ne, a22],
      by simp [iBCore, Core.wr_get_ne, a23], by simp [iBCore, Core.wr_get_ne, a26], fB,
      w0.trans a10, w1.trans a12, w2.trans a11⟩
  have b22 : (iBCore A RA).get 22 = s6v := IB.s6
  have b23 : (iBCore A RA).get 23 = s7v := IB.s7
  have pB : (iBCore A RA).pc = 0x80003dc4 := rfl
  generalize iBCore A RA = Bc at r2 IB b22 b23 pB
  generalize iBRam A RA = RB at r2 IB
  refine lands_of_qrun_lands r2 ?_
  -- the service field copies and the call of TopicSubscribers::new
  have r3 := iC Bc RB pB IB.quiet
    (by rw [b22]; decide) (by rw [b22]; decide) (by rw [b22]; decide) (by rw [b22]; decide) (by rw [b22]; decide)
    (by rw [b22]; decide) (by rw [b22]; decide) (by rw [b22]; decide) (by rw [b22]; decide) (by rw [b22]; decide)
    (by rw [b22]; decide) (by rw [b22]; decide) (by rw [b22]; decide) (by rw [b22]; decide) (by rw [b22]; decide)
    (by rw [b22]; decide) (by rw [b22]; decide) (by rw [b22]; decide) (by rw [b22]; decide) (by rw [b22]; decide)
  have kC : ∀ x, ¬ JW (c.get 2) x → iCRam Bc RB x = RB x := by
    intro x hx; unfold JW at hx; simp only [iCRam, b22]
    rw [SomeP.wr_other _ _ _ _ _ (by decide) (by rw [show (s6v + 0x00000071#32).toNat = 0x8002a52e from rfl]; omega),
      SomeP.wr_other _ _ _ _ _ (by decide) (by rw [show (s6v + 0x00000070#32).toNat = 0x8002a52d from rfl]; omega),
      SomeP.wr_other _ _ _ _ _ (by decide) (by rw [show (s6v + 0x0000006f#32).toNat = 0x8002a52c from rfl]; omega),
      SomeP.wr_other _ _ _ _ _ (by decide) (by rw [show (s6v + 0x0000006b#32).toNat = 0x8002a528 from rfl]; omega),
      SomeP.wr_other _ _ _ _ _ (by decide) (by rw [show (s6v + 0x00000067#32).toNat = 0x8002a524 from rfl]; omega),
      SomeP.wr_other _ _ _ _ _ (by decide) (by rw [show (s6v + 0x00000063#32).toNat = 0x8002a520 from rfl]; omega),
      SomeP.wr_other _ _ _ _ _ (by decide) (by rw [show (s6v + 0x0000005f#32).toNat = 0x8002a51c from rfl]; omega),
      SomeP.wr_other _ _ _ _ _ (by decide) (by rw [show (s6v + 0x0000005b#32).toNat = 0x8002a518 from rfl]; omega),
      SomeP.wr_other _ _ _ _ _ (by decide) (by rw [show (s6v + 0x00000057#32).toNat = 0x8002a514 from rfl]; omega),
      SomeP.wr_other _ _ _ _ _ (by decide) (by rw [show (s6v + 0x00000053#32).toNat = 0x8002a510 from rfl]; omega)]
  have IC : IS c M ⟨iCCore Bc RB, iCRam Bc RB⟩ := is_step hs1 IB (Quiet.of_sameCsr (iCCsr Bc RB) IB.quiet)
    (by simp [iCCore, Core.wr_get_ne]) (by simp [iCCore, Core.wr_get_ne]) (by simp [iCCore, Core.wr_get_ne])
    (by simp [iCCore, Core.wr_get_ne]) kC
  have env : TopicsEnv ⟨iCCore Bc RB, iCRam Bc RB⟩ :=
    ⟨rfl, IC.quiet, by simp [iCCore, Core.wr_get_self], by simp [iCCore, Core.wr_get_ne, Core.wr_get_self, alu_add, b23]; rfl,
      by show (_ : Word).toNat % 4 = 0; rw [IC.sp]; exact hA, by show _ ∧ _; rw [IC.sp]; exact hs⟩
  generalize iCCore Bc RB = Cc at r3 IC env
  generalize iCRam Bc RB = RC at r3 IC env
  refine lands_of_qrun_lands r3 (lands_seq ?_ (hT _ env))
  rintro ⟨e1, M1⟩ ⟨p1, q1, s1, k1⟩
  have k1' : ∀ x, ¬ JW (c.get 2) x → M1 x = RC x := fun x hx => k1 x (by
    show ¬ TW (Cc.get 2) x; rw [IC.sp]; unfold TW; unfold JW at hx; omega)
  have I1 : IS c M ⟨e1, M1⟩ := is_step hs1 IC q1 (s1 2 (by decide)) (s1 22 (by decide)) (s1 23 (by decide))
    (s1 26 (by decide)) k1'
  -- memset(bufA, 0, 0x1e8)
  have r4 := iMid e1 M1 p1 q1
  have mE : Init.MemsetEnv ⟨iMidCore e1 M1, iMidRam e1 M1⟩ :=
    ⟨rfl, Quiet.of_sameCsr (iMidCsr e1 M1) q1, by simp [iMidCore, Core.wr_get_self],
      by simp [iMidCore, Core.wr_get_ne, Core.wr_get_self, alu_add, I1.s7]; decide,
      by simp [iMidCore, Core.wr_get_ne, Core.wr_get_self, alu_add],
      by simp [iMidCore, Core.wr_get_ne, Core.wr_get_self, alu_add, I1.s7]; decide⟩
  have IM : IS c M ⟨iMidCore e1 M1, iMidRam e1 M1⟩ := is_step hs1 I1 mE.quiet
    (by simp [iMidCore, Core.wr_get_ne]) (by simp [iMidCore, Core.wr_get_ne]) (by simp [iMidCore, Core.wr_get_ne])
    (by simp [iMidCore, Core.wr_get_ne]) (fun _ _ => rfl)
  have d10 : (iMidCore e1 M1).get 10 = 0x8002a590 := by simp [iMidCore, Core.wr_get_ne, Core.wr_get_self, alu_add, I1.s7]; rfl
  have d12 : (iMidCore e1 M1).get 12 = 0x1e8 := by simp [iMidCore, Core.wr_get_ne, Core.wr_get_self, alu_add]
  have d1 : (iMidCore e1 M1).get 1 = 0x80003e0a := by simp [iMidCore, Core.wr_get_self]
  generalize iMidCore e1 M1 = Dc at r4 mE IM d10 d12 d1
  generalize iMidRam e1 M1 = RD at r4 mE IM
  refine lands_of_qrun_lands r4 (lands_seq ?_ (memset_words _ mE))
  rintro ⟨e2, M2⟩ P
  have p2 : e2.pc = 0x80003e0a := P.pc.trans d1
  have k2 : ∀ x, ¬ JW (c.get 2) x → M2 x = RD x := fun x hx => P.ram x (by
    show ¬ ((Dc.get 10).toNat ≤ x.toNat ∧ x.toNat < (Dc.get 10).toNat + (Dc.get 12).toNat)
    rw [d10, d12, show (0x8002a590 : Word).toNat = 0x8002a590 from rfl, show (0x1e8 : Word).toNat = 0x1e8 from rfl]
    unfold JW at hx; omega)
  have I2 : IS c M ⟨e2, M2⟩ := is_step hs1 IM P.quiet (P.saved 2 (by decide)) (P.saved 22 (by decide))
    (P.saved 23 (by decide)) (P.saved 26 (by decide)) k2
  have e22 : e2.get 22 = s6v := I2.s6
  -- the deframer reset, to the loop head
  have r5 := iPost e2 M2 p2 I2.quiet (by rw [e22]; decide) (by rw [e22]; decide) (by rw [e22]; decide)
    (by rw [e22]; decide) (by rw [e22]; decide) (by rw [e22]; decide) (by rw [e22]; decide) (by rw [e22]; decide)
  have kP : ∀ x, ¬ JW (c.get 2) x → iPostRam e2 M2 x = M2 x := by
    intro x hx; unfold JW at hx; simp only [iPostRam, e22]
    rw [SomeP.wr_other _ _ _ _ _ (by decide) (by rw [show (s6v + 0x000002ed#32).toNat = 0x8002a7aa from rfl]; omega),
      SomeP.wr_other _ _ _ _ _ (by decide) (by rw [show (s6v + 0x000002d7#32).toNat = 0x8002a794 from rfl]; omega),
      SomeP.wr_other _ _ _ _ _ (by decide) (by rw [show (s6v + 0x000002d3#32).toNat = 0x8002a790 from rfl]; omega),
      SomeP.wr_other _ _ _ _ _ (by decide) (by rw [show (s6v + 0x000002cf#32).toNat = 0x8002a78c from rfl]; omega)]
  have IF : IS c M ⟨iPostCore e2 M2, iPostRam e2 M2⟩ := is_step hs1 I2 (Quiet.of_sameCsr (iPostCsr e2 M2) I2.quiet)
    rfl rfl rfl rfl kP
  have hc0 : ramRead (iPostRam e2 M2) dfr .w = 0 := by
    simp only [iPostRam, e22]
    rw [rd_lit _ _ _ _ _ (by decide) (by decide) (by decide), rd_lit _ _ _ _ _ (by decide) (by decide) (by decide),
      rd_lit _ _ _ _ _ (by decide) (by decide) (by decide), show s6v + 0x000002cf#32 = dfr from rfl, ramRead_ramWrite_w]
  have hf0 : ramRead (iPostRam e2 M2) (dfr + 4) .w = 0 := by
    simp only [iPostRam, e22]
    rw [rd_lit _ _ _ _ _ (by decide) (by decide) (by decide), rd_lit _ _ _ _ _ (by decide) (by decide) (by decide),
      show s6v + 0x000002d3#32 = dfr + 4 from rfl, ramRead_ramWrite_w]
  have hd0 : iPostRam e2 M2 (dfr + 8) = 0 := by
    simp only [iPostRam, e22]
    rw [SomeP.wr_other _ _ _ _ _ (by decide) (by decide), show s6v + 0x000002d7#32 = dfr + 8 from rfl]
    simp [ramWrite, ramPut, byteOf]
  have pF : (iPostCore e2 M2).pc = 0x80003e1a := rfl
  generalize iPostCore e2 M2 = F at r5 IF pF
  generalize iPostRam e2 M2 = RF at r5 IF hc0 hf0 hd0
  refine lands_of_qrun r5 ⟨pF, ?_⟩
  have fr := IF.frame
  have F2 : F.get 2 = c.get 2 := IF.sp
  have lowb : ∀ a : Word, a.toNat < 0x8002a510 → RF a = M a := fun a ha => fr a (by unfold IW; omega)
  have lowv : ∀ a : Word, a.toNat + 4 ≤ 0x8002a510 → ramRead RF a .w = ramRead M a .w := fun a ha =>
    ramRead_w_congr _ fun k hk => lowb _ (by rw [SomeP.spOff _ _ (by omega)]; omega)
  have flagv : ramRead RF (F.get 2 + 0x00000024#32) .w = 0x8002a7c9 := by
    rw [F2, ← h.flag]
    refine ramRead_w_congr _ fun k hk => fr _ ?_
    unfold IW
    rw [SomeP.spOff _ _ (by rw [SomeP.spOff _ _ (by omega)]; omega), SomeP.spOff _ _ (by omega)]; omega
  have uP : ramRead RF uPtr .w = 0x8002a1c0 := IF.rxp
  have nz : ∀ (a : Word) (k : Nat), a.toNat + k < 2 ^ 32 → (a + BitVec.ofNat 32 k).toNat = a.toNat + k :=
    fun a k h => SomeP.spOff a k h
  refine ⟨⟨pF, IF.quiet, IF.s6, IF.s7, by rw [F2]; exact hA, by rw [F2]; exact ⟨hs1, by omega⟩, ?_, ?_⟩,
    ⟨by rw [F2]; exact hs2, ?_, by rw [uP]; decide, ?_, by rw [uP]; decide, ?_, by rw [flagv]; decide,
      by rw [flagv]; decide, ?_, IF.s10, IF.svc, IF.txp, ?_, ?_, ?_⟩⟩
  · show consumed RF dfr ≤ filled RF dfr ∧ filled RF dfr ≤ bufLen
    unfold consumed filled word; rw [hc0, hf0]; decide
  · show (RF (dfr + 8)).toNat ≤ 1
    rw [hd0]; decide
  · rw [uP, show (0x8002a1c0 : Word) + 0x0000001c#32 = 0x8002a1dc from rfl, lowv _ (by decide)]; exact h.rxBase
  · rw [uP, show (0x8002a1c0 : Word) + 0x00000020#32 = 0x8002a1e0 from rfl]
    show (RF 0x8002a1e0).toNat = 1
    rw [lowb 0x8002a1e0 (by decide)]; exact h.rxStride
  · intro k hk
    rw [uP, flagv, F2, show (0x8002a1c0 : Word) + 0x0000001c#32 = 0x8002a1dc from rfl]
    have e1 := nz 0x8002a1dc k (by rw [show (0x8002a1dc : Word).toNat = 0x8002a1dc from rfl]; omega)
    rw [show (0x8002a1dc : Word).toNat = 0x8002a1dc from rfl] at e1
    refine ⟨fun hw => ?_, fun e => ?_⟩
    · unfold SW at hw; rw [e1] at hw; omega
    · have := congrArg BitVec.toNat e; rw [e1, show (0x8002a7c9 : Word).toNat = 0x8002a7c9 from rfl] at this; omega
  · intro k hk
    rw [flagv, F2]
    refine ⟨fun e => ?_, fun e => ?_⟩
    · have := congrArg BitVec.toNat e
      rw [nz _ _ (by rw [show uPtr.toNat = 0x8002a784 from rfl]; omega), show uPtr.toNat = 0x8002a784 from rfl,
        show (0x8002a7c9 : Word).toNat = 0x8002a7c9 from rfl] at this; omega
    · have := congrArg BitVec.toNat e
      rw [nz _ _ (by rw [SomeP.spOff _ _ (by omega)]; omega), SomeP.spOff _ _ (by omega),
        show (0x8002a7c9 : Word).toNat = 0x8002a7c9 from rfl] at this; omega
  · rw [lowv _ (by decide)]; exact h.txBase
  · show (RF 0x8002a204).toNat = 1
    rw [lowb 0x8002a204 (by decide)]; exact h.txStride
  · rw [flagv]
    refine ⟨fun k hk e => ?_, fun k hk e => ?_⟩
    · have := congrArg BitVec.toNat e
      rw [nz _ _ (by rw [show (0x8002a780 : Word).toNat = 0x8002a780 from rfl]; omega),
        show (0x8002a780 : Word).toNat = 0x8002a780 from rfl, show (0x8002a7c9 : Word).toNat = 0x8002a7c9 from rfl] at this
      omega
    · have := congrArg BitVec.toNat e
      rw [nz _ _ (by rw [show (0x8002a200 : Word).toNat = 0x8002a200 from rfl]; omega),
        show (0x8002a200 : Word).toNat = 0x8002a200 from rfl, show (0x8002a7c9 : Word).toNat = 0x8002a7c9 from rfl] at this
      omega

end E5R.Rmk.Init
