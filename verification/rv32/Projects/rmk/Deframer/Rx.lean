/-
  The session's UART receive poll (0x80004374..0x800043a8, the None path's read of incoming bytes)
  on the pinned RMK image: EVERY behaviour, for every value the UART's LSR and RBR registers return.

  Original e5r code, Apache-2.0.

  The loop: `assert_offset(5)`; read LSR (0x10000005); if bit 0 (data ready) is clear, stop; else
  `assert_offset(0)`, read RBR (0x10000000) into buf[i], i += 1, and go on while i ≠ cap.

  PROVED here: `rx_loop`: from the loop head with i < cap (`RxAt`), every behaviour of `Step`
  (each device value is the environment's, quantified over all of them) reaches the exit 0x800043a8
  (`RxOut`), never faulting and never taking an interrupt on the way (`Lands`), with i ≤ cap, every
  register outside a0-a2, s0, s1, ra as at the loop's entry, and RAM changed only in
  buf[dst .. dst+cap) and the one stack byte `assert_offset` writes.

  EXPLICIT PRECONDITIONS (`RxEnv`): s3/s5 hold the UART's RBR/LSR addresses (they are read from the
  `Uart16550` struct in RAM by 0x80004362..0x8000436a; that struct's contents are an assumption here,
  not proved), cap ≥ 1, the destination range and the stack byte are in RAM, the core is quiet at
  entry. Not proved: the code before 0x80004374 and after 0x800043a8, the executor, interrupts.
-/
import Projects.rmk.DevRead
import Projects.rmk.Deframer.RxSegs

set_option maxRecDepth 100000

namespace E5R.Rmk.Deframer.Rx
open E5R E5R.Rmk E5R.Rmk.RxFetch E5R.Rmk.Deframer.Tail

/-- The loop's entry facts, about the core c0 that first reaches 0x80004374. -/
structure RxEnv (c0 : Core) : Prop where
  rbr : c0.get 19 = 0x10000000
  lsr : c0.get 21 = 0x10000005
  cap : 1 ≤ (c0.get 20).toNat
  dst : B.inRam (c0.get 18) (c0.get 20).toNat = true
  stk : B.inRam (c0.get 2 + 0xffffffe0#32 + 0x0000000f#32) 1 = true

/-- The registers the loop writes: ra, s0, s1, a0, a1, a2. -/
def rxW : List Nat := [1, 8, 9, 10, 11, 12]

/-- RAM the loop may change, relative to the entry RAM. -/
def RxRam (c0 : Core) (M0 M : Word → BitVec 8) (n : Nat) : Prop :=
  ∀ x : Word, ¬ ((c0.get 18).toNat ≤ x.toNat ∧ x.toNat < (c0.get 18).toNat + n) →
    x ≠ c0.get 2 + 0xffffffe0#32 + 0x0000000f#32 → M x = M0 x

structure RxAt (c0 : Core) (M0 : Word → BitVec 8) (e : Core) (M : Word → BitVec 8) (i : Nat) : Prop where
  pc : e.pc = 0x80004374
  quiet : Quiet e
  regs : ∀ r : Reg, r.val ∉ rxW → e.get r = c0.get r
  iv : e.get 9 = BitVec.ofNat 32 i
  lt : i < (c0.get 20).toNat
  ram : RxRam c0 M0 M i

def RxOut (c0 : Core) (M0 : Word → BitVec 8) (m : Machine) : Prop :=
  m.core.pc = 0x800043a8 ∧ Quiet m.core ∧ (∀ r : Reg, r.val ∉ rxW → m.core.get r = c0.get r) ∧
    (m.core.get 9).toNat ≤ (c0.get 20).toNat ∧ RxRam c0 M0 m.ram (c0.get 20).toNat

theorem rbr_none : romRead? img (0x10000000 : Word).toNat 1 false = none := rom_none _ (by decide)
theorem lsr_none : romRead? img (0x10000005 : Word).toNat 1 false = none := rom_none _ (by decide)

theorem lsr_dev : B.device? 0x10000005 = some ⟨0x10000005, "uart0.lsr", true, false, 1⟩ := by decide
theorem rbr_dev : B.device? 0x10000000 = some ⟨0x10000000, "uart0.rbr_thr_dll", true, true, 1⟩ := by decide

theorem not_w {r : Reg} {k : Nat} (h : r.val ∉ rxW) (hk : k ∈ rxW) : r ≠ ⟨k % 32, Nat.mod_lt _ (by decide)⟩ := by
  intro e; subst e; simp only [rxW, List.mem_cons, List.not_mem_nil, or_false] at h hk; omega

theorem sp_back (s : Word) : alu .add (alu .add s 0xffffffe0#32) 0x00000020#32 = s := by
  simp only [alu_add]; bv_omega

theorem rx_loop (c0 : Core) (M0 : Word → BitVec 8) (E : RxEnv c0) :
    ∀ k i (e : Core) (M : Word → BitVec 8), (c0.get 20).toNat - i = k → RxAt c0 M0 e M i →
      Lands B img (RxOut c0 M0) ⟨e, M⟩ := by
  intro k
  induction k with
  | zero => intro i e M hk h; have := h.lt; omega
  | succ k ih =>
    intro i e M hk h
    have hdst := (B_ram _ _).mp E.dst
    have hcap := E.cap
    have hlt := h.lt
    have eg : ∀ r : Reg, r.val ∉ rxW → e.get r = c0.get r := h.regs
    have e2 : e.get 2 = c0.get 2 := eg 2 (by decide)
    have e18 : e.get 18 = c0.get 18 := eg 18 (by decide)
    have e19 : e.get 19 = 0x10000000 := (eg 19 (by decide)).trans E.rbr
    have e20 : e.get 20 = c0.get 20 := eg 20 (by decide)
    have e21 : e.get 21 = 0x10000005 := (eg 21 (by decide)).trans E.lsr
    -- assert_offset(5)
    have r1 := rxA e M h.pc h.quiet
    let A := rxACore e M
    have csA : A.sameCsr e := by
      unfold A rxACore
      repeat (first | exact Core.sameCsr_wr _ _ _ _ | exact Core.sameCsr_goto _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_)
    have qA : Quiet A := Quiet.of_sameCsr csA h.quiet
    have A10 : A.get 10 = alu .add 0 0x00000005#32 := by simp [A, rxACore, Core.wr_get_ne, Core.wr_get_self]
    have A1 : A.get 1 = 0x80004380 := by simp [A, rxACore, Core.wr_get_self]
    have gA : ∀ r : Reg, r ≠ 1 → r ≠ 10 → r ≠ 11 → A.get r = e.get r := fun r a b c' => by
      simp [A, rxACore, Core.wr_get_ne, a, b, c']
    have A2 : A.get 2 = c0.get 2 := (gA 2 (by decide) (by decide) (by decide)).trans e2
    have r2 := aoff A M rfl qA (Nat.mod_one _) (by rw [A2]; exact E.stk)
      (by rw [A10]; decide) (by rw [A1]; decide)
    let A' := aoffCore A M
    let M2 := aoffRam A M
    have csA' : A'.sameCsr A := by
      unfold A' aoffCore
      repeat (first | exact Core.sameCsr_wr _ _ _ _ | exact Core.sameCsr_goto _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_)
    have qA' : Quiet A' := Quiet.of_sameCsr csA' qA
    have A'pc : A'.pc = 0x80004380 := by simp only [A', aoffCore, Core.goto_pc]; exact A1
    have gA' : ∀ r : Reg, r ≠ 2 → r ≠ 11 → r ≠ 12 → A'.get r = A.get r := fun r a b c' => by
      simp [A', aoffCore, Core.wr_get_ne, a, b, c']
    have A'2 : A'.get 2 = c0.get 2 := by
      simp only [A', aoffCore, Core.goto_get, Core.wr_get_self _ _ _ _ (show (2 : Reg).val ≠ 0 by decide)]
      rw [sp_back, A2]
    have M2o : ∀ x : Word, x ≠ c0.get 2 + 0xffffffe0#32 + 0x0000000f#32 → M2 x = M x := by
      intro x hx; show ramWrite M _ _ .b x = M x; rw [ramWrite, ramPut_ne _ (by rw [A2]; exact hx)]
    -- registers outside rxW after assert_offset: as at entry
    have kA' : ∀ r : Reg, r.val ∉ rxW → A'.get r = c0.get r := by
      intro r hr
      by_cases h2 : r = 2
      · subst h2; exact A'2
      · rw [gA' r h2 (fun e => by subst e; exact absurd hr (by decide)) (fun e => by subst e; exact absurd hr (by decide)),
          gA r (fun e => by subst e; exact absurd hr (by decide)) (fun e => by subst e; exact absurd hr (by decide))
            (fun e => by subst e; exact absurd hr (by decide))]
        exact eg r hr
    refine lands_of_qrun_lands (r1.trans r2) ?_
    -- read LSR
    refine lands_lbu_dev (rd := 10) (rs1 := 21) (off := 0x00000000#32) (len := 0x00000004#32)
      (by rw [A'pc]; decide) (by rw [A'pc]; exact f80004380)
      (by rw [kA' 21 (by decide), E.lsr]; rfl) (by decide) lsr_none lsr_dev rfl rfl qA' fun v => ?_
    let D := A'.wr 10 (extend .b false (devVal .b v)) (A'.pc + 0x00000004#32)
    have qD : Quiet D := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) qA'
    have Dpc : D.pc = 0x80004384 := by simp only [D, Core.wr_pc, A'pc]; rfl
    have kD : ∀ r : Reg, r.val ∉ rxW → D.get r = c0.get r := fun r hr => by
      rw [show D.get r = A'.get r from Core.wr_get_ne _ _ _ _ _ (fun e => by subst e; exact absurd hr (by decide))]
      exact kA' r hr
    have D9 : D.get 9 = BitVec.ofNat 32 i := by
      simp only [D, Core.wr_get_ne _ _ _ _ _ (show (9 : Reg) ≠ 10 by decide)]
      rw [gA' 9 (by decide) (by decide) (by decide), gA 9 (by decide) (by decide) (by decide)]; exact h.iv
    by_cases hz : alu .and (D.get 10) 0x00000001#32 = 0
    · -- no data: the exit
      have r3 := rxNo D M2 Dpc qD (by rw [hz]; rfl)
      refine lands_of_qrun r3 ⟨rfl, Quiet.of_sameCsr (by
        unfold rxNoCore
        repeat (first | exact Core.sameCsr_wr _ _ _ _ | exact Core.sameCsr_goto _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_)) qD, ?_, ?_, ?_⟩
      · intro r hr
        have hne : r ≠ 10 := fun e => by subst e; exact absurd hr (by decide)
        rw [show (rxNoCore D M2).get r = D.get r by
          simp only [rxNoCore, Core.goto_get]; exact Core.wr_get_ne _ _ _ _ _ hne]
        exact kD r hr
      · show ((rxNoCore D M2).get 9).toNat ≤ _
        rw [show (rxNoCore D M2).get 9 = D.get 9 by simp [rxNoCore, Core.wr_get_ne], D9]
        simp only [BitVec.toNat_ofNat]; omega
      · intro x hx1 hx2
        show M2 x = M0 x
        rw [M2o x hx2]; exact h.ram x (fun h' => hx1 ⟨h'.1, by omega⟩) hx2
    · -- data ready: assert_offset(0), read RBR, store
      have r3 := rxB D M2 Dpc qD (by simp only [taken, beq_eq_false_iff_ne]; exact hz)
      let Bc := rxBCore D M2
      have csB : Bc.sameCsr D := by
        unfold Bc rxBCore
        repeat (first | exact Core.sameCsr_wr _ _ _ _ | exact Core.sameCsr_goto _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_)
      have qB : Quiet Bc := Quiet.of_sameCsr csB qD
      have B10 : Bc.get 10 = alu .add 0 0x00000000#32 := by simp [Bc, rxBCore, Core.wr_get_ne, Core.wr_get_self]
      have B1 : Bc.get 1 = 0x80004398 := by simp [Bc, rxBCore, Core.wr_get_self]
      have B8 : Bc.get 8 = alu .add (D.get 18) (D.get 9) := by simp [Bc, rxBCore, Core.wr_get_ne, Core.wr_get_self]
      have gB : ∀ r : Reg, r ≠ 1 → r ≠ 8 → r ≠ 10 → r ≠ 11 → Bc.get r = D.get r := fun r a b c' d' => by
        simp [Bc, rxBCore, Core.wr_get_ne, a, b, c', d']
      have B2 : Bc.get 2 = c0.get 2 := (gB 2 (by decide) (by decide) (by decide) (by decide)).trans (kD 2 (by decide))
      have r4 := aoff Bc M2 rfl qB (Nat.mod_one _) (by rw [B2]; exact E.stk) (by rw [B10]; decide) (by rw [B1]; decide)
      let B' := aoffCore Bc M2
      let M3 := aoffRam Bc M2
      have csB' : B'.sameCsr Bc := by
        unfold B' aoffCore
        repeat (first | exact Core.sameCsr_wr _ _ _ _ | exact Core.sameCsr_goto _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_)
      have qB' : Quiet B' := Quiet.of_sameCsr csB' qB
      have B'pc : B'.pc = 0x80004398 := by simp only [B', aoffCore, Core.goto_pc]; exact B1
      have gB' : ∀ r : Reg, r ≠ 2 → r ≠ 11 → r ≠ 12 → B'.get r = Bc.get r := fun r a b c' => by
        simp [B', aoffCore, Core.wr_get_ne, a, b, c']
      have B'2 : B'.get 2 = c0.get 2 := by
        simp only [B', aoffCore, Core.goto_get, Core.wr_get_self _ _ _ _ (show (2 : Reg).val ≠ 0 by decide)]
        rw [sp_back, B2]
      have M3o : ∀ x : Word, x ≠ c0.get 2 + 0xffffffe0#32 + 0x0000000f#32 → M3 x = M2 x := by
        intro x hx; show ramWrite M2 _ _ .b x = M2 x; rw [ramWrite, ramPut_ne _ (by rw [B2]; exact hx)]
      have kB' : ∀ r : Reg, r.val ∉ rxW → B'.get r = c0.get r := by
        intro r hr
        by_cases h2 : r = 2
        · subst h2; exact B'2
        · rw [gB' r h2 (fun e => by subst e; exact absurd hr (by decide)) (fun e => by subst e; exact absurd hr (by decide)),
            gB r (fun e => by subst e; exact absurd hr (by decide)) (fun e => by subst e; exact absurd hr (by decide))
              (fun e => by subst e; exact absurd hr (by decide)) (fun e => by subst e; exact absurd hr (by decide))]
          exact kD r hr
      have B'8 : B'.get 8 = c0.get 18 + BitVec.ofNat 32 i := by
        rw [gB' 8 (by decide) (by decide) (by decide), B8, kD 18 (by decide), D9]; rfl
      have B'9 : B'.get 9 = BitVec.ofNat 32 i := by
        rw [gB' 9 (by decide) (by decide) (by decide), gB 9 (by decide) (by decide) (by decide) (by decide), D9]
      refine lands_of_qrun_lands (r3.trans r4) ?_
      -- read RBR
      refine lands_lbu_dev (rd := 10) (rs1 := 19) (off := 0x00000000#32) (len := 0x00000004#32)
        (by rw [B'pc]; decide) (by rw [B'pc]; exact f80004398)
        (by rw [kB' 19 (by decide), E.rbr]; rfl) (by decide) rbr_none rbr_dev rfl rfl qB' fun u => ?_
      let U := B'.wr 10 (extend .b false (devVal .b u)) (B'.pc + 0x00000004#32)
      have qU : Quiet U := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) qB'
      have Upc : U.pc = 0x8000439c := by simp only [U, Core.wr_pc, B'pc]; rfl
      have kU : ∀ r : Reg, r.val ∉ rxW → U.get r = c0.get r := fun r hr => by
        rw [show U.get r = B'.get r from Core.wr_get_ne _ _ _ _ _ (fun e => by subst e; exact absurd hr (by decide))]
        exact kB' r hr
      have U8 : U.get 8 = c0.get 18 + BitVec.ofNat 32 i := by
        rw [show U.get 8 = B'.get 8 from Core.wr_get_ne _ _ _ _ _ (by decide)]; exact B'8
      have U9 : U.get 9 = BitVec.ofNat 32 i := by
        rw [show U.get 9 = B'.get 9 from Core.wr_get_ne _ _ _ _ _ (by decide)]; exact B'9
      have U20 : U.get 20 = c0.get 20 := kU 20 (by decide)
      have ex : (c0.get 18 + BitVec.ofNat 32 i).toNat = (c0.get 18).toNat + i := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      have hin : B.inRam (U.get 8) 1 = true := by rw [U8, B_ram, ex]; omega
      have hi1 : (alu .add (BitVec.ofNat 32 i) 0x00000001#32 : Word) = BitVec.ofNat 32 (i + 1) := by
        simp only [alu_add]; bv_omega
      -- the stored byte lands in buf[dst + i]
      have M4o : ∀ x : Word, x ≠ c0.get 18 + BitVec.ofNat 32 i → ramWrite M3 (U.get 8) (U.get 10) .b x = M3 x := by
        intro x hx; rw [ramWrite, ramPut_ne _ (by rw [U8]; exact hx)]
      have ramN : ∀ n, i + 1 ≤ n → RxRam c0 M0 (ramWrite M3 (U.get 8) (U.get 10) .b) n := by
        intro n hn x hx1 hx2
        have hne : x ≠ c0.get 18 + BitVec.ofNat 32 i := fun he => hx1 (by subst he; rw [ex]; omega)
        rw [M4o x hne, M3o x hx2, M2o x hx2]
        exact h.ram x (fun h' => hx1 ⟨h'.1, by omega⟩) hx2
      by_cases hend : i + 1 = (c0.get 20).toNat
      · -- the buffer is full: the exit with s1 := cap
        have r5 := rxEnd U M3 Upc qU (Nat.mod_one _) hin (by
          rw [U20, U9, hi1]; simp only [taken, bne_eq_false_iff_eq]
          apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega)
        refine lands_of_qrun r5 ⟨rfl, Quiet.of_sameCsr (by
          unfold rxEndCore
          repeat (first | exact Core.sameCsr_wr _ _ _ _ | exact Core.sameCsr_goto _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_)) qU, ?_, ?_, ramN _ (by omega)⟩
        · intro r hr
          have hne : r ≠ 9 := fun e => by subst e; exact absurd hr (by decide)
          rw [show (rxEndCore U M3).get r = U.get r by
            simp only [rxEndCore, Core.goto_get]
            rw [Core.wr_get_ne _ _ _ _ _ hne, Core.goto_get, Core.goto_get, Core.wr_get_ne _ _ _ _ _ hne]]
          exact kU r hr
        · rw [show (rxEndCore U M3).get 9 = alu .add 0 (U.get 20) by simp [rxEndCore, Core.wr_get_self], U20]
          simp [alu_add]
      · -- more room: back to the loop head with i + 1
        have r5 := rxLoop U M3 Upc qU (Nat.mod_one _) hin (by
          rw [U20, U9, hi1]; simp only [taken, bne_iff_ne, ne_eq]
          intro he; have := congrArg BitVec.toNat he; simp only [BitVec.toNat_ofNat] at this; omega)
        let L := rxLoopCore U M3
        have csL : L.sameCsr U := by
          unfold L rxLoopCore
          repeat (first | exact Core.sameCsr_wr _ _ _ _ | exact Core.sameCsr_goto _ _ | refine (Core.sameCsr_wr _ _ _ _).trans ?_ | refine (Core.sameCsr_goto _ _).trans ?_)
        refine lands_of_qrun_lands r5 (ih (i + 1) L _ (by omega) ⟨rfl, Quiet.of_sameCsr csL qU, ?_, ?_, by omega,
          ramN _ (Nat.le_refl _)⟩)
        · intro r hr
          have hne : r ≠ 9 := fun e => by subst e; exact absurd hr (by decide)
          rw [show L.get r = U.get r by
            simp only [L, rxLoopCore, Core.goto_get]; exact Core.wr_get_ne _ _ _ _ _ hne]
          exact kU r hr
        · simp [L, rxLoopCore, Core.wr_get_self, U9]; exact hi1

end E5R.Rmk.Deframer.Rx
