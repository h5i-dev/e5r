/-
  `cobs::dec::decode_in_place_report`, the copy loop 0x8001e09c..0x8001e0c2: the
  `code - 1` data bytes of one COBS block moved from buf[src+1..] to buf[dst..].

    0x8001e09c add a5,t5,a3 ; beqz a5,panic(0x8001e11c) ; beq t6,a3,0x8001e0fe
    0x8001e0a6 add a5,s3,a3 ; lbu a5,1(a5) ; add s1,s2,a3 ; sb a5,0(s1)
    0x8001e0b6 add a5,t4,a3 ; addi a5,a5,2 ; zext.b a5 ; addi a3,a3,1 ; bne s0,a5,0x8001e09c

  with t5 = 1 - len + src, t6 = len - dst, s3 = buf + src, s2 = buf + dst, t4 = src,
  s0 = (src + code) mod 256, a3 = i. The panic branch is taken iff src + i + 1 = len,
  the size branch iff dst + i = len: neither happens when src + code ≤ len and
  dst ≤ src, so every byte read is buf[src+1+i] < len and every byte written is
  buf[dst+i] < len.

  Original e5r code, Apache-2.0.
-/
import Projects.rmk.Cobs.Scan

set_option maxRecDepth 100000

namespace E5R.Rmk.Cobs
open E5R E5R.Rmk E5R.Rmk.CobsFetch

theorem byteOf_byte (b : BitVec 8) : byteOf (BitVec.ofNat 32 b.toNat) 0 = b := by
  have := b.isLt
  apply BitVec.eq_of_toNat_eq
  simp [byteOf]; omega

/-- A buffer byte is a byte of model RAM. -/
theorem buf_inRam (buf : Word) (len j : Nat) (hbuf : 0x80029bc8 ≤ buf.toNat ∧ buf.toNat + len ≤ 0x81000000)
    (hj : j < len) : B.inRam (buf + BitVec.ofNat 32 j) 1 = true := by
  rw [B_ram]; constructor <;> bv_omega

/-- The copy loop's panic guard: a5 = 1 - len + src + i is never zero. -/
theorem t5_ne (len src i : Nat) (h : src + i + 1 < len) (hl : len ≤ 488) :
    ¬ (1#32 - BitVec.ofNat 32 len + BitVec.ofNat 32 src + BitVec.ofNat 32 i = 0) := by
  intro e; bv_omega

/-- The copy loop's size guard: t6 = len - dst never equals a3 = i. -/
theorem t6_ne (len dst i : Nat) (h : dst + i < len) (hl : len ≤ 488) :
    ¬ (BitVec.ofNat 32 (len - dst) = BitVec.ofNat 32 i) := by
  intro e; bv_omega

/-- The registers the copy loop reads, at its head 0x8001e09c. -/
structure CopyRegs (d : Core) (buf : Word) (len src dst code i : Nat) : Prop where
  t5 : d.get 30 = 1#32 - BitVec.ofNat 32 len + BitVec.ofNat 32 src
  t6 : d.get 31 = BitVec.ofNat 32 (len - dst)
  s3 : d.get 19 = buf + BitVec.ofNat 32 src
  s2 : d.get 18 = buf + BitVec.ofNat 32 dst
  t4 : d.get 29 = BitVec.ofNat 32 src
  s0 : d.get 8 = BitVec.ofNat 32 ((src + code) % 256)
  a3 : d.get 13 = BitVec.ofNat 32 i

/-- One iteration from a3 = i (i + 2 ≤ code): 11 steps to the back edge 0x8001e0c2,
    one byte written. -/
theorem copy_body (buf : Word) (len src dst code i : Nat)
    (hbuf : 0x80029bc8 ≤ buf.toNat ∧ buf.toNat + len ≤ 0x81000000) (hlen : len ≤ 488)
    (hc : 2 ≤ code ∧ code ≤ 255) (hsc : src + code ≤ len) (hds : dst ≤ src) (hi : i + 2 ≤ code)
    (d : Core) (S : Word → BitVec 8) (hpc : d.pc = 0x8001e09c) (hq : Quiet d)
    (hr : CopyRegs d buf len src dst code i) :
    ∃ e, QRun B img 11 ⟨d, S⟩ ⟨e, ramPut S (buf + BitVec.ofNat 32 (dst + i))
        (S (buf + BitVec.ofNat 32 (src + 1 + i)))⟩ ∧
      e.pc = 0x8001e0c2 ∧ e.sameCsr d ∧ e.get 13 = BitVec.ofNat 32 (i + 1) ∧
      e.get 15 = BitVec.ofNat 32 ((src + i + 2) % 256) ∧
      (∀ r : Reg, r ≠ 9 → r ≠ 13 → r ≠ 15 → e.get r = d.get r) := by
  obtain ⟨h30, h31, h19, h18, h29, h8, h13⟩ := hr
  have q : ∀ e : Core, e.sameCsr d → Quiet e := fun e h => Quiet.of_sameCsr h hq
  let c1 := d.wr 15 (alu .add (d.get 30) (d.get 13)) 0x8001e0a0
  let c2 := c1.goto 0x8001e0a2
  let c3 := c2.goto 0x8001e0a6
  let c4 := c3.wr 15 (alu .add (c3.get 19) (c3.get 13)) 0x8001e0aa
  let c5 := c4.wr 15 (extend .b false (ramRead S (c4.get 15 + 0x1#32) .b)) 0x8001e0ae
  let c6 := c5.wr 9 (alu .add (c5.get 18) (c5.get 13)) 0x8001e0b2
  let c7 := c6.goto 0x8001e0b6
  let S' := ramWrite S (c6.get 9 + 0x0#32) (c6.get 15) .b
  let c8 := c7.wr 15 (alu .add (c7.get 29) (c7.get 13)) 0x8001e0ba
  let c9 := c8.wr 15 (alu .add (c8.get 15) 0x2#32) 0x8001e0bc
  let c10 := c9.wr 15 (alu .and (c9.get 15) 0xff#32) 0x8001e0c0
  let c11 := c10.wr 13 (alu .add (c10.get 13) 0x1#32) 0x8001e0c2
  -- register values along the way
  have g : ∀ e : Core, (e = c1 ∨ e = c2 ∨ e = c3) → ∀ r : Reg, r ≠ 15 → e.get r = d.get r := by
    intro e he r hr; rcases he with rfl | rfl | rfl <;> simp [c3, c2, c1, Core.wr_get_ne, hr]
  have v1 : c1.get 15 = 1#32 - BitVec.ofNat 32 len + BitVec.ofNat 32 src + BitVec.ofNat 32 i := by
    simp [c1, Core.wr_get_self, alu, h30, h13]
  have v4 : c4.get 15 = buf + BitVec.ofNat 32 src + BitVec.ofNat 32 i := by
    simp [c4, Core.wr_get_self, alu, g c3 (by simp) 19 (by decide), g c3 (by simp) 13 (by decide), h19, h13]
  have rd : buf + BitVec.ofNat 32 src + BitVec.ofNat 32 i + 0x1#32 = buf + BitVec.ofNat 32 (src + 1 + i) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have v5 : c5.get 15 = BitVec.ofNat 32 (S (buf + BitVec.ofNat 32 (src + 1 + i))).toNat := by
    simp only [c5, Core.wr_get_self _ (15 : Reg) _ _ (by decide), v4, rd, lbu_val]
  have g5 : ∀ r : Reg, r ≠ 15 → c5.get r = d.get r := fun r hr => by
    simp only [c5, c4, Core.wr_get_ne _ _ _ _ _ hr]; exact g c3 (by simp) r hr
  have wa : buf + BitVec.ofNat 32 dst + BitVec.ofNat 32 i = buf + BitVec.ofNat 32 (dst + i) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have v6 : c6.get 9 = buf + BitVec.ofNat 32 (dst + i) := by
    simp [c6, Core.wr_get_self, alu, g5 18 (by decide), g5 13 (by decide), h18, h13, wa]
  have v6' : c6.get 15 = c5.get 15 := by simp [c6, Core.wr_get_ne]
  have hS' : S' = ramPut S (buf + BitVec.ofNat 32 (dst + i)) (S (buf + BitVec.ofNat 32 (src + 1 + i))) := by
    simp only [S', ramWrite, v6, BitVec.add_zero, v6', v5, byteOf_byte]
  have g7 : ∀ r : Reg, r ≠ 9 → r ≠ 15 → c7.get r = d.get r := fun r h9 h15 => by
    simp only [c7, c6, Core.goto_get, Core.wr_get_ne _ _ _ _ _ h9]; exact g5 r h15
  have v10 : c10.get 15 = BitVec.ofNat 32 ((src + i + 2) % 256) := by
    simp only [c10, c9, c8, Core.wr_get_self _ (15 : Reg) _ _ (by decide), alu,
      g7 29 (by decide) (by decide), g7 13 (by decide) (by decide), h29, h13]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [show (255 : Nat) % 2 ^ 32 = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  -- the guards
  have nz : ¬ (c1.get 15 = 0) := by
    rw [v1]; exact t5_ne len src i (by omega) hlen
  have ns : ¬ (c2.get 31 = c2.get 13) := by
    rw [g c2 (by simp) 31 (by decide), g c2 (by simp) 13 (by decide), h31, h13]
    exact t6_ne len dst i (by omega) hlen
  have s1 : DetStep B img ⟨d, S⟩ ⟨c1, S⟩ := dstep f8001e09c hpc (by rw [exec_op, hpc]; rfl)
  have s2 : DetStep B img ⟨c1, S⟩ ⟨c2, S⟩ :=
    dstep f8001e0a0 rfl (by rw [exec_branch, if_neg (by simp only [taken, beq_iff_eq, Core.get_zero]; exact nz)]; rfl)
  have s3 : DetStep B img ⟨c2, S⟩ ⟨c3, S⟩ :=
    dstep f8001e0a2 rfl (by rw [exec_branch, if_neg (by simp only [taken, beq_iff_eq]; exact ns)]; rfl)
  have s4 : DetStep B img ⟨c3, S⟩ ⟨c4, S⟩ := dstep f8001e0a6 rfl (by rw [exec_op]; rfl)
  have s5 : DetStep B img ⟨c4, S⟩ ⟨c5, S⟩ :=
    dstep_load f8001e0aa rfl (exec_load _ _ _ _ _ _ _) (Nat.mod_one _)
      (by show B.inRam _ 1 = true; rw [v4, rd]; exact buf_inRam buf len _ hbuf (by omega)) rfl
  have s6 : DetStep B img ⟨c5, S⟩ ⟨c6, S⟩ := dstep f8001e0ae rfl (by rw [exec_op]; rfl)
  have s7 : DetStep B img ⟨c6, S⟩ ⟨c7, S'⟩ :=
    dstep_store f8001e0b2 rfl (exec_store _ _ _ _ _ _) (Nat.mod_one _)
      (by show B.inRam _ 1 = true; rw [v6, BitVec.add_zero]; exact buf_inRam buf len _ hbuf (by omega))
  have s8 : DetStep B img ⟨c7, S'⟩ ⟨c8, S'⟩ := dstep f8001e0b6 rfl (by rw [exec_op]; rfl)
  have s9 : DetStep B img ⟨c8, S'⟩ ⟨c9, S'⟩ := dstep f8001e0ba rfl (by rw [exec_opimm]; rfl)
  have s10 : DetStep B img ⟨c9, S'⟩ ⟨c10, S'⟩ := dstep f8001e0bc rfl (by rw [exec_opimm]; rfl)
  have s11 : DetStep B img ⟨c10, S'⟩ ⟨c11, S'⟩ := dstep f8001e0c0 rfl (by rw [exec_opimm]; rfl)
  have k1 : c1.sameCsr d := Core.sameCsr_wr _ _ _ _
  have k2 : c2.sameCsr d := (Core.sameCsr_goto _ _).trans k1
  have k3 : c3.sameCsr d := (Core.sameCsr_goto _ _).trans k2
  have k4 : c4.sameCsr d := (Core.sameCsr_wr _ _ _ _).trans k3
  have k5 : c5.sameCsr d := (Core.sameCsr_wr _ _ _ _).trans k4
  have k6 : c6.sameCsr d := (Core.sameCsr_wr _ _ _ _).trans k5
  have k7 : c7.sameCsr d := (Core.sameCsr_goto _ _).trans k6
  have k8 : c8.sameCsr d := (Core.sameCsr_wr _ _ _ _).trans k7
  have k9 : c9.sameCsr d := (Core.sameCsr_wr _ _ _ _).trans k8
  have k10 : c10.sameCsr d := (Core.sameCsr_wr _ _ _ _).trans k9
  have k11 : c11.sameCsr d := (Core.sameCsr_wr _ _ _ _).trans k10
  refine ⟨c11, ?_, rfl, k11, ?_, ?_, ?_⟩
  · rw [← hS']
    exact .step hq s1 (.step (q _ k1) s2 (.step (q _ k2) s3 (.step (q _ k3) s4 (.step (q _ k4) s5
      (.step (q _ k5) s6 (.step (q _ k6) s7 (.step (q _ k7) s8 (.step (q _ k8) s9 (.step (q _ k9) s10
      (.single (q _ k10) s11))))))))))
  · simp only [c11, Core.wr_get_self _ (13 : Reg) _ _ (by decide), alu]
    rw [show c10.get 13 = d.get 13 by simp [c10, c9, c8, Core.wr_get_ne]; exact g7 13 (by decide) (by decide), h13]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · simp only [c11, Core.wr_get_ne _ _ _ _ _ (show (15 : Reg) ≠ 13 by decide)]; exact v10
  · intro r h9 h13 h15
    simp only [c11, c10, c9, c8, Core.wr_get_ne _ _ _ _ _ h13, Core.wr_get_ne _ _ _ _ _ h15]
    exact g7 r h9 h15

/-! ## Single byte writes into the buffer -/

theorem put_same (S : Word → BitVec 8) (buf : Word) (p : Nat) (b : BitVec 8) :
    bufByte (ramPut S (buf + BitVec.ofNat 32 p) b) buf p = b.toNat := by
  simp [bufByte, ramPut]

theorem put_other (S : Word → BitVec 8) (buf : Word) (len p j : Nat) (b : BitVec 8)
    (hbuf : 0x80029bc8 ≤ buf.toNat ∧ buf.toNat + len ≤ 0x81000000) (hp : p < len) (hj : j < len) (hne : j ≠ p) :
    bufByte (ramPut S (buf + BitVec.ofNat 32 p) b) buf j = bufByte S buf j := by
  unfold bufByte
  rw [ramPut_ne]
  intro e; have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this; omega

theorem put_outside (S : Word → BitVec 8) (buf : Word) (len p : Nat) (b : BitVec 8) (x : Word)
    (hbuf : 0x80029bc8 ≤ buf.toNat ∧ buf.toNat + len ≤ 0x81000000) (hp : p < len)
    (hx : ¬ (buf.toNat ≤ x.toNat ∧ x.toNat < buf.toNat + len)) :
    ramPut S (buf + BitVec.ofNat 32 p) b x = S x := by
  rw [ramPut_ne]
  intro e; apply hx; subst e
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem mod256_ne (src i code : Nat) (h : i + 2 < code) (hc : code ≤ 255) :
    ¬ (BitVec.ofNat 32 ((src + code) % 256) = BitVec.ofNat 32 ((src + i + 2) % 256)) := by
  intro e; have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by omega : (src + code) % 256 < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : (src + i + 2) % 256 < 2 ^ 32)] at this
  omega

/-- The copy loop from a3 = i to its exit 0x8001e0c6. -/
theorem copy (buf : Word) (len src dst code : Nat)
    (hbuf : 0x80029bc8 ≤ buf.toNat ∧ buf.toNat + len ≤ 0x81000000) (hlen : len ≤ 488)
    (hc : 2 ≤ code ∧ code ≤ 255) (hsc : src + code ≤ len) (hds : dst ≤ src) :
    ∀ (k i : Nat) (d : Core) (S : Word → BitVec 8), i + k + 2 = code →
      d.pc = 0x8001e09c → Quiet d → CopyRegs d buf len src dst code i →
      ∃ n e S', QRun B img n ⟨d, S⟩ ⟨e, S'⟩ ∧ e.pc = 0x8001e0c6 ∧ e.sameCsr d ∧
        e.get 13 = BitVec.ofNat 32 (code - 1) ∧
        (∀ r : Reg, r ≠ 9 → r ≠ 13 → r ≠ 15 → e.get r = d.get r) ∧
        (∀ j, dst + i ≤ j → j < dst + code - 1 → bufByte S' buf j = bufByte S buf (src + 1 + (j - dst))) ∧
        (∀ j, j < dst + i ∨ dst + code - 1 ≤ j → j < len → bufByte S' buf j = bufByte S buf j) ∧
        (∀ x : Word, ¬ (buf.toNat ≤ x.toNat ∧ x.toNat < buf.toNat + len) → S' x = S x) := by
  intro k
  induction k with
  | zero =>
    intro i d S hk hpc hq hr
    obtain ⟨e, hrun, hpc', hcs, h13, h15, hg⟩ := copy_body buf len src dst code i hbuf hlen hc hsc hds (by omega) d S hpc hq hr
    have heq : e.get 8 = e.get 15 := by
      rw [hg 8 (by decide) (by decide) (by decide), hr.s0, h15]; congr 1; omega
    let e1 := e.goto 0x8001e0c6
    let S1 := ramPut S (buf + BitVec.ofNat 32 (dst + i)) (S (buf + BitVec.ofNat 32 (src + 1 + i)))
    have s : DetStep B img ⟨e, S1⟩ ⟨e1, S1⟩ :=
      dstep f8001e0c2 hpc' (by rw [exec_branch, if_neg (by simp [taken, heq]), hpc']; rfl)
    refine ⟨_, e1, S1, hrun.trans (.single (Quiet.of_sameCsr hcs hq) s), rfl, (Core.sameCsr_goto _ _).trans hcs,
      ?_, fun r a b c => by simp only [e1, Core.goto_get]; exact hg r a b c, ?_, ?_, ?_⟩
    · simp only [e1, Core.goto_get, h13]; congr 1; omega
    · intro j h1 h2
      have hj : j = dst + i := by omega
      subst hj
      rw [put_same, show src + 1 + (dst + i - dst) = src + 1 + i by omega]; rfl
    · intro j hj hl; exact put_other S buf len (dst + i) j _ hbuf (by omega) hl (by omega)
    · intro x hx; exact put_outside S buf len (dst + i) _ x hbuf (by omega) hx
  | succ k ih =>
    intro i d S hk hpc hq hr
    obtain ⟨e, hrun, hpc', hcs, h13, h15, hg⟩ := copy_body buf len src dst code i hbuf hlen hc hsc hds (by omega) d S hpc hq hr
    have hne : ¬ (e.get 8 = e.get 15) := by
      rw [hg 8 (by decide) (by decide) (by decide), hr.s0, h15]; exact mod256_ne src i code (by omega) hc.2
    let e1 := e.goto 0x8001e09c
    let S1 := ramPut S (buf + BitVec.ofNat 32 (dst + i)) (S (buf + BitVec.ofNat 32 (src + 1 + i)))
    have s : DetStep B img ⟨e, S1⟩ ⟨e1, S1⟩ :=
      dstep f8001e0c2 hpc' (by
        rw [exec_branch, if_pos (by simp [taken, hne]), hpc']
        exact jump_ok _ _ (by show (0x8001e09c : Word).getLsbD 0 = false; decide))
    have k1 : e1.sameCsr d := (Core.sameCsr_goto _ _).trans hcs
    have g1 : ∀ r : Reg, r ≠ 9 → r ≠ 13 → r ≠ 15 → e1.get r = d.get r := fun r a b c => by
      simp only [e1, Core.goto_get]; exact hg r a b c
    have hr1 : CopyRegs e1 buf len src dst code (i + 1) :=
      ⟨by rw [g1 30 (by decide) (by decide) (by decide)]; exact hr.t5,
       by rw [g1 31 (by decide) (by decide) (by decide)]; exact hr.t6,
       by rw [g1 19 (by decide) (by decide) (by decide)]; exact hr.s3,
       by rw [g1 18 (by decide) (by decide) (by decide)]; exact hr.s2,
       by rw [g1 29 (by decide) (by decide) (by decide)]; exact hr.t4,
       by rw [g1 8 (by decide) (by decide) (by decide)]; exact hr.s0,
       by simp only [e1, Core.goto_get]; exact h13⟩
    obtain ⟨n, f, S'', hrun2, hpc2, hcs2, h13f, hgf, hin, hout, hx⟩ :=
      ih (i + 1) e1 S1 (by omega) rfl (Quiet.of_sameCsr k1 hq) hr1
    refine ⟨_, f, S'', hrun.trans (.step (Quiet.of_sameCsr hcs hq) s hrun2), hpc2, hcs2.trans k1, h13f,
      fun r a b c => by rw [hgf r a b c]; exact g1 r a b c, ?_, ?_, ?_⟩
    · intro j h1 h2
      rcases Nat.eq_or_lt_of_le h1 with e | e
      · subst e
        rw [hout (dst + i) (by omega) (by omega), put_same, show src + 1 + (dst + i - dst) = src + 1 + i by omega]
        rfl
      · rw [hin j (by omega) h2, put_other S buf len (dst + i) (src + 1 + (j - dst)) _ hbuf (by omega) (by omega)
          (by omega)]
    · intro j hj hl
      rw [hout j (by omega) hl, put_other S buf len (dst + i) j _ hbuf (by omega) hl (by omega)]
    · intro x hxx; rw [hx x hxx]; exact put_outside S buf len (dst + i) _ x hbuf (by omega) hxx

end E5R.Rmk.Cobs
