/-
  memmove's misaligned forward loop (pinned RMK image), 0x80020f2e (after 0x80020f28 neg a2,t3; andi a2,a2,0x18):

    neg a2,t3; andi a2,a2,0x18; mv a4,a5; lw a5,4(a1); srl a4,a4,t3;
    addi a1,a1,4; sll s1,a5,a2; or a4,a4,s1; addi s1,t5,8; sw a4,0(t5);
    addi t5,t5,4; bltu s1,a3,0x80020f28            (falls to 0x80020f4c)

  with t3 = 8·o for the source misalignment o ∈ {1,2,3}, a1 the aligned
  word below the source, a5 the previous source word (its bytes o..3 are
  the next source bytes). Every store writes exactly the source word at
  a1 + o (`merge_store`), so the loop computes `words` (Copy.lean); every
  load is an aligned word inside the source range.

  Original e5r code, Apache-2.0.
-/
import Projects.rmk.Merge
import Projects.rmk.MemmoveBigLoops

set_option maxRecDepth 100000

namespace E5R.Rmk
open E5R E5R.Rmk.MemmoveFetch

/-- The shift amounts the loop computes. -/
theorem shifts (o : Nat) (ho : 0 < o ∧ o < 4) :
    (BitVec.ofNat 32 (8 * o)).toNat % 32 = 8 * o ∧
    ((0 - BitVec.ofNat 32 (8 * o)) &&& 0x18#32).toNat % 32 = 32 - 8 * o := by
  rcases (by omega : o = 1 ∨ o = 2 ∨ o = 3) with rfl | rfl | rfl <;> decide

def misBody (c : Core) (ram : Word → BitVec 8) : Core :=
  let A := c.get 11
  let t3 := c.get 28
  let a2 := c.get 12
  let nxt := ramRead ram (A + 4#32) .w
  let mrg := alu .or (alu .srl (alu .add 0 (c.get 15)) t3) (alu .sll nxt a2)
  (((((((((c.wr 14 (alu .add 0 (c.get 15))
    0x80020f30).wr 15 nxt 0x80020f32).wr 14 (alu .srl (alu .add 0 (c.get 15)) t3) 0x80020f36).wr 11 (A + 4)
    0x80020f38).wr 9 (alu .sll nxt a2) 0x80020f3c).wr 14 mrg 0x80020f3e).wr 9 (c.get 30 + 8) 0x80020f42).goto
    0x80020f46).wr 30 (c.get 30 + 4) 0x80020f48)

/-- The merged word the body stores. -/
def misVal (c : Core) (ram : Word → BitVec 8) : Word :=
  alu .or (alu .srl (alu .add 0 (c.get 15)) (c.get 28))
    (alu .sll (ramRead ram (c.get 11 + 4#32) .w) (c.get 12))

theorem misBody_sameCsr (c : Core) (ram) : (misBody c ram).sameCsr c := by
  unfold misBody
  exact (Core.sameCsr_wr _ _ _ _).trans <| (Core.sameCsr_goto _ _).trans <| (Core.sameCsr_wr _ _ _ _).trans <|
    (Core.sameCsr_wr _ _ _ _).trans <| (Core.sameCsr_wr _ _ _ _).trans <| (Core.sameCsr_wr _ _ _ _).trans <|
    (Core.sameCsr_wr _ _ _ _).trans <| (Core.sameCsr_wr _ _ _ _).trans (Core.sameCsr_wr _ _ _ _)

theorem misBody_get (c : Core) (ram) (r : Reg) (h9 : r ≠ 9) (h11 : r ≠ 11)
    (h14 : r ≠ 14) (h15 : r ≠ 15) (h30 : r ≠ 30) : (misBody c ram).get r = c.get r := by
  simp [misBody, Core.wr_get_ne, h9, h11, h14, h15, h30]

theorem mis_body (c : Core) (ram : Word → BitVec 8) (hpc : c.pc = 0x80020f2e) (hq : Quiet c)
    (hA : (c.get 11 + 4#32).toNat % 4 = 0) (hD : (c.get 30).toNat % 4 = 0)
    (hs : B.inRam (c.get 11 + 4#32) 4 = true) (hd : B.inRam (c.get 30) 4 = true) :
    QRun B img 9 ⟨c, ram⟩ ⟨misBody c ram, ramWrite ram (c.get 30) (misVal c ram) .w⟩ := by
  let A := c.get 11
  let t3 := c.get 28
  let a2 := c.get 12
  let nxt := ramRead ram (A + 4#32) .w
  let c3 := c.wr 14 (alu .add 0 (c.get 15)) 0x80020f30
  let c4 := c3.wr 15 nxt 0x80020f32
  let c5 := c4.wr 14 (alu .srl (alu .add 0 (c.get 15)) t3) 0x80020f36
  let c6 := c5.wr 11 (A + 4) 0x80020f38
  let c7 := c6.wr 9 (alu .sll nxt a2) 0x80020f3c
  let c8 := c7.wr 14 (misVal c ram) 0x80020f3e
  let c9 := c8.wr 9 (c.get 30 + 8) 0x80020f42
  let c10 := c9.goto 0x80020f46
  let R1 := ramWrite ram (c.get 30) (misVal c ram) .w
  have q3 : Quiet c3 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) hq
  have q4 : Quiet c4 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q3
  have q5 : Quiet c5 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q4
  have q6 : Quiet c6 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q5
  have q7 : Quiet c7 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q6
  have q8 : Quiet c8 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q7
  have q9 : Quiet c9 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q8
  have q10 : Quiet c10 := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q9
  have s2 : DetStep B img ⟨c, ram⟩ ⟨c3, ram⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f80020f2e) fun o => ?_
    rw [exec_op, Core.get_zero, hpc]; rfl
  have s3 : DetStep B img ⟨c3, ram⟩ ⟨c4, ram⟩ := by
    refine detStep_of (by show (0x80020f30 : Word).getLsbD 0 = false; decide) f80020f30 fun o => ?_
    rw [exec_load, show c3.get 11 = A by simp [c3, Core.wr_get_ne, A],
      interp_load_ram (w := .w) o hA hs]; rfl
  have s4 : DetStep B img ⟨c4, ram⟩ ⟨c5, ram⟩ := by
    refine detStep_of (by show (0x80020f32 : Word).getLsbD 0 = false; decide) f80020f32 fun o => ?_
    rw [exec_op, show c4.get 14 = alu .add 0 (c.get 15) by simp [c4, c3, Core.wr_get_ne, Core.wr_get_self],
      show c4.get 28 = t3 by simp [c4, c3, Core.wr_get_ne, t3]]; rfl
  have s5 : DetStep B img ⟨c5, ram⟩ ⟨c6, ram⟩ := by
    refine detStep_of (by show (0x80020f36 : Word).getLsbD 0 = false; decide) f80020f36 fun o => ?_
    rw [exec_opimm, show c5.get 11 = A by simp [c5, c4, c3, Core.wr_get_ne, A]]; rfl
  have s6 : DetStep B img ⟨c6, ram⟩ ⟨c7, ram⟩ := by
    refine detStep_of (by show (0x80020f38 : Word).getLsbD 0 = false; decide) f80020f38 fun o => ?_
    rw [exec_op, show c6.get 15 = nxt by simp [c6, c5, c4, Core.wr_get_ne, Core.wr_get_self],
      show c6.get 12 = a2 by simp [c6, c5, c4, c3, Core.wr_get_ne, a2]]; rfl
  have s7 : DetStep B img ⟨c7, ram⟩ ⟨c8, ram⟩ := by
    refine detStep_of (by show (0x80020f3c : Word).getLsbD 0 = false; decide) f80020f3c fun o => ?_
    rw [exec_op, show c7.get 14 = alu .srl (alu .add 0 (c.get 15)) t3 by
        simp [c7, c6, c5, Core.wr_get_ne, Core.wr_get_self],
      show c7.get 9 = alu .sll nxt a2 by simp [c7, Core.wr_get_self]]; rfl
  have s8 : DetStep B img ⟨c8, ram⟩ ⟨c9, ram⟩ := by
    refine detStep_of (by show (0x80020f3e : Word).getLsbD 0 = false; decide) f80020f3e fun o => ?_
    rw [exec_opimm, show c8.get 30 = c.get 30 by simp [c8, c7, c6, c5, c4, c3, Core.wr_get_ne]]; rfl
  have s9 : DetStep B img ⟨c9, ram⟩ ⟨c10, R1⟩ := by
    refine detStep_of (by show (0x80020f42 : Word).getLsbD 0 = false; decide) f80020f42 fun o => ?_
    rw [exec_store, BitVec.add_zero,
      show c9.get 30 = c.get 30 by simp [c9, c8, c7, c6, c5, c4, c3, Core.wr_get_ne],
      show c9.get 14 = misVal c ram by simp [c9, c8, Core.wr_get_ne, Core.wr_get_self],
      interp_store_ram (w := .w) o hD hd]; rfl
  have s10 : DetStep B img ⟨c10, R1⟩ ⟨misBody c ram, R1⟩ := by
    refine detStep_of (by show (0x80020f46 : Word).getLsbD 0 = false; decide) f80020f46 fun o => ?_
    rw [exec_opimm, show c10.get 30 = c.get 30 by simp [c10, c9, c8, c7, c6, c5, c4, c3, Core.wr_get_ne]]
    rfl
  exact .step hq s2 (.step q3 s3 (.step q4 s4 (.step q5 s5 (.step q6 s6
    (.step q7 s7 (.step q8 s8 (.step q9 s9 (.single q10 s10))))))))

theorem misVal_eq (c : Core) (ram : Word → BitVec 8) (o : Nat) (ho : 0 < o ∧ o < 4)
    (h28 : c.get 28 = BitVec.ofNat 32 (8 * o)) (h12 : c.get 12 = (0 - BitVec.ofNat 32 (8 * o)) &&& 0x18#32) :
    misVal c ram = (c.get 15 >>> (8 * o)) ||| (ramRead ram (c.get 11 + 4#32) .w <<< (32 - 8 * o)) := by
  obtain ⟨e1, e2⟩ := shifts o ho
  simp only [misVal, alu, h28, h12, e1, e2]
  rw [show (0 : Word) + c.get 15 = c.get 15 by bv_omega]

/-- The misaligned loop: `j+1` merged words to `t5`, the source being the
    bytes from `a1 + o`; ends at 0x80020f4c with `a5` the last source word. -/
theorem mis_loop (o : Nat) (ho : 0 < o ∧ o < 4) : ∀ (j : Nat) (c : Core) (ram : Word → BitVec 8),
    c.pc = 0x80020f2e → Quiet c → c.get 28 = BitVec.ofNat 32 (8 * o) →
    c.get 12 = (0 - BitVec.ofNat 32 (8 * o)) &&& 0x18#32 →
    c.get 13 = c.get 30 + BitVec.ofNat 32 (4 * (j + 1) + 4) →
    (c.get 30).toNat + 4 * (j + 1) + 4 < 2 ^ 32 → (c.get 11).toNat + 4 * (j + 1) + 4 < 2 ^ 32 →
    (c.get 11).toNat % 4 = 0 → (c.get 30).toNat % 4 = 0 →
    ((c.get 30).toNat ≤ (c.get 11).toNat ∨ (c.get 11).toNat + 8 ≤ (c.get 30).toNat) →
    (∀ k, o ≤ k → k < 4 → byteOf (c.get 15) k = ram (c.get 11 + BitVec.ofNat 32 k)) →
    B.inRam (c.get 11 + 4#32) (4 * (j + 1)) = true → B.inRam (c.get 30) (4 * (j + 1)) = true →
    ∃ n c', QRun B img n ⟨c, ram⟩ ⟨c', words ram (c.get 11 + BitVec.ofNat 32 o) (c.get 30) (j + 1)⟩ ∧
      c'.pc = 0x80020f4c ∧ c'.sameCsr c ∧
      c'.get 11 = c.get 11 + BitVec.ofNat 32 (4 * (j + 1)) ∧ c'.get 30 = c.get 30 + BitVec.ofNat 32 (4 * (j + 1)) ∧
      c'.get 28 = c.get 28 ∧ c'.get 13 = c.get 13 ∧ c'.get 12 = c.get 12 ∧
      (∀ k, o ≤ k → k < 4 → byteOf (c'.get 15) k =
        words ram (c.get 11 + BitVec.ofNat 32 o) (c.get 30) (j + 1) (c'.get 11 + BitVec.ofNat 32 k)) ∧
      ∀ r : Reg, r ≠ 9 → r ≠ 11 → r ≠ 14 → r ≠ 15 → r ≠ 30 → c'.get r = c.get r := by
  intro j
  induction j with
  | zero =>
    intro c ram hpc hq h28 h12 h13 hdl hal hA hD hdir hprev hs hd
    have hb := mis_body c ram hpc hq (by bv_omega) hD (by simpa using hs) (by simpa using hd)
    let c11 := misBody c ram
    have q11 : Quiet c11 := Quiet.of_sameCsr (misBody_sameCsr c ram) hq
    let R1 := ramWrite ram (c.get 30) (misVal c ram) .w
    have s11 : DetStep B img ⟨c11, R1⟩ ⟨c11.goto 0x80020f4c, R1⟩ := by
      refine detStep_of (by show (0x80020f48 : Word).getLsbD 0 = false; decide) f80020f48 fun o => ?_
      rw [exec_branch]
      have e9 : c11.get 9 = c.get 30 + 8 := by simp [c11, misBody, Core.wr_get_ne, Core.wr_get_self]
      have e13 : c11.get 13 = c.get 13 := by simp [c11, misBody, Core.wr_get_ne]
      have hnt : (c.get 30 + 8).ult (c.get 13) = false := by
        rw [h13]; simp only [BitVec.ult, decide_eq_false_iff_not]; bv_omega
      rw [e9, e13]; simp only [taken, hnt, Bool.false_eq_true, if_false]; rfl
    have hw : R1 = ramWrite ram (c.get 30) (ramRead ram (c.get 11 + BitVec.ofNat 32 o) .w) .w := by
      show ramWrite ram (c.get 30) (misVal c ram) .w = _
      rw [misVal_eq c ram o ho h28 h12]; exact merge_store ram ram _ _ _ o ho hprev
    refine ⟨10, c11.goto 0x80020f4c, ?_, rfl, (Core.sameCsr_goto _ _).trans (misBody_sameCsr c ram), ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · have := hb.trans (.single q11 s11)
      simp only [words]; rw [← hw]; exact this
    · simp [c11, misBody, Core.wr_get_ne, Core.wr_get_self]
    · simp [c11, misBody, Core.wr_get_self]
    · simp [c11, misBody, Core.wr_get_ne]
    · simp [c11, misBody, Core.wr_get_ne]
    · simp [c11, misBody, Core.wr_get_ne]
    · intro k hk1 hk2
      have g15 : (c11.goto 0x80020f4c).get 15 = ramRead ram (c.get 11 + 4#32) .w := by
        simp [c11, misBody, Core.wr_get_ne, Core.wr_get_self]
      have g11 : (c11.goto 0x80020f4c).get 11 = c.get 11 + 4 := by
        simp [c11, misBody, Core.wr_get_ne, Core.wr_get_self]
      rw [g15, g11, byte_read_k _ _ _ hk2]
      simp only [words]
      rw [← hw]
      show ram _ = ramWrite ram (c.get 30) (misVal c ram) .w _
      rw [ramWrite_w_other]
      · first | (congr 1 <;> bv_omega) | rfl
      · intro m hm; bv_omega
    · intro r a b d e f; simp only [Core.goto_get]; exact misBody_get c ram r a b d e f
  | succ j ih =>
    intro c ram hpc hq h28 h12 h13 hdl hal hA hD hdir hprev hs hd
    have hs4 : B.inRam (c.get 11 + 4#32) 4 = true := by rw [B_ram] at *; omega
    have hd4 : B.inRam (c.get 30) 4 = true := by rw [B_ram] at *; omega
    have hb := mis_body c ram hpc hq (by bv_omega) hD hs4 hd4
    let c11 := misBody c ram
    have cs11 : c11.sameCsr c := misBody_sameCsr c ram
    have q11 : Quiet c11 := Quiet.of_sameCsr cs11 hq
    let R1 := ramWrite ram (c.get 30) (misVal c ram) .w
    have s11 : DetStep B img ⟨c11, R1⟩ ⟨c11.goto 0x80020f2e, R1⟩ := by
      refine detStep_of (by show (0x80020f48 : Word).getLsbD 0 = false; decide) f80020f48 fun o => ?_
      rw [exec_branch]
      have e9 : c11.get 9 = c.get 30 + 8 := by simp [c11, misBody, Core.wr_get_ne, Core.wr_get_self]
      have e13 : c11.get 13 = c.get 13 := by simp [c11, misBody, Core.wr_get_ne]
      have ht : (c.get 30 + 8).ult (c.get 13) = true := by
        rw [h13]; simp only [BitVec.ult, decide_eq_true_iff]; bv_omega
      rw [e9, e13]; simp only [taken, ht, if_true]
      have hp : c11.pc + 0xffffffe6#32 = 0x80020f2e := by rw [show c11.pc = 0x80020f48 from rfl]; decide
      rw [hp, jump_ok _ _ (by decide)]; rfl
    have hw : R1 = ramWrite ram (c.get 30) (ramRead ram (c.get 11 + BitVec.ofNat 32 o) .w) .w := by
      show ramWrite ram (c.get 30) (misVal c ram) .w = _
      rw [misVal_eq c ram o ho h28 h12]; exact merge_store ram ram _ _ _ o ho hprev
    have q12 : Quiet (c11.goto 0x80020f2e) := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q11
    have g11 : (c11.goto 0x80020f2e).get 11 = c.get 11 + 4 := by
      simp [c11, misBody, Core.wr_get_ne, Core.wr_get_self]
    have g30 : (c11.goto 0x80020f2e).get 30 = c.get 30 + 4 := by
      simp [c11, misBody, Core.wr_get_ne, Core.wr_get_self]
    have g13 : (c11.goto 0x80020f2e).get 13 = c.get 13 := by simp [c11, misBody, Core.wr_get_ne]
    have g28 : (c11.goto 0x80020f2e).get 28 = c.get 28 := by simp [c11, misBody, Core.wr_get_ne]
    have g12 : (c11.goto 0x80020f2e).get 12 = c.get 12 := by simp [c11, misBody, Core.wr_get_ne]
    have g15 : (c11.goto 0x80020f2e).get 15 = ramRead ram (c.get 11 + 4#32) .w := by
      simp [c11, misBody, Core.wr_get_ne, Core.wr_get_self]
    have hprev' : ∀ k, o ≤ k → k < 4 → byteOf ((c11.goto 0x80020f2e).get 15) k =
        R1 ((c11.goto 0x80020f2e).get 11 + BitVec.ofNat 32 k) := by
      intro k hk1 hk2
      rw [g15, g11, byte_read_k _ _ _ hk2]
      show ram _ = ramWrite ram (c.get 30) (misVal c ram) .w _
      rw [ramWrite_w_other]
      · first | (congr 1 <;> bv_omega) | rfl
      · intro m hm; bv_omega
    obtain ⟨n, c', hr, hpc', hcs, h11', h30', h28', h13', h12', hpv, hfr⟩ := ih (c11.goto 0x80020f2e) R1 rfl q12
      (by rw [g28, h28]) (by rw [g12, h12]) (by rw [g13, g30, h13]; bv_omega) (by rw [g30]; bv_omega) (by rw [g11]; bv_omega)
      (by rw [g11]; bv_omega) (by rw [g30]; bv_omega) (by rw [g11, g30]; bv_omega) hprev'
      (by rw [g11, B_ram] at *; constructor <;> bv_omega) (by rw [g30, B_ram] at *; constructor <;> bv_omega)
    have hwords : words ram (c.get 11 + BitVec.ofNat 32 o) (c.get 30) (j + 1 + 1) =
        words R1 ((c11.goto 0x80020f2e).get 11 + BitVec.ofNat 32 o) ((c11.goto 0x80020f2e).get 30) (j + 1) := by
      simp only [words]; rw [← hw, g11, g30,
        show c.get 11 + 4 + BitVec.ofNat 32 o = c.get 11 + BitVec.ofNat 32 o + 4 by bv_omega]
    refine ⟨9 + 1 + n, c', ?_, hpc', hcs.trans ((Core.sameCsr_goto _ _).trans cs11), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hwords]; exact (hb.trans (.single q11 s11)).trans hr
    · rw [h11', g11]; bv_omega
    · rw [h30', g30]; bv_omega
    · rw [h28', g28]
    · rw [h13', g13]
    · rw [h12', g12]
    · intro k hk1 hk2; rw [hwords]; exact hpv k hk1 hk2
    · intro r a b d e f
      rw [hfr r a b d e f, Core.goto_get]; exact misBody_get c ram r a b d e f

end E5R.Rmk
