/-
  memmove, backward direction, n ≥ 16, source and destination NOT
  congruent mod 4: the shift/merge loop at 0x80021012 (pinned RMK image),
  for every iteration count.

  Original e5r code, Apache-2.0.

    0x80021012  mv a1,a5; add a3,t5,s2; lw a5,-4(a3); sll a1,a1,a2;
                srl a3,a5,t4; or a1,a1,a3; add a3,s1,s2; addi s1,s1,-4;
                sw a1,-4(a3); add a1,s1,s2; addi t5,t5,-4; bltu t3,a1,0x80021012

  `a5` holds the word above the one loaded (its low `o` bytes are the
  source bytes just above); `s2 = -H` offsets both pointers; `t4 = 8 o`,
  `a2 = 32 - 8 o`.
-/
import Projects.rmk.MemmoveMisLoop

set_option maxRecDepth 100000

namespace E5R.Rmk
open E5R E5R.Rmk.MemmoveFetch

def bmisBody (c : Core) (ram : Word → BitVec 8) : Core :=
  let L := c.get 30 + c.get 18
  let nw := ramRead ram (L + 0xfffffffc#32) .w
  let v := alu .or (alu .sll (alu .add 0 (c.get 15)) (c.get 12)) (alu .srl nw (c.get 29))
  ((((((((((c.wr 11 (alu .add 0 (c.get 15)) 0x80021014).wr 13 L 0x80021018).wr 15 nw 0x8002101c).wr 11
    (alu .sll (alu .add 0 (c.get 15)) (c.get 12)) 0x80021020).wr 13 (alu .srl nw (c.get 29)) 0x80021024).wr 11
    v 0x80021026).wr 13 (c.get 9 + c.get 18) 0x8002102a).wr 9 (c.get 9 + 0xfffffffc#32) 0x8002102c).goto
    0x80021030).wr 11 (c.get 9 + 0xfffffffc#32 + c.get 18) 0x80021034).wr 30 (c.get 30 + 0xfffffffc#32)
    0x80021036

def bmisVal (c : Core) (ram : Word → BitVec 8) : Word :=
  alu .or (alu .sll (alu .add 0 (c.get 15)) (c.get 12))
    (alu .srl (ramRead ram (c.get 30 + c.get 18 + 0xfffffffc#32) .w) (c.get 29))

theorem bmisBody_sameCsr (c : Core) (ram) : (bmisBody c ram).sameCsr c := by
  unfold bmisBody
  exact (Core.sameCsr_wr _ _ _ _).trans <| (Core.sameCsr_wr _ _ _ _).trans <| (Core.sameCsr_goto _ _).trans <|
    (Core.sameCsr_wr _ _ _ _).trans <| (Core.sameCsr_wr _ _ _ _).trans <| (Core.sameCsr_wr _ _ _ _).trans <|
    (Core.sameCsr_wr _ _ _ _).trans <| (Core.sameCsr_wr _ _ _ _).trans <| (Core.sameCsr_wr _ _ _ _).trans <|
    (Core.sameCsr_wr _ _ _ _).trans (Core.sameCsr_wr _ _ _ _)

theorem bmisBody_get (c : Core) (ram) (r : Reg) (h9 : r ≠ 9) (h11 : r ≠ 11) (h13 : r ≠ 13)
    (h15 : r ≠ 15) (h30 : r ≠ 30) : (bmisBody c ram).get r = c.get r := by
  simp [bmisBody, Core.wr_get_ne, h9, h11, h13, h15, h30]

theorem bmis_body (c : Core) (ram : Word → BitVec 8) (hpc : c.pc = 0x80021012) (hq : Quiet c)
    (hA : (c.get 30 + c.get 18 + 0xfffffffc#32).toNat % 4 = 0)
    (hD : (c.get 9 + c.get 18 + 0xfffffffc#32).toNat % 4 = 0)
    (hs : B.inRam (c.get 30 + c.get 18 + 0xfffffffc#32) 4 = true)
    (hd : B.inRam (c.get 9 + c.get 18 + 0xfffffffc#32) 4 = true) :
    QRun B img 11 ⟨c, ram⟩ ⟨bmisBody c ram, ramWrite ram (c.get 9 + c.get 18 + 0xfffffffc#32) (bmisVal c ram) .w⟩ := by
  let L := c.get 30 + c.get 18
  let nw := ramRead ram (L + 0xfffffffc#32) .w
  let c1 := c.wr 11 (alu .add 0 (c.get 15)) 0x80021014
  let c2 := c1.wr 13 L 0x80021018
  let c3 := c2.wr 15 nw 0x8002101c
  let c4 := c3.wr 11 (alu .sll (alu .add 0 (c.get 15)) (c.get 12)) 0x80021020
  let c5 := c4.wr 13 (alu .srl nw (c.get 29)) 0x80021024
  let c6 := c5.wr 11 (bmisVal c ram) 0x80021026
  let c7 := c6.wr 13 (c.get 9 + c.get 18) 0x8002102a
  let c8 := c7.wr 9 (c.get 9 + 0xfffffffc#32) 0x8002102c
  let c9 := c8.goto 0x80021030
  let c10 := c9.wr 11 (c.get 9 + 0xfffffffc#32 + c.get 18) 0x80021034
  let R1 := ramWrite ram (c.get 9 + c.get 18 + 0xfffffffc#32) (bmisVal c ram) .w
  have q1 : Quiet c1 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) hq
  have q2 : Quiet c2 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q1
  have q3 : Quiet c3 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q2
  have q4 : Quiet c4 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q3
  have q5 : Quiet c5 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q4
  have q6 : Quiet c6 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q5
  have q7 : Quiet c7 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q6
  have q8 : Quiet c8 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q7
  have q9 : Quiet c9 := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q8
  have q10 : Quiet c10 := Quiet.of_sameCsr (Core.sameCsr_wr _ _ _ _) q9
  have s1 : DetStep B img ⟨c, ram⟩ ⟨c1, ram⟩ := by
    refine detStep_of (by rw [hpc]; decide) (by rw [hpc]; exact f80021012) fun o => ?_
    rw [exec_op, Core.get_zero, hpc]; rfl
  have s2 : DetStep B img ⟨c1, ram⟩ ⟨c2, ram⟩ := by
    refine detStep_of (by show (0x80021014 : Word).getLsbD 0 = false; decide) f80021014 fun o => ?_
    rw [exec_op, show c1.get 30 = c.get 30 by simp [c1, Core.wr_get_ne],
      show c1.get 18 = c.get 18 by simp [c1, Core.wr_get_ne]]; rfl
  have s3 : DetStep B img ⟨c2, ram⟩ ⟨c3, ram⟩ := by
    refine detStep_of (by show (0x80021018 : Word).getLsbD 0 = false; decide) f80021018 fun o => ?_
    rw [exec_load, show c2.get 13 = L by simp [c2, Core.wr_get_self],
      interp_load_ram (w := .w) o hA hs]; rfl
  have s4 : DetStep B img ⟨c3, ram⟩ ⟨c4, ram⟩ := by
    refine detStep_of (by show (0x8002101c : Word).getLsbD 0 = false; decide) f8002101c fun o => ?_
    rw [exec_op, show c3.get 11 = alu .add 0 (c.get 15) by simp [c3, c2, c1, Core.wr_get_ne, Core.wr_get_self],
      show c3.get 12 = c.get 12 by simp [c3, c2, c1, Core.wr_get_ne]]; rfl
  have s5 : DetStep B img ⟨c4, ram⟩ ⟨c5, ram⟩ := by
    refine detStep_of (by show (0x80021020 : Word).getLsbD 0 = false; decide) f80021020 fun o => ?_
    rw [exec_op, show c4.get 15 = nw by simp [c4, c3, Core.wr_get_ne, Core.wr_get_self],
      show c4.get 29 = c.get 29 by simp [c4, c3, c2, c1, Core.wr_get_ne]]; rfl
  have s6 : DetStep B img ⟨c5, ram⟩ ⟨c6, ram⟩ := by
    refine detStep_of (by show (0x80021024 : Word).getLsbD 0 = false; decide) f80021024 fun o => ?_
    rw [exec_op, show c5.get 11 = alu .sll (alu .add 0 (c.get 15)) (c.get 12) by
        simp [c5, c4, Core.wr_get_ne, Core.wr_get_self],
      show c5.get 13 = alu .srl nw (c.get 29) by simp [c5, Core.wr_get_self]]; rfl
  have s7 : DetStep B img ⟨c6, ram⟩ ⟨c7, ram⟩ := by
    refine detStep_of (by show (0x80021026 : Word).getLsbD 0 = false; decide) f80021026 fun o => ?_
    rw [exec_op, show c6.get 9 = c.get 9 by simp [c6, c5, c4, c3, c2, c1, Core.wr_get_ne],
      show c6.get 18 = c.get 18 by simp [c6, c5, c4, c3, c2, c1, Core.wr_get_ne]]; rfl
  have s8 : DetStep B img ⟨c7, ram⟩ ⟨c8, ram⟩ := by
    refine detStep_of (by show (0x8002102a : Word).getLsbD 0 = false; decide) f8002102a fun o => ?_
    rw [exec_opimm, show c7.get 9 = c.get 9 by simp [c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne]]; rfl
  have s9 : DetStep B img ⟨c8, ram⟩ ⟨c9, R1⟩ := by
    refine detStep_of (by show (0x8002102c : Word).getLsbD 0 = false; decide) f8002102c fun o => ?_
    rw [exec_store, show c8.get 13 = c.get 9 + c.get 18 by simp [c8, c7, Core.wr_get_ne, Core.wr_get_self],
      show c8.get 11 = bmisVal c ram by simp [c8, c7, c6, Core.wr_get_ne, Core.wr_get_self],
      interp_store_ram (w := .w) o hD hd]; rfl
  have s10 : DetStep B img ⟨c9, R1⟩ ⟨c10, R1⟩ := by
    refine detStep_of (by show (0x80021030 : Word).getLsbD 0 = false; decide) f80021030 fun o => ?_
    rw [exec_op, show c9.get 9 = c.get 9 + 0xfffffffc#32 by simp [c9, c8, Core.wr_get_self],
      show c9.get 18 = c.get 18 by simp [c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne]]; rfl
  have s11 : DetStep B img ⟨c10, R1⟩ ⟨bmisBody c ram, R1⟩ := by
    refine detStep_of (by show (0x80021034 : Word).getLsbD 0 = false; decide) f80021034 fun o => ?_
    rw [exec_opimm, show c10.get 30 = c.get 30 by simp [c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, Core.wr_get_ne]]
    rfl
  exact .step hq s1 (.step q1 s2 (.step q2 s3 (.step q3 s4 (.step q4 s5 (.step q5 s6
    (.step q6 s7 (.step q7 s8 (.step q8 s9 (.step q9 s10 (.single q10 s11))))))))))

theorem bmisVal_eq (c : Core) (ram : Word → BitVec 8) (o : Nat) (ho : 0 < o ∧ o < 4)
    (h29 : c.get 29 = BitVec.ofNat 32 (8 * o)) (h12 : c.get 12 = (0 - BitVec.ofNat 32 (8 * o)) &&& 0x18#32) :
    bmisVal c ram =
      (ramRead ram (c.get 30 + c.get 18 + 0xfffffffc#32) .w >>> (8 * o)) ||| (c.get 15 <<< (32 - 8 * o)) := by
  obtain ⟨e1, e2⟩ := shifts o ho
  simp only [bmisVal, alu, h29, h12, e1, e2]
  rw [show (0 : Word) + c.get 15 = c.get 15 by bv_omega, BitVec.or_comm]

/-- Arithmetic of one backward merge iteration (`J + 1` words left), kept
    out of the loop's large proof context. -/
structure BMArith (x30 x18 x9 x28 : Word) (o J : Nat) : Prop where
  a : (x30 + x18 + 0xfffffffc#32).toNat % 4 = 0
  b : (x9 + x18 + 0xfffffffc#32).toNat % 4 = 0
  c : 0x80029bc8 ≤ (x30 + x18 + 0xfffffffc#32).toNat ∧ (x30 + x18 + 0xfffffffc#32).toNat + 4 ≤ 0x81000000
  d : 0x80029bc8 ≤ (x9 + x18 + 0xfffffffc#32).toNat ∧ (x9 + x18 + 0xfffffffc#32).toNat + 4 ≤ 0x81000000
  e0 : J = 0 → x28.ult (x9 + 0xfffffffc#32 + x18) = false
  e1 : 0 < J → x28.ult (x9 + 0xfffffffc#32 + x18) = true
  pv : ∀ k, x30 + x18 + BitVec.ofNat 32 k = x30 + x18 + 0xfffffffc#32 + 4 + BitVec.ofNat 32 k
  dj : ∀ k < o, ∀ m < 4, x30 + 0xfffffffc#32 + x18 + BitVec.ofNat 32 k ≠ x9 + x18 + 0xfffffffc#32 + BitVec.ofNat 32 m
  g : ∀ k, x30 + 0xfffffffc#32 + x18 + BitVec.ofNat 32 k = x30 + x18 + 0xfffffffc#32 + BitVec.ofNat 32 k
  i1 : x9 + 0xfffffffc#32 + x18 = x28 + BitVec.ofNat 32 (4 * J)
  i2 : 0 < J → x28.toNat + 4 * J < 2 ^ 32
  i3 : 4 * J ≤ (x30 + 0xfffffffc#32 + x18).toNat
  i4 : (x30 + 0xfffffffc#32 + x18).toNat % 4 = 0
  i5 : (x30 + 0xfffffffc#32 + x18).toNat + o ≤ (x9 + 0xfffffffc#32 + x18).toNat
  i6 : 0 < J → 0x80029bc8 ≤ (x30 + 0xfffffffc#32 + x18 - BitVec.ofNat 32 (4 * J)).toNat ∧
    (x30 + 0xfffffffc#32 + x18 - BitVec.ofNat 32 (4 * J)).toNat + 4 * J ≤ 0x81000000
  i7 : 0 < J → 0x80029bc8 ≤ x28.toNat ∧ x28.toNat + 4 * J ≤ 0x81000000
  w1 : x30 + x18 + 0xfffffffc#32 + BitVec.ofNat 32 o + 0xfffffffc#32 =
    x30 + 0xfffffffc#32 + x18 + 0xfffffffc#32 + BitVec.ofNat 32 o
  w2 : x9 + x18 + 0xfffffffc#32 = x9 + 0xfffffffc#32 + x18
  r30 : x30 + 0xfffffffc#32 - BitVec.ofNat 32 (4 * J) = x30 - BitVec.ofNat 32 (4 * (J + 1))
  r9 : x9 + 0xfffffffc#32 - BitVec.ofNat 32 (4 * J) = x9 - BitVec.ofNat 32 (4 * (J + 1))

theorem bm_arith (x30 x18 x9 x28 : Word) (o J : Nat) (ho : 0 < o ∧ o < 4)
    (hD : x9 + x18 = x28 + BitVec.ofNat 32 (4 * (J + 1)))
    (hdl : x28.toNat + 4 * (J + 1) < 2 ^ 32) (hlo : 4 * (J + 1) ≤ (x30 + x18).toNat)
    (hA : (x30 + x18).toNat % 4 = 0) (hT : x28.toNat % 4 = 0)
    (hdir : (x30 + x18).toNat + o ≤ (x9 + x18).toNat)
    (hsr : 0x80029bc8 ≤ (x30 + x18 - BitVec.ofNat 32 (4 * (J + 1))).toNat ∧
      (x30 + x18 - BitVec.ofNat 32 (4 * (J + 1))).toNat + 4 * (J + 1) ≤ 0x81000000)
    (hdr : 0x80029bc8 ≤ x28.toNat ∧ x28.toNat + 4 * (J + 1) ≤ 0x81000000) :
    BMArith x30 x18 x9 x28 o J := by
  have a1 : ∀ k, x30 + k + x18 = x30 + x18 + k := fun k => by
    rw [BitVec.add_assoc, BitVec.add_comm k, ← BitVec.add_assoc]
  have a2 : ∀ k, x9 + k + x18 = x9 + x18 + k := fun k => by
    rw [BitVec.add_assoc, BitVec.add_comm k, ← BitVec.add_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (try intro k); all_goals (try intro hk); all_goals (try intro m); all_goals (try intro hm)
  all_goals (try simp only [a1, a2])
  all_goals (try simp only [BitVec.ult, decide_eq_false_iff_not, decide_eq_true_iff])
  all_goals (clear a1 a2; (try generalize x30 + x18 = L at *); (try generalize x9 + x18 = Q at *))
  all_goals (try refine ⟨?_, ?_⟩)
  all_goals (try subst k)
  all_goals bv_omega

/-- The backward misaligned loop: `j+1` merged words stored down from
    `s1 + s2`, the source being the bytes below `t5 + s2 + o`; ends at
    0x8002103a with `a5` the last word loaded. -/
theorem bmis_loop (o : Nat) (ho : 0 < o ∧ o < 4) : ∀ (j : Nat) (c : Core) (ram : Word → BitVec 8),
    c.pc = 0x80021012 → Quiet c → c.get 29 = BitVec.ofNat 32 (8 * o) →
    c.get 12 = (0 - BitVec.ofNat 32 (8 * o)) &&& 0x18#32 →
    c.get 9 + c.get 18 = c.get 28 + BitVec.ofNat 32 (4 * (j + 1)) →
    (c.get 28).toNat + 4 * (j + 1) < 2 ^ 32 → 4 * (j + 1) ≤ (c.get 30 + c.get 18).toNat →
    (c.get 30 + c.get 18).toNat % 4 = 0 → (c.get 28).toNat % 4 = 0 →
    (c.get 30 + c.get 18).toNat + o ≤ (c.get 9 + c.get 18).toNat →
    (∀ k, k < o → byteOf (c.get 15) k = ram (c.get 30 + c.get 18 + BitVec.ofNat 32 k)) →
    B.inRam (c.get 30 + c.get 18 - BitVec.ofNat 32 (4 * (j + 1))) (4 * (j + 1)) = true →
    B.inRam (c.get 28) (4 * (j + 1)) = true →
    ∃ n c', QRun B img n ⟨c, ram⟩
        ⟨c', wordsB ram (c.get 30 + c.get 18 + 0xfffffffc#32 + BitVec.ofNat 32 o) (c.get 9 + c.get 18) (j + 1)⟩ ∧
      c'.pc = 0x8002103a ∧ c'.sameCsr c ∧
      c'.get 30 = c.get 30 - BitVec.ofNat 32 (4 * (j + 1)) ∧ c'.get 9 = c.get 9 - BitVec.ofNat 32 (4 * (j + 1)) ∧
      (∀ k, k < o → byteOf (c'.get 15) k =
        wordsB ram (c.get 30 + c.get 18 + 0xfffffffc#32 + BitVec.ofNat 32 o) (c.get 9 + c.get 18) (j + 1)
          (c'.get 30 + c.get 18 + BitVec.ofNat 32 k)) ∧
      ∀ r : Reg, r ≠ 9 → r ≠ 11 → r ≠ 13 → r ≠ 15 → r ≠ 30 → c'.get r = c.get r := by
  intro j
  induction j with
  | zero =>
    intro c ram hpc hq h29 h12 hD hdl hlo hA hT hdir hprev hs hd
    have ar := bm_arith (c.get 30) (c.get 18) (c.get 9) (c.get 28) o 0 ho hD hdl hlo hA hT hdir
      ((B_ram _ _).mp hs) ((B_ram _ _).mp hd)
    have hb := bmis_body c ram hpc hq ar.a ar.b ((B_ram _ _).mpr ar.c) ((B_ram _ _).mpr ar.d)
    let c11 := bmisBody c ram
    have q11 : Quiet c11 := Quiet.of_sameCsr (bmisBody_sameCsr c ram) hq
    let R1 := ramWrite ram (c.get 9 + c.get 18 + 0xfffffffc#32) (bmisVal c ram) .w
    have s11 : DetStep B img ⟨c11, R1⟩ ⟨c11.goto 0x8002103a, R1⟩ := by
      refine detStep_of (by show (0x80021036 : Word).getLsbD 0 = false; decide) f80021036 fun o => ?_
      rw [exec_branch]
      have e11 : c11.get 11 = c.get 9 + 0xfffffffc#32 + c.get 18 := by
        simp [c11, bmisBody, Core.wr_get_ne, Core.wr_get_self]
      have e28 : c11.get 28 = c.get 28 := by simp [c11, bmisBody, Core.wr_get_ne]
      rw [e11, e28]; simp only [taken, ar.e0 rfl, Bool.false_eq_true, ite_false]; rfl
    have hw : R1 = ramWrite ram (c.get 9 + c.get 18 + 0xfffffffc#32)
        (ramRead ram (c.get 30 + c.get 18 + 0xfffffffc#32 + BitVec.ofNat 32 o) .w) .w := by
      show ramWrite ram _ (bmisVal c ram) .w = _
      rw [bmisVal_eq c ram o ho h29 h12]
      refine merge_store_q ram ram _ _ _ _ o ho (fun k _ hk => byte_read_k _ _ _ hk) (fun k hk => ?_)
      rw [hprev k hk, ar.pv k]
    have g30 : (c11.goto 0x8002103a).get 30 = c.get 30 + 0xfffffffc#32 := by
      simp [c11, bmisBody, Core.wr_get_ne, Core.wr_get_self]
    have g9 : (c11.goto 0x8002103a).get 9 = c.get 9 + 0xfffffffc#32 := by
      simp [c11, bmisBody, Core.wr_get_ne, Core.wr_get_self]
    refine ⟨12, c11.goto 0x8002103a, ?_, rfl, (Core.sameCsr_goto _ _).trans (bmisBody_sameCsr c ram), ?_, ?_, ?_, ?_⟩
    · have := hb.trans (.single q11 s11)
      simp only [wordsB]; rw [← hw]
      exact this
    · rw [g30, ← ar.r30]; simp
    · rw [g9, ← ar.r9]; simp
    · intro k hk
      have g15 : (c11.goto 0x8002103a).get 15 = ramRead ram (c.get 30 + c.get 18 + 0xfffffffc#32) .w := by
        simp [c11, bmisBody, Core.wr_get_ne, Core.wr_get_self]
      rw [g15, g30, byte_read_k _ _ _ (by omega)]
      simp only [wordsB]
      rw [← hw]
      show ram _ = ramWrite ram (c.get 9 + c.get 18 + 0xfffffffc#32) (bmisVal c ram) .w _
      rw [ramWrite_w_other _ _ _ _ (ar.dj k hk), ar.g k]
    · intro r a b d e f; simp only [Core.goto_get]; exact bmisBody_get c ram r a b d e f
  | succ j ih =>
    intro c ram hpc hq h29 h12 hD hdl hlo hA hT hdir hprev hs hd
    have ar := bm_arith (c.get 30) (c.get 18) (c.get 9) (c.get 28) o (j + 1) ho hD hdl hlo hA hT hdir
      ((B_ram _ _).mp hs) ((B_ram _ _).mp hd)
    have hb := bmis_body c ram hpc hq ar.a ar.b ((B_ram _ _).mpr ar.c) ((B_ram _ _).mpr ar.d)
    let c11 := bmisBody c ram
    have cs11 : c11.sameCsr c := bmisBody_sameCsr c ram
    have q11 : Quiet c11 := Quiet.of_sameCsr cs11 hq
    let R1 := ramWrite ram (c.get 9 + c.get 18 + 0xfffffffc#32) (bmisVal c ram) .w
    have s11 : DetStep B img ⟨c11, R1⟩ ⟨c11.goto 0x80021012, R1⟩ := by
      refine detStep_of (by show (0x80021036 : Word).getLsbD 0 = false; decide) f80021036 fun o => ?_
      rw [exec_branch]
      have e11 : c11.get 11 = c.get 9 + 0xfffffffc#32 + c.get 18 := by
        simp [c11, bmisBody, Core.wr_get_ne, Core.wr_get_self]
      have e28 : c11.get 28 = c.get 28 := by simp [c11, bmisBody, Core.wr_get_ne]
      rw [e11, e28]; simp only [taken, ar.e1 (Nat.succ_pos j), ite_true]
      have hp : c11.pc + 0xffffffdc#32 = 0x80021012 := by rw [show c11.pc = 0x80021036 from rfl]; decide
      rw [hp, jump_ok _ _ (by decide)]; rfl
    have hw : R1 = ramWrite ram (c.get 9 + c.get 18 + 0xfffffffc#32)
        (ramRead ram (c.get 30 + c.get 18 + 0xfffffffc#32 + BitVec.ofNat 32 o) .w) .w := by
      show ramWrite ram _ (bmisVal c ram) .w = _
      rw [bmisVal_eq c ram o ho h29 h12]
      refine merge_store_q ram ram _ _ _ _ o ho (fun k _ hk => byte_read_k _ _ _ hk) (fun k hk => ?_)
      rw [hprev k hk, ar.pv k]
    have q12 : Quiet (c11.goto 0x80021012) := Quiet.of_sameCsr (Core.sameCsr_goto _ _) q11
    have g9 : (c11.goto 0x80021012).get 9 = c.get 9 + 0xfffffffc#32 := by
      simp [c11, bmisBody, Core.wr_get_ne, Core.wr_get_self]
    have g30 : (c11.goto 0x80021012).get 30 = c.get 30 + 0xfffffffc#32 := by
      simp [c11, bmisBody, Core.wr_get_ne, Core.wr_get_self]
    have g18 : (c11.goto 0x80021012).get 18 = c.get 18 := by simp [c11, bmisBody, Core.wr_get_ne]
    have g28 : (c11.goto 0x80021012).get 28 = c.get 28 := by simp [c11, bmisBody, Core.wr_get_ne]
    have g29 : (c11.goto 0x80021012).get 29 = c.get 29 := by simp [c11, bmisBody, Core.wr_get_ne]
    have g12 : (c11.goto 0x80021012).get 12 = c.get 12 := by simp [c11, bmisBody, Core.wr_get_ne]
    have g15 : (c11.goto 0x80021012).get 15 = ramRead ram (c.get 30 + c.get 18 + 0xfffffffc#32) .w := by
      simp [c11, bmisBody, Core.wr_get_ne, Core.wr_get_self]
    have hprev' : ∀ k, k < o → byteOf ((c11.goto 0x80021012).get 15) k =
        R1 ((c11.goto 0x80021012).get 30 + (c11.goto 0x80021012).get 18 + BitVec.ofNat 32 k) := by
      intro k hk
      rw [g15, g30, g18, byte_read_k _ _ _ (by omega)]
      show ram _ = ramWrite ram (c.get 9 + c.get 18 + 0xfffffffc#32) (bmisVal c ram) .w _
      rw [ramWrite_w_other _ _ _ _ (ar.dj k hk), ar.g k]
    obtain ⟨n, c', hr, hpc', hcs, h30', h9', hpv, hfr⟩ := ih (c11.goto 0x80021012) R1 rfl q12
      (by rw [g29, h29]) (by rw [g12, h12]) (by rw [g9, g18, g28]; exact ar.i1)
      (by rw [g28]; exact ar.i2 (Nat.succ_pos j)) (by rw [g30, g18]; exact ar.i3)
      (by rw [g30, g18]; exact ar.i4) (by rw [g28]; exact hT)
      (by rw [g30, g18, g9]; exact ar.i5) hprev'
      (by rw [g30, g18]; exact (B_ram _ _).mpr (ar.i6 (Nat.succ_pos j)))
      (by rw [g28]; exact (B_ram _ _).mpr (ar.i7 (Nat.succ_pos j)))
    have hwords : wordsB ram (c.get 30 + c.get 18 + 0xfffffffc#32 + BitVec.ofNat 32 o) (c.get 9 + c.get 18)
        (j + 1 + 1) =
        wordsB R1 ((c11.goto 0x80021012).get 30 + (c11.goto 0x80021012).get 18 + 0xfffffffc#32 + BitVec.ofNat 32 o)
          ((c11.goto 0x80021012).get 9 + (c11.goto 0x80021012).get 18) (j + 1) := by
      simp only [wordsB]; rw [← hw, g30, g9, g18, ar.w1, ar.w2]
    refine ⟨11 + 1 + n, c', ?_, hpc', hcs.trans ((Core.sameCsr_goto _ _).trans cs11), ?_, ?_, ?_, ?_⟩
    · rw [hwords]; exact (hb.trans (.single q11 s11)).trans hr
    · rw [h30', g30, ar.r30]
    · rw [h9', g9, ar.r9]
    · intro k hk; rw [hwords]; have := hpv k hk; rw [g18] at this; exact this
    · intro r a b d e f
      rw [hfr r a b d e f, Core.goto_get]; exact bmisBody_get c ram r a b d e f

end E5R.Rmk
