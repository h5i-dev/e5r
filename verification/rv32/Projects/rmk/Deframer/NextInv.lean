/-
  `Deframer::next` (0x8001d43a) on the pinned RMK image: the invariant at the frame loop head
  0x8001d476, and the prologue establishing it.

  Original e5r code, Apache-2.0.

  PROVED here: `head`: from every machine meeting `next`'s precondition (`CallEnv nextPc nextStack`,
  the deframer invariant, discarding ≤ 1), a quiet run reaches the loop head with `LoopInv`.
  The loop itself, the exits and `NextContract` are not proved here.
-/
import Projects.rmk.Deframer.NextParts
import Projects.rmk.Deframer.NextSegs

set_option maxRecDepth 100000

namespace E5R.Rmk.Deframer.Next
open E5R E5R.Rmk.NextFetch E5R.Rmk.Deframer.Tail

/-- `next`'s stack pointer after `addi sp, sp, -0x40`. -/
def ng (c : Core) : Word := c.get 2 + 0xffffffc0#32

/-- The 13 save slots: (offset from ng, register). -/
def nslots : List (Nat × Reg) :=
  [(0x3c, 1), (0x38, 8), (0x34, 9), (0x30, 18), (0x2c, 19), (0x28, 20), (0x24, 21), (0x20, 22),
   (0x1c, 23), (0x18, 24), (0x14, 25), (0x10, 26), (0xc, 27)]

def NSlots (c : Core) (M : Word → BitVec 8) : Prop :=
  ∀ o r, (o, r) ∈ nslots → ramRead M (ng c + BitVec.ofNat 32 o) .w = c.get r

/-- The registers `next` never writes (all others it saves, or may clobber by the ABI). -/
def nkept : List Nat := [0, 3, 4]

/-- At the frame loop head 0x8001d476: s0 = filled, s1 = cursor (= consumed), s2 = len,
    s3 = self, s4 = buf, s7 = a0 = the discarding flag, s8 = -filled, s9 = -1, s10 = 2. -/
structure LoopInv (c : Core) (R0 : Word → BitVec 8) (d : Core) (M : Word → BitVec 8) : Prop where
  pc : d.pc = 0x8001d476
  quiet : Quiet d
  csr : d.sameCsr c
  sp : d.get 2 = ng c
  len : d.get 18 = c.get 12
  self : d.get 19 = c.get 10
  buf : d.get 20 = c.get 11
  s7 : (d.get 23).toNat ≤ 1
  a0 : d.get 10 = d.get 23
  s8 : d.get 24 = 0 - d.get 8
  s9 : d.get 25 = 0xffffffff#32
  s10 : d.get 26 = 2#32
  kept : ∀ r : Reg, r.val ∈ nkept → d.get r = c.get r
  curle : (d.get 9).toNat ≤ (d.get 8).toNat
  fle : (d.get 8).toNat ≤ (c.get 12).toNat
  slots : NSlots c M
  fcur : ramRead M (c.get 10) .w = d.get 9
  ffil : ramRead M (c.get 10 + 4) .w = d.get 8
  fdisc : (M (c.get 10 + 8)).toNat = (d.get 23).toNat
  ram : ∀ x, Outside (c.get 10) (c.get 11) (c.get 12).toNat (c.get 2) nextStack x → M x = R0 x

/-! ## The saves -/

section Saves
variable (c : Core) (ram : Word → BitVec 8)
  (hs : 0x80029bc8 + 0x40 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000)
include hs

theorem nsaves_other (x : Word) (hx : x.toNat < (c.get 2).toNat - 0x40 ∨ (c.get 2).toNat ≤ x.toNat) :
    nsavesRam c ram x = ram x := by
  simp only [nsavesRam, alu_add]
  repeat rw [wr_byte_other _ _ _ _ (by bv_omega) (by bv_omega)]

theorem nsaves_rd (a : Word) (ha : a.toNat + 4 ≤ (c.get 2).toNat - 0x40) :
    ramRead (nsavesRam c ram) a .w = ramRead ram a .w :=
  rd_congr a (by omega) fun x _ h2 => nsaves_other c ram hs x (.inl (by omega))

theorem nsaves_slots : NSlots c (nsavesRam c ram) := by
  intro o r h
  simp only [nslots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  simp only [nsavesRam, ng, alu_add]
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · repeat (first | rw [ramRead_ramWrite_w] | rw [rd_wr_other _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega)])

end Saves

theorem nsaves_get (c ram) (r : Reg) (h : r ≠ 2) : (nsavesCore c ram).get r = c.get r := by
  simp [nsavesCore, Core.wr_get_ne, h]
theorem nsaves_get2 (c ram) : (nsavesCore c ram).get 2 = ng c := by
  simp [nsavesCore, Core.wr_get_self, ng, alu_add]
theorem nsaves_sameCsr (c ram) : (nsavesCore c ram).sameCsr c := by
  unfold nsavesCore
  repeat (first | exact Core.sameCsr_wr _ _ _ _ | refine (Core.sameCsr_goto _ _).trans ?_ | refine (Core.sameCsr_wr _ _ _ _).trans ?_)

theorem nentry_sameCsr (d R) : (nentryCore d R).sameCsr d := by
  unfold nentryCore
  repeat (first | exact Core.sameCsr_wr _ _ _ _ | refine (Core.sameCsr_goto _ _).trans ?_ | refine (Core.sameCsr_wr _ _ _ _).trans ?_)

/-! ## The prologue reaches the loop head with the invariant -/

theorem head (c : Core) (R0 : Word → BitVec 8) (E : CallEnv nextPc nextStack ⟨c, R0⟩)
    (hI : Inv R0 (c.get 10) (c.get 12).toNat) (hd : discarding R0 (c.get 10) ≤ 1) :
    ∃ k d M, QRun B img k ⟨c, R0⟩ ⟨d, M⟩ ∧ LoopInv c R0 d M := by
  have hpc : c.pc = 0x8001d43a := E.pc
  have hst := stack_nat (c.get 2) nextStack E.stack
  rw [show nextStack = 0x70 from rfl] at hst
  have hs : 0x80029bc8 + 0x40 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000 := ⟨by omega, hst.2⟩
  have hp := (B_ram (c.get 10) 12).mp E.self
  have hsep : (c.get 10).toNat + 12 ≤ (c.get 2).toNat - 0x70 ∧
      (c.get 11).toNat + (c.get 12).toNat ≤ (c.get 2).toNat - 0x70 := E.stackSep
  have hI : consumed R0 (c.get 10) ≤ filled R0 (c.get 10) ∧ filled R0 (c.get 10) ≤ (c.get 12).toNat := hI
  have hd : (R0 (c.get 10 + 8)).toNat ≤ 1 := hd
  have r1 := nsaves c R0 hpc E.quiet E.spAl hs
  let d0 := nsavesCore c R0
  let R1 := nsavesRam c R0
  have g10 : d0.get 10 = c.get 10 := nsaves_get c R0 10 (by decide)
  have g12 : d0.get 12 = c.get 12 := nsaves_get c R0 12 (by decide)
  have e4 : (c.get 10 + 0x4#32).toNat = (c.get 10).toNat + 4 := add_toNat _ 4 (by omega)
  have e8 : (c.get 10 + 0x8#32).toNat = (c.get 10).toNat + 8 := add_toNat _ 8 (by omega)
  have rc : ramRead R1 (c.get 10) .w = ramRead R0 (c.get 10) .w := nsaves_rd c R0 hs _ (by omega)
  have rf : ramRead R1 (c.get 10 + 0x4#32) .w = ramRead R0 (c.get 10 + 0x4#32) .w :=
    nsaves_rd c R0 hs _ (by omega)
  have rd8 : R1 (c.get 10 + 0x8#32) = R0 (c.get 10 + 0x8#32) := nsaves_other c R0 hs _ (.inl (by omega))
  have qd0 : Quiet d0 := Quiet.of_sameCsr (nsaves_sameCsr c R0) E.quiet
  have hle : (ramRead R1 (d0.get 10 + 0x4#32) .w).toNat ≤ (d0.get 12).toNat := by
    rw [g10, g12, rf]; exact hI.2
  have hcf : (ramRead R1 (d0.get 10) .w).toNat ≤ (ramRead R1 (d0.get 10 + 0x4#32) .w).toNat := by
    rw [g10, rc, rf]; exact hI.1
  have r2 := nentry d0 R1 rfl qd0 (by rw [g10]; exact E.selfAl) (by rw [g10]; exact hp) hle hcf
  refine ⟨_, _, _, r1.trans r2, ?_⟩
  let d := nentryCore d0 R1
  have dg : ∀ r : Reg, r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 23 → r ≠ 24 → r ≠ 25 →
      r ≠ 26 → d.get r = d0.get r := fun r a b c' d' e' f' g' h' i' j' => by
    simp [d, nentryCore, Core.wr_get_ne, a, b, c', d', e', f', g', h', i', j']
  have v8 : d.get 8 = ramRead R0 (c.get 10 + 0x4#32) .w := by
    simp [d, nentryCore, Core.wr_get_ne, Core.wr_get_self, g10, rf]
  have v9 : d.get 9 = ramRead R0 (c.get 10) .w := by
    simp [d, nentryCore, Core.wr_get_ne, Core.wr_get_self, g10, rc]
  have v23 : d.get 23 = BitVec.ofNat 32 (R0 (c.get 10 + 0x8#32)).toNat := by
    simp only [d, nentryCore, Core.wr_get_ne _ _ _ _ _ (show (23 : Reg) ≠ 10 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (23 : Reg) ≠ 26 by decide), Core.wr_get_ne _ _ _ _ _ (show (23 : Reg) ≠ 25 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (23 : Reg) ≠ 24 by decide),
      Core.wr_get_self _ _ _ _ (show (23 : Reg).val ≠ 0 by decide), g10, lbu_val, ← rd8]
  have h23 : (d.get 23).toNat = (R0 (c.get 10 + 0x8#32)).toNat := by
    rw [v23]; have := (R0 (c.get 10 + 0x8#32)).isLt; simp; omega
  refine ⟨rfl, Quiet.of_sameCsr ((nentry_sameCsr _ _).trans (nsaves_sameCsr c R0)) E.quiet,
    (nentry_sameCsr _ _).trans (nsaves_sameCsr c R0), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [dg 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]; exact nsaves_get2 c R0
  · simp [d, nentryCore, Core.wr_get_ne, Core.wr_get_self, g12, alu_add]
  · simp [d, nentryCore, Core.wr_get_ne, Core.wr_get_self, g10, alu_add]
  · simp [d, nentryCore, Core.wr_get_ne, Core.wr_get_self, alu_add]; exact nsaves_get c R0 11 (by decide)
  · rw [h23]; exact hd
  · rw [v23]; simp [d, nentryCore, Core.wr_get_self, alu_add, g10, lbu_val, ← rd8]
  · rw [v8]; simp [d, nentryCore, Core.wr_get_ne, Core.wr_get_self, alu_sub, g10, rf]
  · simp [d, nentryCore, Core.wr_get_ne, Core.wr_get_self, alu_add]
  · simp [d, nentryCore, Core.wr_get_ne, Core.wr_get_self, alu_add]
  · intro r hr
    simp only [nkept, List.mem_cons, List.not_mem_nil, or_false] at hr
    have hr' : r ≠ 2 ∧ r ≠ 8 ∧ r ≠ 9 ∧ r ≠ 10 ∧ r ≠ 18 ∧ r ≠ 19 ∧ r ≠ 20 ∧ r ≠ 23 ∧ r ≠ 24 ∧ r ≠ 25 ∧
        r ≠ 26 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro e <;> subst e <;> exact absurd hr (by decide)
    obtain ⟨a, b, c', d', e', f', g', h', i', j', k'⟩ := hr'
    rw [dg r b c' d' e' f' g' h' i' j' k']; exact nsaves_get c R0 r a
  · rw [v8, v9]; exact hI.1
  · rw [v8]; exact hI.2
  · exact nsaves_slots c R0 hs
  · rw [v9]; exact rc
  · rw [v8]; exact rf
  · rw [h23, ← rd8]; rfl
  · intro x hx
    have h3 : ¬ ((c.get 2).toNat - nextStack ≤ x.toNat ∧ x.toNat < (c.get 2).toNat) := hx.2.2
    rw [show nextStack = 0x70 from rfl] at h3
    exact nsaves_other c R0 hs x (by omega)

end E5R.Rmk.Deframer.Next
