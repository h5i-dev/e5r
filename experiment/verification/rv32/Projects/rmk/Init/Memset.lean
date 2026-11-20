/-
  compiler_builtins `memset` (0x80020bb2) on the pinned RMK image, word-store path: PROVED.

  Original e5r code, Apache-2.0.

  PROVED here: `memset_words`: from `MemsetEnv` (destination a0 word-aligned, length a2 ≥ 16 and a
  multiple of 4, [a0, a0+a2) RAM, even return address), every behaviour returns to ra, quiet, with sp
  and every callee-saved register kept (memset writes only a2..a6) and RAM changed only in
  [a0, a0+a2). This covers the session task's initialization call `memset(bufA, 0, 0x1e8)` at
  0x80003e02. Unaligned or short calls (the byte head/tail loops) are not covered.
-/
import Projects.rmk.Init.MemsetSegs
import Projects.rmk.MemmoveAligned
import Projects.rmk.DevRead

set_option maxRecDepth 100000

namespace E5R.Rmk.Init
open E5R E5R.Rmk E5R.Rmk.Deframer E5R.Rmk.Deframer.Tail

structure MemsetEnv (m : Machine) : Prop where
  pc : m.core.pc = 0x80020bb2
  quiet : Quiet m.core
  ra : (m.core.get 1).getLsbD 0 = false
  dstAl : (m.core.get 10).toNat % 4 = 0
  len : 16 ≤ (m.core.get 12).toNat ∧ (m.core.get 12).toNat % 4 = 0
  dst : 0x80029bc8 ≤ (m.core.get 10).toNat ∧ (m.core.get 10).toNat + (m.core.get 12).toNat ≤ 0x81000000

structure MemsetPost (m₀ m : Machine) : Prop where
  pc : m.core.pc = m₀.core.get 1
  quiet : Quiet m.core
  saved : ∀ r : Reg, r.val ∉ callerSaved → m.core.get r = m₀.core.get r
  ram : ∀ x, ¬ ((m₀.core.get 10).toNat ≤ x.toNat ∧ x.toNat < (m₀.core.get 10).toNat + (m₀.core.get 12).toNat) →
    m.ram x = m₀.ram x

/-- At the word loop 0x80020bf4 with `i` words stored. -/
structure WAtL (c : Core) (M0 : Word → BitVec 8) (i : Nat) (m : Machine) : Prop where
  pc : m.core.pc = 0x80020bf4
  quiet : Quiet m.core
  regs : ∀ r : Reg, r.val ∉ [12, 13, 14, 15, 16] → m.core.get r = c.get r
  a4 : (m.core.get 14).toNat = (c.get 10).toNat + 4 * i
  a3 : (m.core.get 13).toNat = (c.get 10).toNat + (c.get 12).toNat
  a2 : m.core.get 12 = c.get 12
  lt : 4 * i < (c.get 12).toNat
  ram : ∀ x, ¬ ((c.get 10).toNat ≤ x.toNat ∧ x.toNat < (c.get 10).toNat + (c.get 12).toNat) → m.ram x = M0 x

theorem ne_of_mem {r : Reg} {l : List Nat} (h : r.val ∉ l) (k : Reg) (hk : k.val ∈ l) : r ≠ k :=
  fun e => h (e ▸ hk)

theorem sub_cs (n : Nat) (h : n ∈ [12, 13, 14, 15, 16]) : n ∈ callerSaved := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

/-- **The word loop**: from i stored words, the rest, then the return. -/
theorem words (c : Core) (M0 : Word → BitVec 8) (E : MemsetEnv ⟨c, M0⟩) :
    ∀ k i m, (c.get 12).toNat = 4 * (i + k + 1) → WAtL c M0 i m → Lands B img (MemsetPost ⟨c, M0⟩) m := by
  have hd : 0x80029bc8 ≤ (c.get 10).toNat ∧ (c.get 10).toNat + (c.get 12).toNat ≤ 0x81000000 := E.dst
  have hal : (c.get 10).toNat % 4 = 0 := E.dstAl
  intro k
  induction k with
  | zero =>
    intro i ⟨e, M⟩ hk L
    have a4 : (e.get 14).toNat = (c.get 10).toNat + 4 * i := L.a4
    have r1 := mWord e M L.pc L.quiet (by rw [a4]; omega) (by rw [B_ram, a4]; omega)
    have g14 : ((mWordCore e M).get 14).toNat = (c.get 10).toNat + 4 * (i + 1) := by
      simp [mWordCore, Core.wr_get_self, alu_add]; rw [a4]; omega
    have g13 : (mWordCore e M).get 13 = e.get 13 := by simp [mWordCore, Core.wr_get_ne]
    have r2 := mExit (mWordCore e M) (mWordRam e M) rfl (Quiet.of_sameCsr (mWordCsr e M) L.quiet)
      (by simp only [taken, BitVec.ult, Bool.not_eq_false', decide_eq_false_iff_not]
          rw [g13, show ((e.get 13)).toNat = _ from L.a3, g14]; omega)
      (by simp only [taken, BitVec.ult, decide_eq_false_iff_not]
          simp only [mWordCore, Core.goto_get, Core.wr_get_ne _ _ _ _ _ (show (12 : Reg) ≠ 14 by decide),
            Core.wr_get_ne _ _ _ _ _ (show (13 : Reg) ≠ 14 by decide), alu_add, Memmove.alu_and]
          rw [show (e.get 12) = c.get 12 from L.a2, BitVec.toNat_add, Memmove.and3, L.a3]; omega)
      (by simp only [mWordCore, Core.goto_get, Core.wr_get_ne _ _ _ _ _ (show (1 : Reg) ≠ 14 by decide)]
          rw [L.regs 1 (by decide)]; exact E.ra)
    refine lands_of_qrun (r1.trans r2) ⟨?_, Quiet.of_sameCsr ((mExitCsr (mWordCore e M) (mWordRam e M)).trans (mWordCsr e M)) L.quiet, ?_, ?_⟩
    · show (mExitCore (mWordCore e M) (mWordRam e M)).pc = c.get 1
      simp only [mExitCore, Core.goto_pc, mWordCore, Core.goto_get, Core.wr_get_ne _ _ _ _ _ (show (1 : Reg) ≠ 14 by decide)]
      exact L.regs 1 (by decide)
    · intro r hr
      show (mExitCore (mWordCore e M) (mWordRam e M)).get r = c.get r
      have h12 := ne_of_mem hr 12 (by decide)
      have h14 := ne_of_mem hr 14 (by decide)
      simp only [mExitCore, mWordCore, Core.goto_get, Core.wr_get_ne _ _ _ _ _ h12, Core.wr_get_ne _ _ _ _ _ h14]
      exact L.regs r fun hm => hr (sub_cs _ hm)
    · intro x hx
      have hx : ¬ ((c.get 10).toNat ≤ x.toNat ∧ x.toNat < (c.get 10).toNat + (c.get 12).toNat) := hx
      show ramWrite M (e.get 14) (e.get 15) .w x = M0 x
      rw [wr_byte_other _ _ _ _ (by rw [a4]; omega) (by rw [a4]; omega)]
      exact L.ram x hx
  | succ j ih =>
    intro i ⟨e, M⟩ hk L
    have a4 : (e.get 14).toNat = (c.get 10).toNat + 4 * i := L.a4
    have r1 := mWord e M L.pc L.quiet (by rw [a4]; omega) (by rw [B_ram, a4]; omega)
    have g14 : ((mWordCore e M).get 14).toNat = (c.get 10).toNat + 4 * (i + 1) := by
      simp [mWordCore, Core.wr_get_self, alu_add]; rw [a4]; omega
    have g13 : (mWordCore e M).get 13 = e.get 13 := by simp [mWordCore, Core.wr_get_ne]
    have r2 := mBack (mWordCore e M) (mWordRam e M) rfl (Quiet.of_sameCsr (mWordCsr e M) L.quiet)
      (by simp only [taken, BitVec.ult, decide_eq_true_eq]
          rw [g13, show ((e.get 13)).toNat = _ from L.a3, g14]; omega)
    refine lands_of_qrun_lands (r1.trans r2) (ih (i + 1) _ (by omega) ⟨rfl,
      Quiet.of_sameCsr ((mBackCsr (mWordCore e M) (mWordRam e M)).trans (mWordCsr e M)) L.quiet, ?_, ?_, ?_, ?_, by omega, ?_⟩)
    · intro r hr
      show (mBackCore (mWordCore e M) (mWordRam e M)).get r = c.get r
      have h14 := ne_of_mem hr 14 (by decide)
      simp only [mBackCore, mWordCore, Core.goto_get, Core.wr_get_ne _ _ _ _ _ h14]
      exact L.regs r hr
    · show ((mBackCore (mWordCore e M) (mWordRam e M)).get 14).toNat = _
      simp only [mBackCore, Core.goto_get]; exact g14
    · show ((mBackCore (mWordCore e M) (mWordRam e M)).get 13).toNat = _
      simp only [mBackCore, Core.goto_get, g13]; exact L.a3
    · show (mBackCore (mWordCore e M) (mWordRam e M)).get 12 = _
      simp only [mBackCore, mWordCore, Core.goto_get, Core.wr_get_ne _ _ _ _ _ (show (12 : Reg) ≠ 14 by decide)]
      exact L.a2
    · intro x hx
      show ramWrite M (e.get 14) (e.get 15) .w x = M0 x
      rw [wr_byte_other _ _ _ _ (by rw [a4]; omega) (by rw [a4]; omega)]
      exact L.ram x hx

/-- **`memset`, word path.** -/
theorem memset_words (m₀ : Machine) (E : MemsetEnv m₀) : Lands B img (MemsetPost m₀) m₀ := by
  obtain ⟨c, M0⟩ := m₀
  have hd : 0x80029bc8 ≤ (c.get 10).toNat ∧ (c.get 10).toNat + (c.get 12).toNat ≤ 0x81000000 := E.dst
  have hal : (c.get 10).toNat % 4 = 0 := E.dstAl
  have hl : 16 ≤ (c.get 12).toNat ∧ (c.get 12).toNat % 4 = 0 := E.len
  have hh : ((0 : Word) - c.get 10 &&& 3#32) = 0 := by
    apply BitVec.eq_of_toNat_eq; rw [Memmove.and3]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    show (2 ^ 32 - (c.get 10).toNat + 0) % 2 ^ 32 % 4 = 0
    have := (c.get 10).isLt; omega
  have hhn : -(c.get 10) &&& 3#32 = 0 := by simpa using hh
  have z1 : c.get 12 - (0 : Word) = c.get 12 := by simp
  have z2 : c.get 10 + (0 : Word) = c.get 10 := by simp
  have r := mPre c M0 E.pc E.quiet
    (by rw [show (alu .add 0 0x00000010#32 : Word) = 0x00000010#32 from by decide]
        simp only [taken, BitVec.ult, decide_eq_false_iff_not]; show ¬ (c.get 12).toNat < 16; omega)
    (by simp only [taken, BitVec.ult, Bool.not_eq_true', decide_eq_false_iff_not, alu_add, Memmove.alu_and, alu_sub, hh]
        simp)
    (by simp only [taken, BitVec.ult, Bool.not_eq_true', decide_eq_false_iff_not, Bool.not_eq_false', decide_eq_true_eq,
          alu_add, Memmove.alu_and, alu_sub, hh]
        rw [z1, z2, BitVec.toNat_add, Memmove.andm4]; omega)
  refine lands_of_qrun_lands r (words c M0 E ((c.get 12).toNat / 4 - 1) 0 _ (by omega) ⟨rfl,
    Quiet.of_sameCsr (mPreCsr c M0) E.quiet, ?_, ?_, ?_, ?_, by omega, fun x _ => rfl⟩)
  · intro r hr
    have n12 := ne_of_mem hr 12 (by decide)
    have n13 := ne_of_mem hr 13 (by decide)
    have n14 := ne_of_mem hr 14 (by decide)
    have n15 := ne_of_mem hr 15 (by decide)
    have n16 := ne_of_mem hr 16 (by decide)
    simp [mPreCore, Core.wr_get_ne, n12, n13, n14, n15, n16]
  · show ((mPreCore c M0).get 14).toNat = _
    simp only [mPreCore, Core.goto_get, Core.wr_get_ne _ _ _ _ _ (show (14 : Reg) ≠ 12 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (14 : Reg) ≠ 13 by decide), Core.wr_get_ne _ _ _ _ _ (show (14 : Reg) ≠ 15 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (14 : Reg) ≠ 16 by decide), Core.wr_get_self _ _ _ _ (show (14 : Reg).val ≠ 0 by decide),
      alu_add, Memmove.alu_and, alu_sub, hh, z2]
    omega
  · show ((mPreCore c M0).get 13).toNat = _
    simp only [mPreCore, Core.goto_get, Core.wr_get_ne _ _ _ _ _ (show (13 : Reg) ≠ 12 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (13 : Reg) ≠ 14 by decide), Core.wr_get_ne _ _ _ _ _ (show (13 : Reg) ≠ 15 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (13 : Reg) ≠ 16 by decide), Core.wr_get_self _ _ _ _ (show (13 : Reg).val ≠ 0 by decide),
      alu_add, Memmove.alu_and, alu_sub, hh, z1, z2]
    rw [BitVec.toNat_add, Memmove.andm4]; omega
  · show (mPreCore c M0).get 12 = _
    simp only [mPreCore, Core.goto_get, Core.wr_get_ne _ _ _ _ _ (show (12 : Reg) ≠ 13 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (12 : Reg) ≠ 14 by decide), Core.wr_get_ne _ _ _ _ _ (show (12 : Reg) ≠ 15 by decide),
      Core.wr_get_ne _ _ _ _ _ (show (12 : Reg) ≠ 16 by decide), Core.wr_get_self _ _ _ _ (show (12 : Reg).val ≠ 0 by decide),
      alu_sub, Memmove.alu_and, hh, z1]

end E5R.Rmk.Init
