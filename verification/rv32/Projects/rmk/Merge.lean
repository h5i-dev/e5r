/-
  Word arithmetic of memmove's misaligned shift/merge copy.

  Original e5r code, Apache-2.0.

  The misaligned loop stores `(prev >>> 8o) ||| (next <<< (32 - 8o))` for
  a source misalignment `o ∈ {1,2,3}`. `merge_byte` says which byte of
  which word each stored byte is; `ramWrite_w_bytes` says a word store
  depends only on the four bytes stored. Together they show the merged
  store writes exactly the source bytes, as `sw (lw src)` would.
-/
import Projects.rmk.Copy

set_option maxRecDepth 100000

namespace E5R.Rmk
open E5R

theorem merge_toNat (p q : Word) (a : Nat) (ha : 0 < a) (ha' : a < 32) :
    ((p >>> a) ||| (q <<< (32 - a))).toNat = p.toNat / 2 ^ a + q.toNat * 2 ^ (32 - a) % 2 ^ 32 := by
  have hz : (p >>> a) &&& (q <<< (32 - a)) = 0#32 := by
    apply BitVec.eq_of_getElem_eq; intro i hi
    simp only [BitVec.getElem_and, BitVec.getElem_ushiftRight, BitVec.getElem_shiftLeft, BitVec.getElem_zero]
    by_cases h : i < 32 - a
    · simp [h]
    · simp [h]
      intro h2
      exact absurd h2 (by rw [BitVec.getLsbD_of_ge _ _ (by omega)]; simp)
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hz, BitVec.toNat_add_of_and_eq_zero hz,
    BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]

/-- Byte `k` of the merged word. -/
theorem merge_byte (p q : Word) (o k : Nat) (ho : 0 < o ∧ o < 4) (hk : k < 4) :
    byteOf ((p >>> (8 * o)) ||| (q <<< (32 - 8 * o))) k =
      if k + o < 4 then byteOf p (k + o) else byteOf q (k + o - 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [byteOf, BitVec.toNat_ofNat, merge_toNat _ _ _ (by omega) (by omega)]
  have hp := p.isLt; have hq := q.isLt
  rcases (by omega : o = 1 ∨ o = 2 ∨ o = 3) with rfl | rfl | rfl <;>
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    simp [byteOf] <;> omega

/-- A word store is determined by the four bytes it stores. -/
theorem ramWrite_w_bytes (R : Word → BitVec 8) (a v v' : Word)
    (h : ∀ k < 4, byteOf v k = byteOf v' k) : ramWrite R a v .w = ramWrite R a v' .w := by
  simp only [ramWrite, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)]

theorem byte_read_k (R : Word → BitVec 8) (s : Word) (k : Nat) (hk : k < 4) :
    byteOf (ramRead R s .w) k = R (s + BitVec.ofNat 32 k) := by
  obtain ⟨b0, b1, b2, b3⟩ := byte_read R s
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · simpa using b0
  · exact b1
  · exact b2
  · exact b3

/-- The merged store writes the source word at `A + o`: `prev` holds the
    bytes `A + o .. A + 3` at its positions `o .. 3`, `next` is the word
    at `A + 4`. -/
theorem merge_store (R R' : Word → BitVec 8) (D A prev : Word) (o : Nat) (ho : 0 < o ∧ o < 4)
    (hprev : ∀ k, o ≤ k → k < 4 → byteOf prev k = R (A + BitVec.ofNat 32 k)) :
    ramWrite R' D ((prev >>> (8 * o)) ||| (ramRead R (A + 4) .w <<< (32 - 8 * o))) .w =
      ramWrite R' D (ramRead R (A + BitVec.ofNat 32 o) .w) .w := by
  apply ramWrite_w_bytes
  intro k hk
  rw [merge_byte _ _ _ _ ho hk, byte_read_k _ _ _ hk]
  split
  · rw [hprev (k + o) (by omega) (by omega)]; congr 1; bv_omega
  · rw [byte_read_k _ _ _ (by omega)]; congr 1; bv_omega

end E5R.Rmk
