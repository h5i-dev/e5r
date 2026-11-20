/-
  The ring-index wrap rustc emits for `if i + 1 == 4 { 0 } else { i + 1 }`:
  `a = i + 1; t = seqz(a - 4) - 1; i' = t & a` (branch-free). Word-level
  facts the machine-code summaries use. Original e5r code, Apache-2.0.
-/
import Theories.Hart

namespace E5R.Hybrid
open E5R

/-- The ring index after one step: `i + 1`, wrapped at the capacity 4. -/
def next (h : Word) : Word := if h = 3 then 0 else h + 1

theorem next_lt {h : Word} (hh : h.toNat < 4) : (next h).toNat < 4 := by
  unfold next; split
  · simp
  · rename_i hn
    have : h.toNat ≠ 3 := fun e => hn (BitVec.eq_of_toNat_eq (by simp [e]))
    rw [BitVec.toNat_add]; simp; omega

theorem cases4 {h : Word} (hh : h.toNat < 4) : h = 0 ∨ h = 1 ∨ h = 2 ∨ h = 3 := by
  have e : h = BitVec.ofNat 32 h.toNat := by simp
  rcases (by omega : h.toNat = 0 ∨ h.toNat = 1 ∨ h.toNat = 2 ∨ h.toNat = 3) with k | k | k | k <;>
    rw [k] at e <;> simp [e]

/-- The emitted wrap computes `next` (mask on the left, as in the firmware). -/
theorem wrap {h : Word} (hh : h.toNat < 4) :
    alu .and (alu .add (alu .sltu (h + 1 + 0xfffffffc) 1) 0xffffffff) (h + 1) = next h := by
  rcases cases4 hh with rfl | rfl | rfl | rfl <;> decide

/-- The same with the mask on the right. -/
theorem wrap' {h : Word} (hh : h.toNat < 4) :
    alu .and (h + 1) (alu .add (alu .sltu (h + 1 + 0xfffffffc) 1) 0xffffffff) = next h := by
  rcases cases4 hh with rfl | rfl | rfl | rfl <;> decide

end E5R.Hybrid
