import E5R.Image

/-
Lemmas for specifications about the trace: what a function wrote, and the
words a syscall leaves in a0.
-/
namespace E5R

/-- The bytes of `es` if every event in it is a `write` to `fd`, in order. -/
def writtenTo (fd : Word) : List Event → Option (List Byte)
  | [] => some []
  | .write f bs :: es => if f = fd then (writtenTo fd es).map (bs ++ ·) else none
  | _ :: _ => none

@[simp] theorem writtenTo_nil (fd : Word) : writtenTo fd [] = some [] := rfl

theorem writtenTo_append_write (fd : Word) (es : List Event) (bs : List Byte) :
    writtenTo fd (es ++ [.write fd bs]) = (writtenTo fd es).map (· ++ bs) := by
  induction es with
  | nil => simp [writtenTo]
  | cons e es ih =>
    cases e with
    | write f cs =>
      by_cases h : f = fd
      · simp only [List.cons_append, writtenTo, h, ite_true, ih, Option.map_map]
        cases writtenTo fd es <;> simp
      · simp [writtenTo, h]
    | read => simp [writtenTo]
    | exit => simp [writtenTo]

/-- Reading `k + r` bytes is reading `k`, then `r` more. -/
theorem readBytes_add (m : Word → Byte) (a : Word) (k r : Nat) :
    readBytes m a (k + r) = readBytes m a k ++ readBytes m (a + BitVec.ofNat 64 k) r := by
  induction k generalizing a with
  | zero => simp [readBytes]
  | succ k ih =>
    have e : a + 1 + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (k + 1) := by
      apply BitVec.eq_of_toNat_eq; simp; omega
    rw [Nat.add_right_comm, readBytes, ih, readBytes, List.cons_append, e]

/-- A write's result, at most `maxRW`, is not negative. -/
theorem ofNat_not_slt_zero {r : Nat} (h : r ≤ maxRW) : (BitVec.ofNat 64 r).slt 0 = false := by
  have : r < 2 ^ 63 := by unfold maxRW at h; omega
  simp only [BitVec.slt, decide_eq_false_iff_not, Int.not_lt]
  rw [BitVec.toInt_eq_toNat_of_lt (x := BitVec.ofNat 64 r)
    (by rw [toNat_ofNat_of_lt (by omega)]; omega)]
  simp; omega

/-- An error result `-e`, `1 ≤ e ≤ 4095`, is negative. -/
theorem neg_ofNat_slt_zero {e : Nat} (h1 : 1 ≤ e) (h2 : e ≤ 4095) :
    (-(BitVec.ofNat 64 e)).slt 0 = true := by
  simp only [BitVec.slt, decide_eq_true_eq]
  rw [BitVec.toInt_neg_of_ne_intMin (by
    intro h; have := congrArg BitVec.toNat h; simp at this; omega)]
  rw [BitVec.toInt_eq_toNat_of_lt (x := BitVec.ofNat 64 e)
    (by rw [toNat_ofNat_of_lt (by omega)]; omega)]
  simp; omega

end E5R
