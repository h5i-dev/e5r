/-
Spec vocabulary: folds over lists.

A loop that accumulates over an array (a sum, a checksum, a count) has the
invariant "the accumulator is the fold of the first k elements". The
compiler may count k up, or count the remaining `m = n - k` down (clang's
rotated loops do); both forms are here, with the boundary cases.
-/
namespace NoCompiler.Vocab
variable {α β : Type}

/-- One more element, counted up. -/
theorem foldl_take_succ (f : β → α → β) (z : β) (xs : List α) (k : Nat) (h : k < xs.length) :
    (xs.take (k + 1)).foldl f z = f ((xs.take k).foldl f z) xs[k] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  simp only [Option.toList, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- One more element, with `m` elements left before and `m - 1` after. -/
theorem foldl_take_sub_pred (f : β → α → β) (z : β) (xs : List α) (m : Nat) (h : 0 < m)
    (h' : m ≤ xs.length) :
    (xs.take (xs.length - (m - 1))).foldl f z =
      f ((xs.take (xs.length - m)).foldl f z) xs[xs.length - m] := by
  rw [show xs.length - (m - 1) = xs.length - m + 1 by omega]
  exact foldl_take_succ f z xs _ (by omega)

/-- The last element, counted down (`m = 1` left). -/
theorem foldl_eq_last (f : β → α → β) (z : β) (xs : List α) (m : Nat) (h : m = 1)
    (h' : m ≤ xs.length) :
    xs.foldl f z = f ((xs.take (xs.length - m)).foldl f z) xs[xs.length - m] := by
  subst h
  have := foldl_take_sub_pred f z xs 1 (by omega) h'
  rwa [Nat.sub_self, Nat.sub_zero, List.take_length] at this

/-- The last element, counted up (`k + 1 = n`). -/
theorem foldl_eq_take_succ (f : β → α → β) (z : β) (xs : List α) (k : Nat) (h : k + 1 = xs.length) :
    xs.foldl f z = f ((xs.take k).foldl f z) xs[k] := by
  rw [← foldl_take_succ f z xs k (by omega), h, List.take_length]

theorem foldl_of_length_zero (f : β → α → β) (z : β) (xs : List α) (h : xs.length = 0) :
    xs.foldl f z = z := by
  simp_all [List.length_eq_zero_iff]

end NoCompiler.Vocab
