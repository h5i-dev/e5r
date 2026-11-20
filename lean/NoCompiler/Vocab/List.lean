/-
Spec vocabulary: lists as buffers.

`nocompiler_auto` leaves a buffer in memory as a list (`readBytes m a n`),
an element read from it as `L.getD i 0`, a store into it as `L.set i x`.
These are the facts a specification about such a buffer needs, stated for
any element type:

* a buffer updated in place from the front: the part not yet written is the
  original (`L.drop d = M.drop d`), the part written is `L.take d`;
* the first element satisfying a test (`List.findIdx`: a terminator, a
  separator), with `getD` forms of the core lemmas.

Nothing here mentions the machine.
-/
namespace NoCompiler.Vocab
variable {α : Type}

/-! ## Reading at an index -/

theorem getD_take (l : List α) (n i : Nat) {d : α} (h : i < n) :
    (l.take n).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, h]

/-- Two lists that agree from `d` on agree at every index from `d`. -/
theorem getD_of_drop_eq {L M : List α} {d i : Nat} {x : α} (h : L.drop d = M.drop d) (hi : d ≤ i) :
    L.getD i x = M.getD i x := by
  have := congrArg (fun l => l.getD (i - d) x) h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop] at this ⊢
  rwa [Nat.add_sub_cancel' hi] at this

/-- `cnt` elements from `p`: the one at `p`, then `cnt - 1` more. -/
theorem take_drop_succ (l : List α) (p cnt : Nat) {d : α} (hp : p < l.length) (hc : 0 < cnt) :
    (l.drop p).take cnt = l.getD p d :: (l.drop (p + 1)).take (cnt - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, cnt = k + 1 := ⟨cnt - 1, by omega⟩
  rw [List.drop_eq_getElem_cons hp, List.take_succ_cons]
  simp [List.getD_eq_getElem?_getD, hp]

/-! ## A buffer written in place from the front -/

theorem drop_set_succ (L : List α) (d : Nat) (x : α) :
    (L.set d x).drop (d + 1) = L.drop (d + 1) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2; simp [List.getElem_set]; omega

theorem drop_succ_of_drop {L M : List α} {d : Nat} (h : L.drop d = M.drop d) :
    L.drop (d + 1) = M.drop (d + 1) := by
  have := congrArg (List.drop 1) h; simpa [List.drop_drop, Nat.add_comm] using this

/-- Writing at `d` keeps the agreement from `d + 1` on. -/
theorem drop_set_of_drop {L M : List α} {d : Nat} (x : α) (h : L.drop d = M.drop d) :
    (L.set d x).drop (d + 1) = M.drop (d + 1) := by
  rw [drop_set_succ]; exact drop_succ_of_drop h

theorem take_set_le (L : List α) (d k : Nat) (x : α) (h : k ≤ d) :
    (L.set d x).take k = L.take k := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2; simp only [List.length_take, List.length_set] at h1
    rw [List.getElem_take, List.getElem_take, List.getElem_set]; simp; omega

/-- The written prefix grows by the element written. -/
theorem take_set_succ (L : List α) (d : Nat) (x : α) (h : d < L.length) :
    (L.set d x).take (d + 1) = L.take d ++ [x] := by
  rw [List.take_add_one, take_set_le L d d x (Nat.le_refl _), List.getElem?_set_self h]; rfl

/-- The written prefix of `L` followed by the untouched rest of `M` is `L`. -/
theorem take_append_drop_of {L M : List α} {d : Nat} (h : L.drop d = M.drop d) :
    L.take d ++ M.drop d = L := by rw [← h, List.take_append_drop]

theorem length_take_of_le {L : List α} {d : Nat} (h : d ≤ L.length) : (L.take d).length = d := by
  simp; omega

/-! ## The first element that passes a test -/

/-- Before the first hit, the test fails. -/
theorem getD_not_of_lt_findIdx {p : α → Bool} {l : List α} {j : Nat} (d : α)
    (h : j < l.findIdx p) : p (l.getD j d) = false := by
  have hj : j < l.length := Nat.lt_of_lt_of_le h List.findIdx_le_length
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  exact List.not_of_lt_findIdx h

/-- A hit at `k`, with no hit before `k`: the first hit is `k`. -/
theorem findIdx_eq_of_getD {p : α → Bool} {l : List α} {k : Nat} (d : α) (hk : k < l.length)
    (hz : p (l.getD k d) = true) (hle : k ≤ l.findIdx p) : l.findIdx p = k := by
  induction l generalizing k with
  | nil => simp at hk
  | cons b bs ih =>
    rw [List.findIdx_cons] at hle ⊢
    cases k with
    | zero => simp_all
    | succ k =>
      cases hb : p b <;> simp only [hb, Bool.false_eq_true, ite_false, ite_true] at hle ⊢
      · have := ih (k := k) (by simp at hk; omega) (by simpa using hz) (by omega); omega
      · omega

/-- No hit at `k`, with no hit before `k`: no hit up to `k + 1`. -/
theorem succ_le_findIdx_of_getD {p : α → Bool} {l : List α} {k : Nat} (d : α) (hk : k < l.length)
    (hnz : p (l.getD k d) = false) (hle : k ≤ l.findIdx p) : k + 1 ≤ l.findIdx p := by
  induction l generalizing k with
  | nil => simp at hk
  | cons b bs ih =>
    rw [List.findIdx_cons] at hle ⊢
    cases k with
    | zero => simp_all
    | succ k =>
      cases hb : p b <;> simp only [hb, Bool.false_eq_true, ite_false, ite_true] at hle ⊢
      · have := ih (k := k) (by simp at hk; omega) (by simpa using hnz) (by omega); omega
      · omega

end NoCompiler.Vocab
