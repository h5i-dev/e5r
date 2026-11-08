/-
  Generic packed-file slice lemmas, reused from Projects/rmk/Fetch.lean.
  Original e5r code, Apache-2.0. No RMK image or program is imported.
  These are equations about the existing RamElf reader, not new semantics.
-/
import Theories.RamElf
set_option maxRecDepth 100000
namespace E5R.Thermostat.PackedSlice
open E5R E5R.RamElf

/-- Byte `j` of packed words, read the way `File.slice` reads it. -/
def rawByte (ws : List Nat) (j : Nat) : Nat := ws.getD (j / 64) 0 / 256 ^ (j % 64) % 256

/-! ## `File.slice` -/

theorem unpackN_length : ∀ n x, (unpackN n x).length = n
  | 0, _ => rfl
  | n+1, x => by simp [unpackN, unpackN_length n]

theorem unpackN_get : ∀ n x k, k < n → (unpackN n x)[k]? = some (x / 256 ^ k % 256)
  | 0, _, k, h => absurd h (Nat.not_lt_zero _)
  | n+1, x, 0, _ => by simp [unpackN]
  | n+1, x, k+1, h => by
    simp only [unpackN, List.getElem?_cons_succ]
    rw [unpackN_get n (x / 256) k (by omega), Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

theorem go_length : ∀ (ws : List Nat) (k n : Nat), k ≤ 64 → (File.slice.go ws k n).length = n
  | _, _, 0, _ => by simp [File.slice.go]
  | [], _, n+1, _ => by simp [File.slice.go]
  | w :: ws, k, n+1, hk => by
    simp only [File.slice.go]
    have hl : ((unpackN 64 w).drop k).length = 64 - k := by simp [unpackN_length]
    split
    · rename_i h; rw [List.length_take]; omega
    · rename_i h; rw [List.length_append, go_length ws 0 _ (by omega)]; omega

theorem go_get : ∀ (ws : List Nat) (k n i : Nat), k < 64 → i < n →
    (File.slice.go ws k n)[i]? = some (rawByte ws (k + i))
  | _, _, 0, i, _, hi => absurd hi (Nat.not_lt_zero _)
  | [], k, n+1, i, _, hi => by
    simp only [File.slice.go, List.getElem?_replicate, rawByte, List.getD_nil, Nat.zero_div, Nat.zero_mod]
    simp [hi]
  | w :: ws, k, n+1, i, hk, hi => by
    simp only [File.slice.go]
    have hl : ((unpackN 64 w).drop k).length = 64 - k := by simp [unpackN_length]
    have here : ∀ i, i < 64 - k → ((unpackN 64 w).drop k)[i]? = some (rawByte (w :: ws) (k + i)) := by
      intro i hi'
      rw [List.getElem?_drop, unpackN_get 64 w (k + i) (by omega)]
      simp only [rawByte]
      rw [show (k + i) / 64 = 0 by omega, show (k + i) % 64 = k + i by omega]; rfl
    split
    · rename_i h
      rw [List.getElem?_take_of_lt hi]; exact here i (by omega)
    · rename_i h
      by_cases hi' : i < 64 - k
      · rw [List.getElem?_append_left (by omega)]; exact here i hi'
      · rw [List.getElem?_append_right (by omega), hl, go_get ws 0 _ _ (by omega) (by omega)]
        simp only [rawByte]
        rw [show (k + i) / 64 = (0 + (i - (64 - k))) / 64 + 1 by omega,
          show (k + i) % 64 = (0 + (i - (64 - k))) % 64 by omega]
        rfl

theorem slice_length (f : File) (off n : Nat) : (f.slice off n).length = n :=
  go_length _ _ _ (by omega)

theorem slice_get (f : File) (off n i : Nat) (hi : i < n) :
    (f.slice off n)[i]? = some (rawByte f.words (off + i)) := by
  unfold File.slice
  rw [go_get _ _ _ _ (by omega) hi]
  simp only [rawByte, List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [show off / 64 + (off % 64 + i) / 64 = (off + i) / 64 by omega,
    show (off % 64 + i) % 64 = (off + i) % 64 by omega]

end E5R.Thermostat.PackedSlice
