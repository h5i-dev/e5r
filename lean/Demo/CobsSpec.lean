import E5R.Auto

/-
The specification of `cobs_decode` (demo/src/cobs.c), shared by the proof
about the e5r build (Demo/CobsB.lean) and the one about the ordinary build
(Demo/CobsA.lean). Nothing here depends on either binary.

COBS, as a function on lists: a frame is a sequence of blocks, each a code
byte `c ≥ 1` followed by `c - 1` data bytes; between two blocks a zero is
decoded, except after a block of code 255. `decodeFrame` returns whether the
frame was well formed and the bytes decoded (on an error: the bytes decoded
before the block whose code runs past the end).
-/
namespace Demo.Cobs
open E5R

/-- The index of the first zero byte, or the length. -/
def frameLen : List Byte → Nat
  | [] => 0
  | b :: bs => if b = 0 then 0 else frameLen bs + 1

/-- The zero decoded after a block of code `c` ending at `e`, in a frame of `n` bytes. -/
def zeroAfter (c e n : Nat) : List Byte := if c ≠ 255 ∧ e < n then [0] else []

def prepend (l : List Byte) (r : Bool × List Byte) : Bool × List Byte := (r.1, l ++ r.2)

/-- Decode a frame (no zero bytes). -/
def decodeFrame (xs : List Byte) : Bool × List Byte :=
  match xs with
  | [] => (true, [])
  | c :: rest =>
    if rest.length < c.toNat - 1 then (false, [])
    else prepend (rest.take (c.toNat - 1) ++ zeroAfter c.toNat (c.toNat - 1) rest.length)
      (decodeFrame (rest.drop (c.toNat - 1)))
termination_by xs.length

/-- What `cobs_decode(r, buf, len)` leaves in the three result words, and the
    buffer afterwards. `none`: the third word is not written. -/
def report (buf : List Byte) : (Nat × Nat × Option Nat) × List Byte :=
  if buf = [] then ((1, 0, none), buf) else
  let n := frameLen buf
  let d := decodeFrame (buf.take n)
  ((if d.1 then 0 else 1, if d.1 then n else 1, some d.2.length), d.2 ++ buf.drop d.2.length)

/-- The logical arguments: the result slot, the buffer and its contents. -/
structure Args where
  r : Word
  buf : Word
  orig : List Byte

/-- `void cobs_decode(struct cobs_report *r, u8 *buf, u64 len)`: decodes
    `buf` in place and writes the report to the 24 bytes at `r`. It may read
    and write the buffer and the slot (the slot is only written), nothing
    else, and uses no stack. -/
def spec : Spec Args where
  pre := fun ⟨r, buf, orig⟩ s =>
    s.reg Reg.a0 = r ∧ s.reg Reg.a1 = buf ∧ s.reg Reg.a2 = BitVec.ofNat 64 orig.length ∧
    orig.length < 2 ^ 63 ∧ readBytes s.mem buf orig.length = orig ∧ aligned r 8 ∧
    Region.Disjoint ⟨r, 24⟩ ⟨buf, orig.length⟩
  post := fun ⟨r, buf, orig⟩ s s' =>
    read64 s'.mem r = BitVec.ofNat 64 (report orig).1.1 ∧
    read64 s'.mem (r + 8) = BitVec.ofNat 64 (report orig).1.2.1 ∧
    (match (report orig).1.2.2 with
     | some b => read64 s'.mem (r + 16) = BitVec.ofNat 64 b
     | none => read64 s'.mem (r + 16) = read64 s.mem (r + 16)) ∧
    readBytes s'.mem buf orig.length = (report orig).2
  writes := fun ⟨r, buf, orig⟩ _ => [⟨buf, orig.length⟩, ⟨r, 24⟩]

/-! ## Facts the proofs use (about the specification, not the code) -/

theorem frameLen_le (l : List Byte) : frameLen l ≤ l.length := by
  induction l with
  | nil => simp [frameLen]
  | cons b bs ih => simp only [frameLen]; split <;> simp <;> omega

theorem getD_ne_zero_of_lt (l : List Byte) (j : Nat) (h : j < frameLen l) : l.getD j 0 ≠ 0 := by
  induction l generalizing j with
  | nil => simp [frameLen] at h
  | cons b bs ih =>
    simp only [frameLen] at h
    split at h
    · omega
    · cases j with
      | zero => simpa
      | succ j => simpa using ih j (by omega)

theorem frameLen_eq_of_zero (l : List Byte) (k : Nat) (hk : k < l.length) (hz : l.getD k 0 = 0)
    (hle : k ≤ frameLen l) : frameLen l = k := by
  induction l generalizing k with
  | nil => simp at hk
  | cons b bs ih =>
    cases k with
    | zero => simp_all [frameLen]
    | succ k =>
      simp only [frameLen] at hle ⊢
      split at hle
      · omega
      · rename_i hb; simp only [hb, ite_false]
        have := ih k (by simp at hk; omega) (by simpa using hz) (by omega); omega

theorem succ_le_frameLen (l : List Byte) (k : Nat) (hk : k < l.length) (hnz : l.getD k 0 ≠ 0)
    (hle : k ≤ frameLen l) : k + 1 ≤ frameLen l := by
  induction l generalizing k with
  | nil => simp at hk
  | cons b bs ih =>
    cases k with
    | zero => simp_all [frameLen]
    | succ k =>
      simp only [frameLen] at hle ⊢
      split at hle
      · omega
      · rename_i hb; simp only [hb, ite_false]
        have := ih k (by simp at hk; omega) (by simpa using hnz) (by omega); omega

/-- One block, read at index `src` of the frame. -/
theorem decodeFrame_drop (xs : List Byte) (src : Nat) (hs : src < xs.length)
    (hc : 1 ≤ (xs.getD src 0).toNat) :
    decodeFrame (xs.drop src) =
      if xs.length < src + (xs.getD src 0).toNat then (false, [])
      else prepend ((xs.drop (src + 1)).take ((xs.getD src 0).toNat - 1) ++
          zeroAfter (xs.getD src 0).toNat (src + (xs.getD src 0).toNat) xs.length)
        (decodeFrame (xs.drop (src + (xs.getD src 0).toNat))) := by
  rw [List.drop_eq_getElem_cons hs, decodeFrame]
  have hg : xs.getD src 0 = xs[src] := by simp [List.getD_eq_getElem?_getD, hs]
  rw [hg] at hc ⊢
  simp only [List.length_drop, List.drop_drop]
  by_cases h : xs.length < src + xs[src].toNat
  · rw [ite_eq_left (by omega), ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right h]
    have e2 : src + 1 + (xs[src].toNat - 1) = src + xs[src].toNat := by omega
    have e3 : (xs[src].toNat ≠ 255 ∧ xs[src].toNat - 1 < xs.length - (src + 1)) ↔
        (xs[src].toNat ≠ 255 ∧ src + xs[src].toNat < xs.length) := by omega
    simp only [zeroAfter, e2, e3]

theorem prepend_prepend (a b : List Byte) (r : Bool × List Byte) :
    prepend a (prepend b r) = prepend (a ++ b) r := by simp [prepend]

theorem getD_of_drop_eq {L M : List Byte} {d i : Nat} (h : L.drop d = M.drop d) (hi : d ≤ i) :
    L.getD i 0 = M.getD i 0 := by
  have := congrArg (fun l => l.getD (i - d) 0) h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop] at this ⊢
  rwa [Nat.add_sub_cancel' hi] at this

theorem getD_take (l : List Byte) (n i : Nat) (h : i < n) : (l.take n).getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, h]

/-! ### Lists at the write index -/

theorem drop_set_succ (L : List Byte) (d : Nat) (x : Byte) :
    (L.set d x).drop (d + 1) = L.drop (d + 1) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2; simp [List.getElem_set]; omega

theorem drop_succ_of_drop {L M : List Byte} {d : Nat} (h : L.drop d = M.drop d) :
    L.drop (d + 1) = M.drop (d + 1) := by
  have := congrArg (List.drop 1) h; simpa [List.drop_drop, Nat.add_comm] using this

theorem take_set_le (L : List Byte) (d k : Nat) (x : Byte) (h : k ≤ d) :
    (L.set d x).take k = L.take k := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2; simp only [List.length_take, List.length_set] at h1
    rw [List.getElem_take, List.getElem_take, List.getElem_set]; simp; omega

theorem take_set_succ (L : List Byte) (d : Nat) (x : Byte) (h : d < L.length) :
    (L.set d x).take (d + 1) = L.take d ++ [x] := by
  rw [List.take_add_one, take_set_le L d d x (Nat.le_refl _), List.getElem?_set_self h]; rfl

theorem take_drop_succ (l : List Byte) (p cnt : Nat) (hp : p < l.length) (hc : 0 < cnt) :
    (l.drop p).take cnt = l.getD p 0 :: (l.drop (p + 1)).take (cnt - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, cnt = k + 1 := ⟨cnt - 1, by omega⟩
  rw [List.drop_eq_getElem_cons hp, List.take_succ_cons]
  simp [List.getD_eq_getElem?_getD, hp]

theorem take_append_drop_of {L M : List Byte} {d : Nat} (h : L.drop d = M.drop d) :
    L.take d ++ M.drop d = L := by rw [← h, List.take_append_drop]

/-! ### The decode loop, one block at a time -/

/-- The code byte: the buffer's at `src` (not yet overwritten) is the frame's,
    and not zero. -/
theorem code_eq {orig L : List Byte} {src dst : Nat} (hsrc : src < frameLen orig)
    (hds : dst ≤ src) (hL : L.drop dst = orig.drop dst) :
    L.getD src 0 = (orig.take (frameLen orig)).getD src 0 := by
  rw [getD_of_drop_eq hL hds, getD_take _ _ _ hsrc]

theorem code_pos {orig L : List Byte} {src dst : Nat} (hsrc : src < frameLen orig)
    (hds : dst ≤ src) (hL : L.drop dst = orig.drop dst) : 1 ≤ (L.getD src 0).toNat := by
  rw [getD_of_drop_eq hL hds]
  have := getD_ne_zero_of_lt orig src hsrc
  have : (orig.getD src 0).toNat ≠ 0 := fun h => this (BitVec.eq_of_toNat_eq (by simpa using h))
  omega

/-- The invariant of the decode loop at `src`, unfolded by one block. -/
theorem inv_block {orig L : List Byte} {src dst : Nat}
    (hsrc : src < frameLen orig) (hds : dst ≤ src) (hL : L.drop dst = orig.drop dst)
    (hdec : decodeFrame (orig.take (frameLen orig)) =
      prepend (L.take dst) (decodeFrame ((orig.take (frameLen orig)).drop src))) :
    decodeFrame (orig.take (frameLen orig)) =
      if frameLen orig < src + (L.getD src 0).toNat then prepend (L.take dst) (false, [])
      else prepend (L.take dst ++ (orig.drop (src + 1)).take ((L.getD src 0).toNat - 1) ++
          zeroAfter (L.getD src 0).toNat (src + (L.getD src 0).toNat) (frameLen orig))
        (decodeFrame ((orig.take (frameLen orig)).drop (src + (L.getD src 0).toNat))) := by
  have hn : (orig.take (frameLen orig)).length = frameLen orig := by
    simp [frameLen_le]
  have hc := code_pos hsrc hds hL
  rw [code_eq hsrc hds hL] at hc ⊢
  rw [hdec, decodeFrame_drop _ src (by omega) hc, hn]
  split
  · rfl
  · rename_i h
    have e : ((orig.take (frameLen orig)).drop (src + 1)).take
          (((orig.take (frameLen orig)).getD src 0).toNat - 1) =
        (orig.drop (src + 1)).take (((orig.take (frameLen orig)).getD src 0).toNat - 1) := by
      rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]
    rw [prepend_prepend, e, List.append_assoc]

/-- What the report is, given how the frame decodes. -/
theorem report_of {orig : List Byte} (hne : orig.length ≠ 0) {ok : Bool} {out : List Byte}
    (h : decodeFrame (orig.take (frameLen orig)) = (ok, out)) :
    report orig = ((if ok then 0 else 1, if ok then frameLen orig else 1, some out.length),
      out ++ orig.drop out.length) := by
  have : orig ≠ [] := fun e => hne (by simp [e])
  simp [report, this, h]

theorem report_empty {orig : List Byte} (h : orig.length = 0) : report orig = ((1, 0, none), orig) := by
  simp_all [report, List.length_eq_zero_iff]

end Demo.Cobs
