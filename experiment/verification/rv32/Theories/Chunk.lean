/-
  Splitting an image into small segments changes no byte the model reads.
  Original e5r code, Apache-2.0.

  `romByte?` looks a byte up in the first segment containing it, and
  `romRead?`/`fetch` read byte by byte, so an image whose segments are cut
  into pieces of at most `k` bytes (same addresses, bytes and exec flags)
  answers every read the same way. Proofs and the replay may use the chunked
  image, whose lookups do not walk a 135 KB list.
-/
import Theories.Platform

namespace E5R

/-- Segment `⟨base, bytes, exec⟩` cut into pieces of at most `k` bytes. -/
def chunkSeg (k : Nat) (exec : Bool) (base : Nat) (bytes : List Nat) : List Segment :=
  if h : bytes = [] ∨ k = 0 then [] else
    ⟨base, bytes.take k, exec⟩ :: chunkSeg k exec (base + k) (bytes.drop k)
termination_by bytes.length
decreasing_by
  simp only [not_or] at h
  obtain ⟨hb, hk⟩ := h
  have : 0 < bytes.length := List.length_pos_iff.mpr hb
  simp only [List.length_drop]; omega

def chunkImg (k : Nat) (img : List Segment) : List Segment :=
  img.flatMap fun s => chunkSeg k s.exec s.base s.bytes

/-- The test `romByte?` uses to pick a segment. -/
def holds (a : Nat) (fetch : Bool) (s : Segment) : Bool :=
  s.base ≤ a && a < s.base + s.bytes.length && (!fetch || s.exec)

theorem byte_of_holds {a : Nat} {fetch : Bool} {s : Segment} (h : holds a fetch s = true) :
    (s.byte? a).isSome = true := by
  simp only [holds, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [Segment.byte?, if_pos h.1.1]
  rw [List.getElem?_eq_getElem (by omega)]; rfl

/-- What a piece list says about one address: the byte of the segment, if
    the segment holds the address. -/
def look (a : Nat) (fetch : Bool) (l : List Segment) : Option Nat :=
  (l.find? (holds a fetch)).bind (·.byte? a)

theorem look_append (a : Nat) (fetch : Bool) (l1 l2 : List Segment) :
    look a fetch (l1 ++ l2) = match l1.find? (holds a fetch) with
      | some s => s.byte? a
      | none => look a fetch l2 := by
  unfold look
  rw [List.find?_append]
  cases l1.find? (holds a fetch) <;> rfl

theorem chunkSeg_look (k : Nat) (hk : 0 < k) (exec : Bool) (a : Nat) (fetch : Bool)
    (bytes : List Nat) (base : Nat) :
    look a fetch (chunkSeg k exec base bytes) =
      if holds a fetch ⟨base, bytes, exec⟩ then Segment.byte? ⟨base, bytes, exec⟩ a else none := by
  rw [chunkSeg]
  by_cases hb : bytes = []
  · subst hb
    have h0 : holds a fetch ⟨base, [], exec⟩ = false := by
      simp only [holds, List.length_nil, Nat.add_zero, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      omega
    rw [if_neg (by simp [h0]), dif_pos (Or.inl rfl)]
    rfl
  · have hk' : k ≠ 0 := by omega
    simp only [hb, hk', or_self, ↓reduceDIte]
    have ih := chunkSeg_look k hk exec a fetch (bytes.drop k) (base + k)
    unfold look at ih ⊢
    rw [List.find?_cons]
    by_cases hin : a < base + k
    · by_cases hp : holds a fetch ⟨base, bytes, exec⟩ = true
      · have hp' : holds a fetch ⟨base, bytes.take k, exec⟩ = true := by
          simp only [holds, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.length_take] at hp ⊢
          exact ⟨⟨hp.1.1, by omega⟩, hp.2⟩
        rw [hp', if_pos hp]
        simp only [Option.bind_some, Segment.byte?]
        simp only [holds, Bool.and_eq_true, decide_eq_true_eq] at hp
        rw [if_pos hp.1.1, if_pos hp.1.1, List.getElem?_take, if_pos (by omega)]
      · have hp' : holds a fetch ⟨base, bytes.take k, exec⟩ = false := by
          cases hq : holds a fetch ⟨base, bytes.take k, exec⟩
          · rfl
          · exfalso; apply hp
            simp only [holds, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.length_take] at hq ⊢
            exact ⟨⟨hq.1.1, by omega⟩, hq.2⟩
        have hn : holds a fetch ⟨base + k, bytes.drop k, exec⟩ = false := by
          simp only [holds, Bool.and_eq_false_iff, decide_eq_false_iff_not]; left; left; omega
        rw [hp']
        simp only
        rw [ih, if_neg (by simp [hn]), if_neg hp]
    · have hp' : holds a fetch ⟨base, bytes.take k, exec⟩ = false := by
        simp only [holds, List.length_take, Bool.and_eq_false_iff, decide_eq_false_iff_not]
        left; right; omega
      rw [hp']
      simp only
      rw [ih]
      have e : holds a fetch ⟨base + k, bytes.drop k, exec⟩ = holds a fetch ⟨base, bytes, exec⟩ := by
        simp only [holds, List.length_drop]
        have h1 : decide (base + k ≤ a) = decide (base ≤ a) := by simp only [decide_eq_decide]; omega
        have h2 : decide (a < base + k + (bytes.length - k)) = decide (a < base + bytes.length) := by
          simp only [decide_eq_decide]; omega
        rw [h1, h2]
      rw [e]
      split
      · next hh =>
        simp only [Segment.byte?]
        simp only [holds, Bool.and_eq_true, decide_eq_true_eq] at hh
        rw [if_pos (by omega), if_pos hh.1.1, List.getElem?_drop]
        congr 1; omega
      · rfl
termination_by bytes.length
decreasing_by
  have : 0 < bytes.length := List.length_pos_iff.mpr hb
  simp only [List.length_drop]; omega

theorem look_chunkImg (k : Nat) (hk : 0 < k) (a : Nat) (fetch : Bool) :
    ∀ img : List Segment, look a fetch (chunkImg k img) = look a fetch img := by
  intro img
  induction img with
  | nil => rfl
  | cons s rest ih =>
    have hc : chunkImg k (s :: rest) = chunkSeg k s.exec s.base s.bytes ++ chunkImg k rest := by
      simp [chunkImg, List.flatMap_cons]
    rw [hc, look_append]
    have hs := chunkSeg_look k hk s.exec a fetch s.bytes s.base
    have hseg : (⟨s.base, s.bytes, s.exec⟩ : Segment) = s := rfl
    rw [hseg] at hs
    unfold look at hs ih ⊢
    rw [List.find?_cons]
    cases hp : holds a fetch s with
    | true =>
      rw [if_pos hp] at hs
      cases hf : (chunkSeg k s.exec s.base s.bytes).find? (holds a fetch) with
      | some c => rw [hf] at hs; simpa using hs
      | none =>
        exfalso
        rw [hf] at hs
        have := byte_of_holds hp
        rw [← hs] at this; simp at this
    | false =>
      rw [if_neg (by simp [hp])] at hs
      cases hf : (chunkSeg k s.exec s.base s.bytes).find? (holds a fetch) with
      | some c =>
        exfalso
        rw [hf] at hs
        have := byte_of_holds (List.find?_some hf)
        simp only [Option.bind_some] at hs
        rw [hs] at this; simp at this
      | none => simpa using ih

/-- **A chunked image answers every byte read like the original.** -/
theorem romByte?_chunk (k : Nat) (hk : 0 < k) (img : List Segment) (a : Nat) (fetch : Bool) :
    romByte? (chunkImg k img) a fetch = romByte? img a fetch := by
  have := look_chunkImg k hk a fetch img
  unfold look holds at this
  unfold romByte?
  cases h1 : (chunkImg k img).find? _ <;> cases h2 : img.find? _ <;> simp_all

theorem romRead?_chunk (k : Nat) (hk : 0 < k) (img : List Segment) (a n : Nat) (fetch : Bool) :
    romRead? (chunkImg k img) a n fetch = romRead? img a n fetch := by
  unfold romRead?
  congr 1
  induction n with
  | zero => rfl
  | succ n ih => simp only [romRead?.go, romByte?_chunk k hk, ih]

/-- **Fetching from a chunked image is fetching from the image.** -/
theorem fetch_chunk (k : Nat) (hk : 0 < k) (img : List Segment) (pc : Word) :
    fetch (chunkImg k img) pc = fetch img pc := by
  simp only [fetch, romRead?_chunk k hk]

theorem interp_chunk (k : Nat) (hk : 0 < k) (B : Board) (img : List Segment) (o : Oracle) :
    ∀ (e : Eff) (ram : Word → BitVec 8) (i : Nat) (evs : List Event),
      interp B (chunkImg k img) o e ram i evs = interp B img o e ram i evs := by
  intro e
  induction e with
  | done c => intros; rfl
  | trap _ => intros; rfl
  | unsupported _ => intros; rfl
  | choose kk ih => intro ram i evs; simp only [interp, ih]
  | pick kk ih => intro ram i evs; simp only [interp, ih]
  | load w a atomic kk ih => intro ram i evs; simp only [interp, romRead?_chunk k hk, ih]
  | store w a v atomic kk ih => intro ram i evs; simp only [interp, ih]

/-- **A step of the model on a chunked image is a step on the image.** -/
theorem stepInstr_chunk (k : Nat) (hk : 0 < k) (B : Board) (img : List Segment) (m : Machine)
    (o : Oracle) : stepInstr B (chunkImg k img) m o = stepInstr B img m o := by
  simp only [stepInstr, fetch_chunk k hk, interp_chunk k hk]

end E5R
