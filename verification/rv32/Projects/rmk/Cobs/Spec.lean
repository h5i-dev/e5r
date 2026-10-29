/-
  The decode loop of `cobs::dec::decode_in_place_report` (pinned RMK image) as a
  pure function of the ORIGINAL buffer bytes: a transliteration of the emitted
  machine code (0x8001e064..0x8001e0ea), not of the COBS specification.

  Original e5r code, Apache-2.0.

  Machine loop, with src = t4, dst = t2, n = a4 (first zero), len = a2:
    0x8001e068  (src < n)  code := buf[src]
                if n < src + code                         -> invalid frame (0x8001e116)
                if code < 2:  src += 1                    -> tail (0x8001e0d8)
                else: copy buf[src+1 .. src+code) to buf[dst ..), src += code, dst += code-1;
                      code = 0xff -> 0x8001e064, else -> tail
    0x8001e0d8  tail: if src < n: buf[dst] := 0, dst += 1
    0x8001e064 / 0x8001e0ea: src < n -> 0x8001e068, else success (0x8001e0ee)
  `block` is one iteration; `run` the loop. Because writes trail reads (dst ≤ src),
  every byte the loop reads is an original byte at an index in [src, n), which is
  why the specification needs only `orig`.
-/

namespace E5R.Rmk.Cobs

/-- One iteration at source index `src`: the bytes appended to the output and the
    next source index, or `none` for an invalid frame (a code running past `n`). -/
def block (orig : Nat → Nat) (n src : Nat) : Option (List Nat × Nat) :=
  let code := orig src
  if n < src + code then none
  else if code < 2 then some ((if src + 1 < n then [0] else []), src + 1)
  else
    some ((List.range (code - 1)).map (fun i => orig (src + 1 + i)) ++
      (if code ≠ 0xff ∧ src + code < n then [0] else []), src + code)

inductive Outcome where
  | ok
  | invalid
  deriving DecidableEq, Repr

/-- The loop from source index `src` with output `acc` so far (fuel bounds the
    iterations; `n - src + 1` is always enough, `run_fuel`). -/
def run (orig : Nat → Nat) (n : Nat) : Nat → Nat → List Nat → Outcome × List Nat
  | 0, _, acc => (.ok, acc)
  | f + 1, src, acc =>
    if n ≤ src then (.ok, acc) else
    match block orig n src with
    | none => (.invalid, acc)
    | some (out, src') => run orig n f src' (acc ++ out)

/-! ## Facts about one block -/

theorem block_some {orig : Nat → Nat} {n src : Nat} {out : List Nat} {src' : Nat}
    (h : block orig n src = some (out, src')) (hs : src < n) :
    src < src' ∧ src' ≤ n ∧ out.length ≤ src' - src := by
  unfold block at h
  simp only at h
  split at h
  · cases h
  · rename_i hle
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by omega, by omega, ?_⟩
      split <;> simp
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by omega, by omega, ?_⟩
      simp only [List.length_append, List.length_map, List.length_range]
      split <;> simp <;> omega

/-! ## The loop reads only bytes below `n` -/

theorem block_congr (f g : Nat → Nat) (n src : Nat) (h : ∀ j, j < n → f j = g j) (hs : src < n) :
    block f n src = block g n src := by
  unfold block
  simp only [h src hs]
  split
  · rfl
  · split
    · rfl
    · rename_i h1 h2
      congr 3
      apply List.map_congr_left
      intro i hi
      simp only [List.mem_range] at hi
      exact h _ (by omega)

theorem run_congr (f g : Nat → Nat) (n : Nat) (h : ∀ j, j < n → f j = g j) :
    ∀ fuel src acc, run f n fuel src acc = run g n fuel src acc
  | 0, _, _ => rfl
  | fuel + 1, src, acc => by
    unfold run
    split
    · rfl
    · rename_i hs
      rw [block_congr f g n src h (by omega)]
      split
      · rfl
      · exact run_congr f g n h fuel _ _

end E5R.Rmk.Cobs
