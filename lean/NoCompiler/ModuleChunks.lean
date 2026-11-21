import NoCompiler.RefineReuse

/-! # Modules in chunks: reuse at the scale of a real binary

A relocatable module as `nocompiler module --format chunks` writes it, in
numbers: one `RChunk` per function, its relocatable words as one number
literal (the form of A's image chunks, `Chunk` in Image.lean), its
relocations packed in a second, its name and its relocations' symbols as
numbers too (`symOfCode`). The module is still the trusted `Module`
(`Module.ofChunks`); what changes is what the kernel compares when an
unchanged function's theorem is reused.

`RChunk.subSeq fs ks fs'` says `fs` is a sublist of `fs'`: skip `ks[0]`
functions of `fs'`, match `fs[0]`, skip `ks[1]`, match `fs[1]`, and so on.
Deciding it walks at most `fs'.length` list cells and compares, per function
of `fs`, two `RChunk`s: numbers and lists of numbers only, which the kernel
compares natively. It decodes no word, relocation or string. Distinct names,
which `Module.Ok` asks of the smaller module, follow from the sublist and the
larger module's `Ok`, so nothing compares strings. `Verified.of_chunks` and
`Refines.of_chunks` are `Verified.of_sub` and `Refines.of_sub_verified` with
that check for their side conditions.
-/

namespace NoCompiler

/-- The string whose characters are the 32-bit slots of `n` from the low end,
    up to the first zero slot. -/
def symOfCode (n : Nat) : Sym := String.ofList (go n n)
where
  go : Nat → Nat → List Char
    | 0, _ => []
    | fuel + 1, n => if n = 0 then [] else Char.ofNat (n % 2 ^ 32) :: go fuel (n >>> 32)

/-- A relocatable function in numbers: its name `symOfCode name`; word `i`
    the 32 bits of `bits` from bit `32 * i`; relocation `i` the 128 bits of
    `rbits` from bit `128 * i` (`RChunk.reloc`), its symbol by index into
    `syms`. -/
structure RChunk where
  name : Nat
  len : Nat
  bits : Nat
  nrel : Nat := 0
  rbits : Nat := 0
  syms : List Nat := []
  deriving DecidableEq

/-- A data section in parts, each `(n, bits)`: `n` bytes, byte `i` the 8 bits
    of `bits` from bit `8 * i`. Parts keep each literal short: elaborating
    one hexadecimal literal grows faster than its length. -/
structure DChunk where
  name : Nat
  parts : List (Nat × Nat)
  writable : Bool := false
  deriving DecidableEq

namespace RChunk

def words (c : RChunk) : List (BitVec 32) :=
  (List.range c.len).map fun i => BitVec.ofNat 32 (c.bits >>> (32 * i))

def kindOf : Nat → RelocKind
  | 0 => .call
  | 1 => .pcrelHi
  | 2 => .pcrelLoI
  | _ => .pcrelLoS

/-- Relocation `i`: bits 0-23 the offset, 24-47 the `auipc`'s offset, 48-49
    the kind, 50-69 the symbol's index, 70-127 the addend zigzag-coded
    (`2a` for `a ≥ 0`, `-2a - 1` below). -/
def reloc (c : RChunk) (i : Nat) : Reloc :=
  let v := c.rbits >>> (128 * i)
  let z := (v >>> 70) % 2 ^ 58
  { off := v % 2 ^ 24, kind := kindOf ((v >>> 48) % 4),
    sym := symOfCode (c.syms.getD ((v >>> 50) % 2 ^ 20) 0),
    addend := if z % 2 = 0 then ((z / 2 : Nat) : Int) else -(((z + 1) / 2 : Nat) : Int),
    hiOff := (v >>> 24) % 2 ^ 24 }

def relocs (c : RChunk) : List Reloc := (List.range c.nrel).map c.reloc

/-- The function the chunk stands for. -/
def func (c : RChunk) : RFunc := ⟨symOfCode c.name, c.words, c.relocs⟩

/-- `fs` is a sublist of `fs'`, with `ks` the functions skipped before each. -/
def subSeq : List RChunk → List Nat → List RChunk → Bool
  | [], _, _ => true
  | c :: cs, k :: ks, fs' =>
    match fs'.drop k with
    | d :: rest => decide (d = c) && subSeq cs ks rest
    | [] => false
  | _ :: _, [], _ => false

theorem sublist_of_subSeq : ∀ {fs ks fs'}, subSeq fs ks fs' = true → List.Sublist fs fs'
  | [], _, fs', _ => List.nil_sublist fs'
  | _ :: _, [], _, h => by simp [subSeq] at h
  | c :: cs, k :: ks, fs', h => by
    cases hd : fs'.drop k with
    | nil => simp [subSeq, hd] at h
    | cons d rest =>
      simp only [subSeq, hd, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨rfl, h⟩ := h
      have h2 : List.Sublist (d :: cs) (d :: rest) := (sublist_of_subSeq h).cons_cons d
      rw [← hd] at h2
      exact h2.trans (List.drop_sublist k fs')

/-- The same over functions in groups (`gs.flatten`), from a cursor `cur`
    in the current group: `(0, k)` skips `k` more of `cur`; `(j + 1, k)`
    leaves `cur`, skips `j` groups and `k` functions of the next. A lookup
    walks groups and then one group, not the whole list. -/
def subSeqG : List RChunk → List (Nat × Nat) → List RChunk → List (List RChunk) → Bool
  | [], _, _, _ => true
  | c :: cs, (0, k) :: ks, cur, gs =>
    match cur.drop k with
    | d :: rest => decide (d = c) && subSeqG cs ks rest gs
    | [] => false
  | c :: cs, (j + 1, k) :: ks, _, gs =>
    match gs.drop j with
    | g :: gs' =>
      match g.drop k with
      | d :: rest => decide (d = c) && subSeqG cs ks rest gs'
      | [] => false
    | [] => false
  | _ :: _, [], _, _ => false

theorem flatten_drop_sublist : ∀ (j : Nat) (gs : List (List RChunk)),
    List.Sublist (gs.drop j).flatten gs.flatten
  | 0, gs => List.Sublist.refl _
  | _ + 1, [] => List.Sublist.refl _
  | j + 1, g :: gs => by
    simp only [List.drop_succ_cons, List.flatten_cons]
    exact (flatten_drop_sublist j gs).trans (List.sublist_append_right g _)

theorem sublist_of_subSeqG : ∀ {fs ks cur gs}, subSeqG fs ks cur gs = true →
    List.Sublist fs (cur ++ gs.flatten)
  | [], _, _, _, _ => List.nil_sublist _
  | _ :: _, [], _, _, h => by simp [subSeqG] at h
  | c :: cs, (0, k) :: ks, cur, gs, h => by
    cases hd : cur.drop k with
    | nil => simp [subSeqG, hd] at h
    | cons d rest =>
      simp only [subSeqG, hd, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨rfl, h⟩ := h
      have h2 := (sublist_of_subSeqG h).cons_cons d
      rw [← List.cons_append, ← hd] at h2
      exact h2.trans ((List.drop_sublist k cur).append_right _)
  | c :: cs, (j + 1, k) :: ks, cur, gs, h => by
    cases hg : gs.drop j with
    | nil => simp [subSeqG, hg] at h
    | cons g gs' =>
      cases hd : g.drop k with
      | nil => simp [subSeqG, hg, hd] at h
      | cons d rest =>
        simp only [subSeqG, hg, hd, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨rfl, h⟩ := h
        have h2 := (sublist_of_subSeqG h).cons_cons d
        rw [← List.cons_append, ← hd] at h2
        have h3 : List.Sublist (g.drop k ++ gs'.flatten) (gs.drop j).flatten := by
          rw [hg, List.flatten_cons]; exact (List.drop_sublist k g).append_right _
        exact ((h2.trans h3).trans (flatten_drop_sublist j gs)).trans (List.sublist_append_right cur _)

theorem subSeq_of_subSeqG {fs ks gs} (h : subSeqG fs ks [] gs = true) : List.Sublist fs gs.flatten := by
  simpa using sublist_of_subSeqG h

end RChunk

def DChunk.data (d : DChunk) : RData :=
  ⟨symOfCode d.name,
    d.parts.flatMap (fun p => (List.range p.1).map fun i => BitVec.ofNat 8 (p.2 >>> (8 * i))),
    d.writable⟩

/-- The module the chunks stand for. -/
def Module.ofChunks (fs : List RChunk) (ds : List DChunk := []) : Module :=
  ⟨fs.map RChunk.func, ds.map DChunk.data⟩

theorem Module.ofChunks_sub {fs fs' : List RChunk} {ds ds' : List DChunk}
    (h : List.Sublist fs fs') :
    ∀ g ∈ (Module.ofChunks fs ds).funcs, g ∈ (Module.ofChunks fs' ds').funcs :=
  fun _ hg => (h.map RChunk.func).subset hg

/-- Distinct names in the smaller module, from the larger one's `Ok`. -/
theorem Module.ofChunks_names {fs fs' : List RChunk} {ds ds' : List DChunk}
    {L : Layout} (h : List.Sublist fs fs') (hL : (Module.ofChunks fs' ds').Ok L) :
    ((Module.ofChunks fs ds).funcs.map (·.name)).Nodup :=
  hL.names.sublist ((h.map RChunk.func).map _)

/-- An unchanged function's theorem, carried to a module in chunks: `fs`
    (the module the theorem is about) is a sublist of `fs'`. -/
theorem Verified.of_sublist {α : Type} {fs fs' : List RChunk} {ds ds' : List DChunk}
    {f : Sym} {sp : Layout → Spec α} (hs : List.Sublist fs fs')
    (h : Verified (Module.ofChunks fs ds) f sp) : Verified (Module.ofChunks fs' ds') f sp :=
  fun L hL => Verified.of_sub (Module.ofChunks_sub hs) (Module.ofChunks_names hs hL) h L hL

/-- The same with the sublist decided by `RChunk.subSeq`. -/
theorem Verified.of_chunks {α : Type} {fs fs' : List RChunk} {ks : List Nat} {ds ds' : List DChunk}
    {f : Sym} {sp : Layout → Spec α} (hs : RChunk.subSeq fs ks fs' = true)
    (h : Verified (Module.ofChunks fs ds) f sp) : Verified (Module.ofChunks fs' ds') f sp :=
  Verified.of_sublist (RChunk.sublist_of_subSeq hs) h

/-- The same with the larger module's functions in groups (`RChunk.subSeqG`):
    what the whole-artifact files use. -/
theorem Verified.of_groups {α : Type} {fs : List RChunk} {gs : List (List RChunk)}
    {ks : List (Nat × Nat)} {ds ds' : List DChunk} {f : Sym} {sp : Layout → Spec α}
    (hs : RChunk.subSeqG fs ks [] gs = true)
    (h : Verified (Module.ofChunks fs ds) f sp) : Verified (Module.ofChunks gs.flatten ds') f sp :=
  Verified.of_sublist (RChunk.subSeq_of_subSeqG hs) h

/-- The theorem does not depend on the order of the module's functions. -/
theorem Verified.of_perm {α : Type} {fs fs' : List RChunk} {ds : List DChunk} {f : Sym}
    {sp : Layout → Spec α} (hp : List.Perm fs fs')
    (h : Verified (Module.ofChunks fs ds) f sp) : Verified (Module.ofChunks fs' ds) f sp :=
  fun L hL => Verified.of_sub (fun _ hg => ((hp.map RChunk.func).subset hg))
    (hL.names.perm ((hp.map RChunk.func).map _).symm) h L hL

/-- `Verified.of_groups` when the closure's functions come in another order
    in the larger module: `fs'` is `fs` reordered (decided by `List.Perm`,
    on the same constants), and `fs'` is what is found in the groups. -/
theorem Verified.of_groups_perm {α : Type} {fs fs' : List RChunk} {gs : List (List RChunk)}
    {ks : List (Nat × Nat)} {ds ds' : List DChunk} {f : Sym} {sp : Layout → Spec α}
    (hp : List.Perm fs fs') (hs : RChunk.subSeqG fs' ks [] gs = true)
    (h : Verified (Module.ofChunks fs ds) f sp) : Verified (Module.ofChunks gs.flatten ds') f sp :=
  Verified.of_groups hs (Verified.of_perm hp h)

/-- An unchanged verified function refines itself across two modules in
    chunks that both hold `fs`, at one layout. -/
theorem Refines.of_chunks {α : Type} {fs fa fb : List RChunk} {ka kb : List Nat}
    {ds da db : List DChunk} {L : Layout} {f : Sym} {sp : Layout → Spec α}
    (hA : (Module.ofChunks fa da).Ok L) (hB : (Module.ofChunks fb db).Ok L)
    (hsa : RChunk.subSeq fs ka fa = true) (hsb : RChunk.subSeq fs kb fb = true)
    (hv : Verified (Module.ofChunks fs ds) f sp) :
    let M := Module.ofChunks fs ds
    Refines (sp L) ((Module.ofChunks fa da).link L) (M.dom L f) (L.addr f)
      ((Module.ofChunks fb db).link L) (M.dom L f) (L.addr f) :=
  Refines.of_sub_verified hA hB (Module.ofChunks_sub (RChunk.sublist_of_subSeq hsa))
    (Module.ofChunks_sub (RChunk.sublist_of_subSeq hsb)) (Module.ofChunks_names (RChunk.sublist_of_subSeq hsa) hA) hv

/-- The same with both modules' functions in groups. -/
theorem Refines.of_groups {α : Type} {fs : List RChunk} {ga gb : List (List RChunk)}
    {ka kb : List (Nat × Nat)} {ds da db : List DChunk} {L : Layout} {f : Sym} {sp : Layout → Spec α}
    (hA : (Module.ofChunks ga.flatten da).Ok L) (hB : (Module.ofChunks gb.flatten db).Ok L)
    (hsa : RChunk.subSeqG fs ka [] ga = true) (hsb : RChunk.subSeqG fs kb [] gb = true)
    (hv : Verified (Module.ofChunks fs ds) f sp) :
    let M := Module.ofChunks fs ds
    Refines (sp L) ((Module.ofChunks ga.flatten da).link L) (M.dom L f) (L.addr f)
      ((Module.ofChunks gb.flatten db).link L) (M.dom L f) (L.addr f) :=
  have ha := RChunk.subSeq_of_subSeqG hsa
  Refines.of_sub_verified hA hB (Module.ofChunks_sub ha)
    (Module.ofChunks_sub (RChunk.subSeq_of_subSeqG hsb)) (Module.ofChunks_names ha hA) hv

/-- `Refines.of_groups` with the closure in another order in `B`'s groups. -/
theorem Refines.of_groups_perm {α : Type} {fs fs' : List RChunk} {ga gb : List (List RChunk)}
    {ka kb : List (Nat × Nat)} {ds da db : List DChunk} {L : Layout} {f : Sym} {sp : Layout → Spec α}
    (hA : (Module.ofChunks ga.flatten da).Ok L) (hB : (Module.ofChunks gb.flatten db).Ok L)
    (hsa : RChunk.subSeqG fs ka [] ga = true) (hp : List.Perm fs fs')
    (hsb : RChunk.subSeqG fs' kb [] gb = true)
    (hv : Verified (Module.ofChunks fs ds) f sp) :
    let M := Module.ofChunks fs ds
    Refines (sp L) ((Module.ofChunks ga.flatten da).link L) (M.dom L f) (L.addr f)
      ((Module.ofChunks gb.flatten db).link L) (M.dom L f) (L.addr f) :=
  have ha := RChunk.subSeq_of_subSeqG hsa
  Refines.of_sub_verified hA hB (Module.ofChunks_sub ha)
    (fun _ hg => (((RChunk.subSeq_of_subSeqG hsb).map RChunk.func).subset
      ((hp.map RChunk.func).subset hg))) (Module.ofChunks_names ha hA) hv

end NoCompiler
