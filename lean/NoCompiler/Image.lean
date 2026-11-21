import NoCompiler.Mem
import NoCompiler.Step

/-
The data of a binary: every allocated section that is not code (`.rodata`,
`.data`, `.bss`, ...), as `nocompiler export` writes it next to the code image.

A proof that reads a constant (a string in `.rodata`, a table in `.data`)
assumes `Segment.Loaded` for its segment at entry, the way it assumes
`Code.Loaded` for the code: it is what the loader establishes. `nocompiler-audit`
re-reads each segment from the ELF file in Lean and checks it byte for byte
against the exported one, so the exporter is not trusted for the contents.
-/
namespace NoCompiler

structure Segment where
  name : String
  base : Word
  bytes : Array Byte
  /-- The section is writable (SHF_WRITE): a proof cannot assume it unchanged
      after code it does not control has run. -/
  writable : Bool
  deriving DecidableEq

namespace Segment

/-- `len` bytes, byte `i` the 8 bits of `bits` from bit `8 * i`: how
    `nocompiler export --format chunks` writes a segment's contents (one number
    literal, see `Chunk`). -/
def bytesOfNat (len bits : Nat) : Array Byte := ((List.range len).map fun i => BitVec.ofNat 8 (bits >>> (8 * i))).toArray

@[simp] theorem size_bytesOfNat (len bits : Nat) : (bytesOfNat len bits).size = len := by simp [bytesOfNat]

/-- Memory holds the segment. -/
def Loaded (g : Segment) (m : Word → Byte) : Prop :=
  ∀ i (h : i < g.bytes.size), m (g.base + BitVec.ofNat 64 i) = g.bytes[i]

def region (g : Segment) : Region := ⟨g.base, g.bytes.size⟩

/-- Reading `n` bytes at offset `o` of a loaded segment. -/
theorem readBytes_of_loaded {g : Segment} {m : Word → Byte} (h : g.Loaded m) :
    ∀ (o n : Nat), o + n ≤ g.bytes.size →
      readBytes m (g.base + BitVec.ofNat 64 o) n = (g.bytes.toList.drop o).take n := by
  intro o n
  induction n generalizing o with
  | zero => intro _; simp [readBytes]
  | succ n ih =>
    intro hon
    have ho : o < g.bytes.size := by omega
    simp only [readBytes]
    have e : g.base + BitVec.ofNat 64 o + 1 = g.base + BitVec.ofNat 64 (o + 1) := by
      apply BitVec.eq_of_toNat_eq; simp; omega
    rw [h o ho, e, ih (o + 1) (by omega)]
    have hl : o < g.bytes.toList.length := by simpa using ho
    have : List.drop o g.bytes.toList = g.bytes.toList[o] :: List.drop (o + 1) g.bytes.toList :=
      List.drop_eq_getElem_cons hl
    rw [this]
    simp

end Segment

/-! ## Code in chunks

A binary's `.text` as `nocompiler export --format chunks` writes it: one chunk
per symbol (a long function in several), each a short literal with its offset
in words from the start of `.text`. The image is still the trusted `Code`, one
array (`Code.ofChunks`); what changes is how a proof gets at an instruction.
`Chunk.contig` checks once, in time linear in the number of chunks, that the
offsets are where the chunks are; then `Code.ofChunks_instr` gives, for chunk
`k`, that the image agrees with the chunk's own small `Code` on the chunk's
range, without the kernel ever walking the words before it. A proof about a
function runs on its chunks (`VerifiedImg.congr_code`, Module.lean), and no
lemma per instruction is needed.

`Code.ofChunks base cs` is `⟨base, (cs.map Chunk.words).flatten.toArray⟩`,
which is C's `Code.ofSegs base (cs.map Chunk.words)` (NoCompiler/VC/Seg.lean),
and `Chunk.contig` gives its `segOffset` (`Chunk.segOffset_eq`).
-/

/-- Words of `.text` at offset `off` (in words) from its start: `len` words,
    word `i` the 32 bits of `bits` from bit `32 * i`. One number literal per
    chunk, not one literal per word: elaborating a `BitVec` literal costs
    about a millisecond and its share of memory, a number literal of any size
    almost nothing, and the kernel's `Nat` arithmetic is native. -/
structure Chunk where
  off : Nat
  len : Nat
  bits : Nat
  deriving DecidableEq

namespace Chunk

def words (c : Chunk) : List (BitVec 32) := (List.range c.len).map fun i => BitVec.ofNat 32 (c.bits >>> (32 * i))

@[simp] theorem length_words (c : Chunk) : c.words.length = c.len := by simp [words]

/-- The chunk on its own, at its address. -/
def code (base : Word) (c : Chunk) : Code := ⟨base + BitVec.ofNat 64 (4 * c.off), c.words.toArray⟩

/-- The chunk's bytes, as a range of a `Dom`. -/
def range (base : Word) (c : Chunk) : Word × Nat := (base + BitVec.ofNat 64 (4 * c.off), 4 * c.len)

/-- The chunks are back to back from offset `o`. Reads only the offsets and
    lengths, so `decide` never decodes a word. -/
def contig : Nat → List Chunk → Bool
  | _, [] => true
  | o, c :: cs => c.off == o && contig (o + c.len) cs

/-- The words of all the chunks. -/
def total (cs : List Chunk) : Nat := (cs.map Chunk.len).sum

theorem length_flatten (cs : List Chunk) : (cs.map Chunk.words).flatten.length = total cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [total] at ih ⊢; omega

theorem split_of_contig :
    ∀ (o : Nat) (cs : List Chunk) (k : Nat) (c : Chunk), contig o cs = true → cs[k]? = some c →
      ∃ pre post, (cs.map Chunk.words).flatten = pre ++ c.words ++ post ∧ o + pre.length = c.off
  | _, [], _, _, _, hk => by simp at hk
  | o, d :: ds, 0, c, h, hk => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk
    simp only [contig, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨[], (ds.map Chunk.words).flatten, by simp, by simp [h.1]⟩
  | o, d :: ds, k + 1, c, h, hk => by
    simp only [List.getElem?_cons_succ] at hk
    simp only [contig, Bool.and_eq_true] at h
    obtain ⟨pre, post, he, hl⟩ := split_of_contig (o + d.len) ds k c h.2 hk
    exact ⟨d.words ++ pre, post, by simp [he], by simp; omega⟩

end Chunk

/-- `.text` from its chunks. -/
def Code.ofChunks (base : Word) (cs : List Chunk) : Code := ⟨base, (cs.map Chunk.words).flatten.toArray⟩

/-- The image agrees with chunk `k`'s own code wherever the chunk is. -/
theorem Code.ofChunks_fetch {base : Word} {cs : List Chunk} {k : Nat} {c : Chunk}
    (h : Chunk.contig 0 cs = true) (hk : cs[k]? = some c)
    (hb : 4 * Chunk.total cs < 2 ^ 64) {x : Word}
    (hx : (x - (c.code base).base).toNat < 4 * c.len) :
    (Code.ofChunks base cs).fetch x = (c.code base).fetch x := by
  obtain ⟨pre, post, he, hl⟩ := Chunk.split_of_contig 0 cs k c h hk
  simp only [Nat.zero_add] at hl
  have hwl := Chunk.length_words c
  have hlen : 4 * (pre.length + c.len) < 2 ^ 64 := by
    rw [← Chunk.length_flatten, he] at hb; simp only [List.length_append] at hb; omega
  simp only [Chunk.code] at hx ⊢
  have hx' : (x - base).toNat = 4 * c.off + (x - (base + BitVec.ofNat 64 (4 * c.off))).toNat := by
    have : x - base = (x - (base + BitVec.ofNat 64 (4 * c.off))) + BitVec.ofNat 64 (4 * c.off) := by
      bv_omega
    rw [this, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 * c.off) (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  generalize hj : (x - (base + BitVec.ofNat 64 (4 * c.off))).toNat = j at hx hx'
  simp only [Code.fetch, Code.ofChunks, hx', hj, he]
  have h4 : (4 * c.off + j) % 4 = j % 4 := by omega
  rw [h4]
  split
  · have hd : (4 * c.off + j) / 4 = pre.length + j / 4 := by omega
    rw [hd]
    simp only [List.getElem?_toArray, List.append_assoc]
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left (by omega)]
  · rfl

theorem Code.ofChunks_instr {base : Word} {cs : List Chunk} {k : Nat} {c : Chunk}
    (h : Chunk.contig 0 cs = true) (hk : cs[k]? = some c)
    (hb : 4 * Chunk.total cs < 2 ^ 64) :
    ∀ x, Dom.mem [c.range base] x → (Code.ofChunks base cs).instr x = (c.code base).instr x := by
  intro x hx
  simp only [Dom.mem, List.any_cons, List.any_nil, Bool.or_false, decide_eq_true_eq, Chunk.range] at hx
  simp only [Code.instr, Code.ofChunks_fetch h hk hb (x := x) (by simpa [Chunk.code] using hx)]

/-- Where chunk `k` starts, as C's `segOffset` computes it (NoCompiler/VC/Seg.lean):
    its recorded offset. -/
theorem Chunk.offset_eq {cs : List Chunk} {k : Nat} {c : Chunk}
    (h : Chunk.contig 0 cs = true) (hk : cs[k]? = some c) :
    (((cs.map Chunk.words).take k).map List.length).sum = c.off := by
  suffices ∀ o (cs : List Chunk) k, Chunk.contig o cs = true → cs[k]? = some c →
      o + (((cs.map Chunk.words).take k).map List.length).sum = c.off by simpa using this 0 cs k h hk
  intro o cs
  induction cs generalizing o with
  | nil => intro k _ hk; simp at hk
  | cons d ds ih =>
    intro k h hk
    simp only [Chunk.contig, Bool.and_eq_true, beq_iff_eq] at h
    cases k with
    | zero => simp at hk; subst hk; simp [h.1]
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk
      have := ih (o + d.len) k h.2 hk
      simp only [List.map_cons, List.take_succ_cons, List.map_cons, List.sum_cons, Chunk.length_words]; omega

end NoCompiler
