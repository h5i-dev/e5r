import NoCompiler.Struct

/-
The register, stack and frame rules R4 to R6 of the profile, version 1
(docs/isa/v1.md), as an executable checker, and the conformance level a
function reaches: L0 when it decodes, L1 with R1 to R3 (`Struct.check`), L2
with R4 to R6 as well.

R5 (one `sp` offset per instruction) and 6e (saved registers back at every
return) are dataflow properties. The checker does not run the dataflow: it
checks a certificate, a `Fact` per instruction, against each instruction and
its successors, one instruction at a time. `nocompiler export` computes the
certificate (crates/nocompiler/src/frame.rs) and writes it next to the
function's tree and frame partition, and `<name>_checked` states the level,
proved by `decide`. A wrong certificate, partition or tree only lowers the
level; nothing is trusted about any of them.

The Rust checker decides the same rules and is what reports violations by
name; this one is what the kernel evaluates.
-/
namespace NoCompiler
namespace Struct

/-- What an 8-byte frame slot holds (rule 6b): the entry value of a register
    (`ra`, `s0` to `s11`), or a spill. -/
inductive SlotKind | save (r : Nat) | spill
  deriving DecidableEq, Repr

/-- A slot at `off` bytes above the bottom of the frame. -/
structure Slot where
  off : Nat
  kind : SlotKind
  deriving DecidableEq, Repr

/-- An address-taken range: `len` bytes from `off` above the bottom of the frame. -/
structure Range where
  off : Nat
  len : Nat
  deriving DecidableEq, Repr

/-- A function's frame: `size` bytes below the entry `sp`, and its partition. -/
structure Frame where
  size : Nat
  slots : List Slot
  ranges : List Range
  deriving DecidableEq, Repr

/-- The dataflow fact before an instruction: `sp` is `depth` bytes below its
    entry value (R5); the saved registers in `keep` hold their entry value;
    each `(k, r)` in `held` is a slot at `k` holding the entry value of `r`
    (6e). -/
structure Fact where
  depth : Nat
  keep : List Nat
  held : List (Nat × Nat)
  deriving DecidableEq, Repr

/-- Registers whose entry value a function gives back (6e): `ra`, `s0` to `s11`. -/
def savedRegs : List Nat := [1, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

def Fact.entry : Fact := ⟨0, savedRegs, []⟩

/-- `g` promises no more than `f`: the fact at a successor follows from the
    fact after the instruction. -/
def Fact.le (g f : Fact) : Bool :=
  g.depth == f.depth && g.keep.all (f.keep.contains ·) && g.held.all (f.held.contains ·)

/-- The facts, one per instruction of the function. -/
abbrev Cert := List Fact

/-- The registers of a bit mask, in increasing order: how
    `nocompiler export --format chunks` writes a fact's `keep`. -/
def regsOfMask (m : Nat) : List Nat := (List.range 32).filter fun r => m.testBit r

/-- A certificate as runs: `(n, depth, keep as a mask, held)` is `n` equal
    facts in a row. What `nocompiler export --format chunks` writes, so that a
    certificate costs a few literals per run, not per instruction. -/
def Cert.ofRuns (rs : List (Nat × Nat × Nat × List (Nat × Nat))) : Cert :=
  rs.flatMap fun (n, d, m, h) => List.replicate n ⟨d, regsOfMask m, h⟩

namespace Frame

def slotAt (fr : Frame) (k : Int) : Option Slot :=
  fr.slots.find? fun s => (s.off : Int) == k

def saveOf (fr : Frame) (r : Nat) : Option Slot :=
  fr.slots.find? fun s => s.kind == .save r

/-- `[k, k + w)` lies in one range. -/
def inRange (fr : Frame) (k : Int) (w : Nat) : Bool :=
  fr.ranges.any fun g => (g.off : Int) ≤ k && k + w ≤ g.off + g.len

/-- `k` is inside a range or at its end (6d). -/
def pointsInto (fr : Frame) (k : Int) : Bool :=
  fr.ranges.any fun g => (g.off : Int) ≤ k && k ≤ g.off + g.len

/-- 6b: slots are aligned 8 bytes inside the frame, ranges nonempty and
    inside it, nothing overlaps, at most one save slot per register, and only
    for `ra` and `s0` to `s11`. -/
def wellFormed (fr : Frame) : Bool :=
  let spans : List (Nat × Nat) := fr.slots.map (fun s => (s.off, s.off + 8)) ++
    fr.ranges.map (fun g => (g.off, g.off + g.len))
  fr.slots.all (fun s => s.off % 8 == 0 && s.off + 8 ≤ fr.size &&
    match s.kind with
    | .save r => savedRegs.contains r && (fr.slots.filter (·.kind == .save r)).length == 1
    | .spill => true) &&
  fr.ranges.all (fun g => 0 < g.len && g.off + g.len ≤ fr.size) &&
  (List.range spans.length).all fun i => (List.range spans.length).all fun j =>
    i == j || (spans.getD i (0, 0)).2 ≤ (spans.getD j (0, 0)).1 ||
      (spans.getD j (0, 0)).2 ≤ (spans.getD i (0, 0)).1

end Frame

/-- The register an instruction writes (none for x0, branches, stores). -/
def _root_.NoCompiler.Instr.dst : Instr → Option Nat
  | .lui rd _ | .auipc rd _ | .jal rd _ | .jalr rd _ _ | .load _ rd _ _ | .iop _ rd _ _
  | .addiw rd _ _ | .shift _ rd _ _ | .shiftw _ rd _ _ | .rop _ rd _ _ | .rwop _ rd _ _
  | .uop _ rd _ => if rd.val = 0 then none else some rd.val
  | .ecall => some 10
  | .branch .. | .store .. => none

/-- The registers an instruction reads. -/
def _root_.NoCompiler.Instr.srcs : Instr → List Nat
  | .lui .. | .auipc .. | .jal .. | .ecall => []
  | .jalr _ a _ | .load _ _ a _ | .iop _ _ a _ | .addiw _ a _ | .shift _ _ a _
  | .shiftw _ _ a _ | .uop _ _ a => [a.val]
  | .branch _ a b _ | .store _ a b _ | .rop _ _ a b | .rwop _ _ a b => [a.val, b.val]

/-- 6a: the forms in which `sp` may be an operand. -/
def spFormOk : Instr → Bool
  | .iop .addi _ _ _ => true      -- addi sp, sp, k and addi rd, sp, k
  | .load .. => true              -- sp only as the base
  | .store _ _ src _ => src.val != 2
  | i => !i.srcs.contains 2

/-- Where control may go after the instruction at `pc` in a function that
    passed `check`: the next instruction, a branch or jump target inside it,
    or nowhere (a return, a tail call). -/
def succs (f : Func) (pc : Word) : Instr → List Word
  | .branch _ _ _ off => [pc + 4, pc + off.signExtend 64]
  | .jal rd off =>
    if rd.val = 0 then (if f.contains (pc + off.signExtend 64) then [pc + off.signExtend 64] else [])
    else [pc + 4]
  | .jalr rd _ _ => if rd.val = 0 then [] else [pc + 4]
  | _ => [pc + 4]

/-- The instruction leaves the function (a return or a tail call). -/
def leaves (f : Func) (pc : Word) : Instr → Bool
  | .jal rd off => rd.val = 0 && !f.contains (pc + off.signExtend 64)
  | .jalr rd _ _ => rd.val = 0
  | _ => false

/-- The instruction calls (it links `ra`). -/
def calls : Instr → Bool
  | .jal rd _ | .jalr rd _ _ => rd.val == 1
  | _ => false

/-- The frame offset of `k(sp)` when `sp` is `d` bytes below its entry value. -/
def frameOff (fr : Frame) (d : Nat) (k : BitVec 12) : Int := (fr.size : Int) - d + k.toInt

/-- The fact after the instruction, if it keeps R4 to R6 at fact `F`; `ra`
    may also be written by the `auipc ra` of a call (`pairNext`). -/
def step (fr : Frame) (pairNext : Bool) (F : Fact) (i : Instr) : Option Fact :=
  let drop (r : Nat) (F : Fact) : Fact := { F with keep := F.keep.filter (· != r) }
  let base : Option Fact := match i with
    -- sp: R5
    | .iop .addi rd rs1 k =>
      if rd.val = 2 then
        if rs1.val = 2 && k.toInt % 16 == 0 && 0 ≤ (F.depth : Int) - k.toInt &&
            (F.depth : Int) - k.toInt ≤ fr.size then
          some { F with depth := ((F.depth : Int) - k.toInt).toNat }
        else none
      else if rs1.val = 2 then
        -- 6d: an address in a range, or its end
        if fr.pointsInto (frameOff fr F.depth k) then some (drop rd.val F) else none
      else some (match i.dst with | some r => drop r F | none => F)
    | .load op rd rs1 k =>
      if rs1.val = 2 then
        let o := frameOff fr F.depth k
        let isSlot := op == .ld && (fr.slotAt o).isSome
        if 0 ≤ o && o + op.width ≤ fr.size && (isSlot || fr.inRange o op.width) then
          if rd.val = 0 then some F
          else if isSlot && F.held.contains (o.toNat, rd.val) then
            some { F with keep := rd.val :: F.keep.filter (· != rd.val) }
          else some (drop rd.val F)
        else none
      else some (match i.dst with | some r => drop r F | none => F)
    | .store op base src k =>
      if base.val = 2 then
        let o := frameOff fr F.depth k
        let held := F.held.filter (fun h => (h.1 : Int) != o)
        if 0 ≤ o && o + op.width ≤ fr.size then
          match fr.slotAt o with
          | some s =>
            if op != .sd then none
            else match s.kind with
              | .save r =>
                -- 6e: a save slot only receives its register's entry value
                if src.val == r && F.keep.contains r then some { F with held := (o.toNat, r) :: held }
                else none
              | .spill => some { F with held := held }
          | none => if fr.inRange o op.width then some { F with held := held } else none
        else none
      else some F
    | _ => some (match i.dst with | some r => drop r F | none => F)
  match base with
  | none => none
  | some G =>
    -- R4: gp and tp are never written; ra only by a call (or the auipc of
    -- one) or an ld from its save slot.
    let raOk := i.dst != some 1 || calls i ||
      (pairNext && (match i with | .auipc .. => true | _ => false)) ||
      (match i with
       | .load .ld _ rs1 k => rs1.val == 2 && (fr.saveOf 1).any (fun s => (s.off : Int) == frameOff fr F.depth k)
       | _ => false)
    -- sp only by addi sp, sp, k (R5); 6a.
    if (i.dst == some 3 || i.dst == some 4) || !raOk || !spFormOk i then none
    else if i.dst == some 2 && !(match i with | .iop .addi _ rs1 _ => rs1.val = 2 | _ => false) then none
    else if calls i && F.depth % 16 != 0 then none
    else some G

/-- R4 to R6 at one instruction: its step from the certificate's fact, the
    successors' facts follow, and at a return or tail call `sp` and the
    saved registers are back. -/
def instrL2 (c : Code) (f : Func) (fr : Frame) (cert : Cert) (pc : Word) : Bool :=
  let at_ (p : Word) : Fact := cert.getD ((p - f.entry).toNat / 4) Fact.entry
  match c.instr pc with
  | none => false
  | some i =>
    let F := at_ pc
    let pairNext := match c.instr (pc + 4) with
      | some (.jalr 1 1 _) => true
      | _ => false
    match step fr pairNext F i with
    | none => false
    | some G =>
      (succs f pc i).all (fun s => !f.contains s || (at_ s).le G) &&
      (!leaves f pc i || (F.depth == 0 && savedRegs.all (F.keep.contains ·)))

/-- 6e: a save slot for every saved register the function writes, and for
    `ra` if it calls. -/
def savesOk (c : Code) (f : Func) (fr : Frame) : Bool :=
  let ins := (List.range f.len).filterMap fun i => c.instr (f.entry + BitVec.ofNat 64 (4 * i))
  ins.all (fun i => match i.dst with
    | some r => r == 1 || !savedRegs.contains r || (fr.saveOf r).isSome
    | none => true) &&
  (!ins.any calls || (fr.saveOf 1).isSome)

/-- R4 to R6 for `f` with frame `fr` and certificate `cert`. -/
def checkL2 (c : Code) (f : Func) (fr : Frame) (cert : Cert) : Bool :=
  fr.wellFormed && savesOk c f fr && cert.length == f.len && cert.head? == some Fact.entry &&
  cert.all (·.depth ≤ fr.size) &&
  (List.range f.len).all fun i => instrL2 c f fr cert (f.entry + BitVec.ofNat 64 (4 * i))

/-- The conformance levels (docs/isa/v1.md). -/
inductive Level | l0 | l1 | l2
  deriving DecidableEq, Repr

/-- The level `f` reaches; `none` when some word does not decode (R1). -/
def level (c : Code) (f : Func) (entries : List Word) (fr : Frame) (cert : Cert) : Option Level :=
  if !(List.range f.len).all (fun i => (c.instr (f.entry + BitVec.ofNat 64 (4 * i))).isSome) then none
  else if !check c f entries then some .l0
  else if checkL2 c f fr cert then some .l2
  else some .l1

theorem check_of_level {c : Code} {f : Func} {entries : List Word} {fr : Frame} {cert : Cert}
    {l : Level} (h : level c f entries fr cert = some l) (hl : l ≠ .l0) : check c f entries = true := by
  unfold level at h
  split at h
  · cases h
  · split at h
    · cases h; exact absurd rfl hl
    · rename_i h2; simpa using h2

theorem checkL2_of_level {c : Code} {f : Func} {entries : List Word} {fr : Frame} {cert : Cert}
    (h : level c f entries fr cert = some .l2) : checkL2 c f fr cert = true := by
  unfold level at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · assumption
      · cases h

/-! ## The same level, in time about linear in the function

`level` reads an instruction with `c.instr`, an `Array` index the kernel
reduces as a walk down the list under the array, and the certificate with
`List.getD`: both linear in the index, at every instruction, so `decide` on
`level` is quadratic in the function's size (docs/isa/v1-results.md, 7').
`levelFast` is `level` with those two reads replaced: the function's words are
decoded once into an `ITree` (a Braun tree: logarithmic lookup), and the
certificate is put in another. `levelFast_eq` proves it equal to `level`, so
`<f>_checked` keeps its statement and is proved as `level_of_fast (by decide)`.
-/

/-- `level` with the reads of an instruction (`I`) and of the certificate's fact
    at an address (`A`) as parameters (`levelW_spec`: with `c.instr` and
    `cert.getD`, it is `level`). -/
def pairAtW (I : Word → Option Instr) (f : Func) (pc : Word) : Option (Reg × Word) :=
  if f.contains (pc - 4) then pairOf (I pc) (I (pc - 4)) (pc - 4) else none

def instrOkW (I : Word → Option Instr) (E : Word → Bool) (f : Func) (pc : Word) : Bool :=
  match I pc with
  | none => false
  | some i =>
    let fall := f.contains (pc + 4)
    let local_ (t : Word) := f.contains t && f.target pc t && (pairAtW I f t).isNone
    match i with
    | .branch _ _ _ off => fall && local_ (pc + off.signExtend 64)
    | .jal rd off =>
      let t := pc + off.signExtend 64
      if rd = 0 then local_ t || E t
      else rd == 1 && E t && fall
    | .jalr rd rs1 off =>
      if rd = 0 && rs1 = 1 && off = 0 then true
      else match pairAtW I f pc with
        | some (r, v) =>
          let t := (v + off.signExtend 64) &&& ~~~1
          E t && ((rd == 1 && r == 1 && fall) || (rd == 0 && r == 6))
        | none => false
    | _ => fall

def checkW (I : Word → Option Instr) (E : Word → Bool) (f : Func) : Bool :=
  (List.range f.len).all fun i => instrOkW I E f (f.entry + BitVec.ofNat 64 (4 * i))

def instrL2W (I : Word → Option Instr) (A : Word → Fact) (f : Func) (fr : Frame) (pc : Word) : Bool :=
  match I pc with
  | none => false
  | some i =>
    let F := A pc
    let pairNext := match I (pc + 4) with
      | some (.jalr 1 1 _) => true
      | _ => false
    match step fr pairNext F i with
    | none => false
    | some G =>
      (succs f pc i).all (fun s => !f.contains s || (A s).le G) &&
      (!leaves f pc i || (F.depth == 0 && savedRegs.all (F.keep.contains ·)))

def savesOkW (I : Word → Option Instr) (f : Func) (fr : Frame) : Bool :=
  let ins := (List.range f.len).filterMap fun i => I (f.entry + BitVec.ofNat 64 (4 * i))
  ins.all (fun i => match i.dst with
    | some r => r == 1 || !savedRegs.contains r || (fr.saveOf r).isSome
    | none => true) &&
  (!ins.any calls || (fr.saveOf 1).isSome)

def checkL2W (I : Word → Option Instr) (A : Word → Fact) (f : Func) (fr : Frame) (cert : Cert) : Bool :=
  fr.wellFormed && savesOkW I f fr && cert.length == f.len && cert.head? == some Fact.entry &&
  cert.all (·.depth ≤ fr.size) &&
  (List.range f.len).all fun i => instrL2W I A f fr (f.entry + BitVec.ofNat 64 (4 * i))

def levelW (I : Word → Option Instr) (A : Word → Fact) (E : Word → Bool) (f : Func) (fr : Frame)
    (cert : Cert) : Option Level :=
  if !(List.range f.len).all (fun i => (I (f.entry + BitVec.ofNat 64 (4 * i))).isSome) then none
  else if !checkW I E f then some .l0
  else if checkL2W I A f fr cert then some .l2
  else some .l1

theorem levelW_spec (c : Code) (f : Func) (entries : List Word) (fr : Frame) (cert : Cert) :
    levelW c.instr (fun p => cert.getD ((p - f.entry).toNat / 4) Fact.entry) (entries.contains ·) f fr cert =
      level c f entries fr cert := rfl

/-- A Braun tree: the root is element 0, the left subtree the elements
    1, 3, 5, ..., the right one 2, 4, 6, ... -/
inductive ITree (α : Type) where
  | leaf
  | node (l : ITree α) (v : α) (r : ITree α)

namespace ITree

def get? {α : Type} : ITree α → Nat → Option α
  | leaf, _ => none
  | node l v r, i => if i = 0 then some v else if i % 2 = 1 then get? l (i / 2) else get? r (i / 2 - 1)

/-- Elements 0, 2, 4, ... -/
def evens {α : Type} : List α → List α
  | [] => []
  | [x] => [x]
  | x :: _ :: xs => x :: evens xs

/-- Elements 1, 3, 5, ... -/
def odds {α : Type} : List α → List α
  | [] => []
  | _ :: xs => evens xs

theorem evens_get {α : Type} : ∀ (xs : List α) (k : Nat), (evens xs)[k]? = xs[2 * k]?
  | [], _ => by simp [evens]
  | [_], 0 => by simp [evens]
  | [_], k + 1 => by simp [evens]
  | _ :: _ :: xs, 0 => by simp [evens]
  | _ :: _ :: xs, k + 1 => by
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega]
    simp only [evens, List.getElem?_cons_succ]
    exact evens_get xs k

theorem odds_get {α : Type} (xs : List α) (k : Nat) : (odds xs)[k]? = xs[2 * k + 1]? := by
  cases xs with
  | nil => simp [odds]
  | cons _ xs => simp only [odds, List.getElem?_cons_succ]; exact evens_get xs k

theorem length_evens_le {α : Type} : ∀ (xs : List α), (evens xs).length ≤ xs.length
  | [] => by simp [evens]
  | [_] => by simp [evens]
  | _ :: _ :: xs => by simp only [evens, List.length_cons]; have := length_evens_le xs; omega

theorem length_odds_le {α : Type} (xs : List α) : (odds xs).length ≤ xs.length := by
  cases xs with
  | nil => simp [odds]
  | cons _ xs => simp only [odds, List.length_cons]; have := length_evens_le xs; omega

/-- The tree of a list of at most `n` elements (`n` bounds the depth). -/
def ofListN {α : Type} : Nat → List α → ITree α
  | 0, _ => leaf
  | _ + 1, [] => leaf
  | n + 1, x :: xs => node (ofListN n (evens xs)) x (ofListN n (odds xs))

def ofList {α : Type} (xs : List α) : ITree α := ofListN xs.length xs

theorem get?_ofListN {α : Type} : ∀ (n : Nat) (xs : List α) (i : Nat), xs.length ≤ n →
    (ofListN n xs).get? i = xs[i]?
  | 0, xs, i, h => by
    have : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [ofListN, get?]
  | _ + 1, [], i, _ => by simp [ofListN, get?]
  | n + 1, x :: xs, i, h => by
    have hl : xs.length ≤ n := by simp at h; omega
    simp only [ofListN, get?]
    by_cases h0 : i = 0
    · subst h0; simp
    · simp only [h0, ↓reduceIte]
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [List.getElem?_cons_succ]
      by_cases h1 : (j + 1) % 2 = 1
      · simp only [h1, ↓reduceIte]
        rw [get?_ofListN n _ _ (Nat.le_trans (length_evens_le xs) hl), evens_get]
        rw [show 2 * ((j + 1) / 2) = j by omega]
      · simp only [h1, ↓reduceIte]
        rw [get?_ofListN n _ _ (Nat.le_trans (length_odds_le xs) hl), odds_get]
        rw [show 2 * ((j + 1) / 2 - 1) + 1 = j by omega]

theorem get?_ofList {α : Type} (xs : List α) (i : Nat) : (ofList xs).get? i = xs[i]? :=
  get?_ofListN _ xs i (Nat.le_refl _)

end ITree

/-- `f`'s words, decoded once: from word `(f.entry - c.base) / 4` of `c`. -/
def decoded (c : Code) (f : Func) : List (Option Instr) :=
  ((c.words.toList.drop ((f.entry - c.base).toNat / 4)).take f.len).map decode

/-- `f`'s words are where `decoded` takes them: aligned, and the function does
    not wrap around the address space. -/
def fastOk (c : Code) (f : Func) : Bool :=
  (f.entry - c.base).toNat % 4 == 0 && (f.entry - c.base).toNat + 4 * f.len < 2 ^ 64

/-- `c.instr`, from `T` inside `f`. -/
def instrFast (c : Code) (f : Func) (T : ITree (Option Instr)) (pc : Word) : Option Instr :=
  if f.contains pc then (T.get? ((pc - f.entry).toNat / 4)).getD none else c.instr pc

theorem instrFast_eq {c : Code} {f : Func} (h : fastOk c f = true) (pc : Word) :
    instrFast c f (ITree.ofList (decoded c f)) pc = c.instr pc := by
  unfold instrFast
  split
  · rename_i hc
    simp only [Func.contains, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    simp only [fastOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨hd, hd4⟩ := hc
    obtain ⟨he4, hb⟩ := h
    have hoff : (pc - c.base).toNat = (f.entry - c.base).toNat + (pc - f.entry).toNat := by
      have : pc - c.base = (pc - f.entry) + (f.entry - c.base) := by bv_omega
      rw [this, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
      omega
    generalize (pc - f.entry).toNat = d at hd hd4 hoff
    generalize he : (f.entry - c.base).toNat = e at he4 hb hoff
    simp only [Code.instr, Code.fetch, hoff, ITree.get?_ofList, decoded, he]
    simp only [show (e + d) % 4 = 0 by omega, ↓reduceIte]
    rw [List.getElem?_map, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      show e / 4 + d / 4 = (e + d) / 4 by omega, Array.getElem?_toList]
    cases c.words[(e + d) / 4]? <;> rfl
  · rfl

/-- The certificate's fact at an address, from `T`. -/
def certFast (f : Func) (T : ITree Fact) (p : Word) : Fact :=
  (T.get? ((p - f.entry).toNat / 4)).getD Fact.entry

theorem certFast_eq (f : Func) (cert : Cert) (p : Word) :
    certFast f (ITree.ofList cert) p = cert.getD ((p - f.entry).toNat / 4) Fact.entry := by
  simp [certFast, ITree.get?_ofList, List.getD_eq_getElem?_getD]

/-- Binary search for `t` among the elements `[lo, hi)` of `T`, by address
    (`fuel` bounds the steps). `true` only if it finds `t` (`bsearch_sound`);
    a miss says nothing, so `entriesFast` falls back to the list. -/
def bsearch (T : ITree Word) (t : Word) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      match T.get? mid with
      | none => false
      | some x =>
        if x == t then true
        else if x.toNat < t.toNat then bsearch T t fuel (mid + 1) hi
        else bsearch T t fuel lo mid
    else false

theorem bsearch_sound {T : ITree Word} {t : Word} :
    ∀ (fuel lo hi : Nat), bsearch T t fuel lo hi = true → ∃ i, T.get? i = some t
  | 0, _, _, h => by simp [bsearch] at h
  | fuel + 1, lo, hi, h => by
    unfold bsearch at h
    split at h
    · dsimp only at h
      split at h
      · cases h
      · rename_i x hx
        split at h
        · rename_i he; exact ⟨_, by rw [hx, beq_iff_eq.1 he]⟩
        · split at h
          · exact bsearch_sound fuel _ _ h
          · exact bsearch_sound fuel _ _ h
    · cases h

/-- `entries.contains t`: a binary search in `T`, else the list. The list is
    sorted as `nocompiler export` writes it, so a call's target costs a
    logarithm; a walk down the list costs the kernel about 0.15 ms per element
    whatever it compares (1235 entries in the 7' artifact). -/
def entriesFast (entries : List Word) (T : ITree Word) (t : Word) : Bool :=
  bsearch T t 64 0 entries.length || entries.contains t

theorem entriesFast_eq (entries : List Word) (t : Word) :
    entriesFast entries (ITree.ofList entries) t = entries.contains t := by
  unfold entriesFast
  cases h : bsearch (ITree.ofList entries) t 64 0 entries.length
  · simp
  · obtain ⟨i, hi⟩ := bsearch_sound _ _ _ h
    rw [ITree.get?_ofList] at hi
    have : t ∈ entries := List.mem_of_getElem? hi
    simp [this]

/-- `level`, reading the function's instructions, its certificate and the
    entries from trees built once. -/
def levelFast (c : Code) (f : Func) (entries : List Word) (fr : Frame) (cert : Cert) : Option Level :=
  if fastOk c f then
    levelW (instrFast c f (ITree.ofList (decoded c f))) (certFast f (ITree.ofList cert))
      (entriesFast entries (ITree.ofList entries)) f fr cert
  else level c f entries fr cert

theorem levelFast_eq (c : Code) (f : Func) (entries : List Word) (fr : Frame) (cert : Cert) :
    levelFast c f entries fr cert = level c f entries fr cert := by
  unfold levelFast
  split
  · rename_i h
    rw [← levelW_spec]
    congr 1
    · funext pc; exact instrFast_eq h pc
    · funext p; exact certFast_eq f cert p
    · funext t; exact entriesFast_eq entries t
  · rfl

theorem level_of_fast {c : Code} {f : Func} {entries : List Word} {fr : Frame} {cert : Cert} {l : Level}
    (h : levelFast c f entries fr cert = some l) : level c f entries fr cert = some l :=
  levelFast_eq c f entries fr cert ▸ h

end Struct
end NoCompiler
