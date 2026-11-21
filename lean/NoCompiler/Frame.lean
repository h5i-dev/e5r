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

end Struct
end NoCompiler
