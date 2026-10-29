/-
  A single-hart platform: RAM, a read-only executable image, and a table of
  device registers, interpreting the effect trees of `Theories/Hart.lean`.

  Original e5r code, Apache-2.0.

  The platform is deliberately an over-approximation of the board in the
  directions that cannot make a proof unsound:

  * A device register read returns any value (the environment picks it).
  * Any enabled interrupt may be taken at any instruction boundary, whether or
    not a real device would have raised it by then.
  * An SC with a reservation may succeed or fail.

  and it fails closed everywhere else: an access the board description does
  not name is `unsupported`, never a guessed value.
-/
import Theories.Hart

set_option linter.constructorNameAsVariable false

namespace E5R

/-- A device register: a word-aligned, word-sized address. Reads (if
    allowed) return environmental values; accepted writes are observable
    events. -/
structure DevReg where
  addr : Nat
  name : String
  read : Bool
  write : Bool
  deriving Repr, DecidableEq

/-- One loaded, read-only segment of the firmware image. -/
structure Segment where
  base : Nat
  bytes : List Nat
  exec : Bool
  deriving Repr, DecidableEq

structure Board where
  ramBase : Nat
  ramSize : Nat
  devices : List DevReg
  deriving Repr

structure Event where
  addr : Word
  val : Word
  deriving Repr, DecidableEq

structure Machine where
  core : Core
  ram : Word → BitVec 8

inductive Fault where
  | trap (e : Exc)
  | misaligned
  | unsupported (why : String)
  deriving Repr, DecidableEq

inductive Result where
  | ok (c : Core) (ram : Word → BitVec 8) (evs : List Event)
  | fault (f : Fault)

/-- An environment: the value of each nondeterministic choice in a step, in
    the order the step asks for them. -/
abbrev Oracle := Nat → Word

def Segment.byte? (s : Segment) (a : Nat) : Option Nat :=
  if s.base ≤ a then s.bytes[a - s.base]? else none

def romByte? (img : List Segment) (a : Nat) (fetch : Bool) : Option Nat :=
  match img.find? (fun s => s.base ≤ a && a < s.base + s.bytes.length && (!fetch || s.exec)) with
  | some s => s.byte? a
  | none => none

def romRead? (img : List Segment) (a n : Nat) (fetch : Bool) : Option Word :=
  let rec go : Nat → Option Nat
    | 0 => some 0
    | k+1 => do
      let b ← romByte? img (a + k) fetch
      let rest ← go k
      return rest + b * 256 ^ k
  (go n).map (BitVec.ofNat 32)

def Board.inRam (B : Board) (a : Word) (n : Nat) : Bool :=
  B.ramBase ≤ a.toNat && a.toNat + n ≤ B.ramBase + B.ramSize

/-- Little-endian bytes as a number. (Written arithmetically rather than with
    shifts and ORs so that frame and read-after-write facts are linear.) -/
def ramRead (ram : Word → BitVec 8) (a : Word) : Width → Word
  | .b => BitVec.ofNat 32 (ram a).toNat
  | .h => BitVec.ofNat 32 ((ram a).toNat + 256 * (ram (a+1)).toNat)
  | .w => BitVec.ofNat 32 ((ram a).toNat + 256 * (ram (a+1)).toNat +
            65536 * (ram (a+2)).toNat + 16777216 * (ram (a+3)).toNat)

def ramPut (ram : Word → BitVec 8) (a : Word) (b : BitVec 8) : Word → BitVec 8 :=
  fun x => if x = a then b else ram x

/-- Byte `k` of `v`. -/
def byteOf (v : Word) (k : Nat) : BitVec 8 := BitVec.ofNat 8 (v.toNat / 256 ^ k)

def ramWrite (ram : Word → BitVec 8) (a v : Word) : Width → (Word → BitVec 8)
  | .b => ramPut ram a (byteOf v 0)
  | .h => ramPut (ramPut ram a (byteOf v 0)) (a+1) (byteOf v 1)
  | .w => ramPut (ramPut (ramPut (ramPut ram a (byteOf v 0)) (a+1) (byteOf v 1))
            (a+2) (byteOf v 2)) (a+3) (byteOf v 3)

def Board.device? (B : Board) (a : Word) : Option DevReg :=
  B.devices.find? (fun d => d.addr == a.toNat)

/-- Interpret one effect tree. `i` counts the oracle values used so far. -/
def interp (B : Board) (img : List Segment) (o : Oracle) :
    Eff → (Word → BitVec 8) → Nat → List Event → Result
  | .done c, ram, _, evs => .ok c ram evs
  | .trap e, _, _, _ => .fault (.trap e)
  | .unsupported why, _, _, _ => .fault (.unsupported why)
  | .choose k, ram, i, evs => interp B img o (k ((o i).getLsbD 0)) ram (i+1) evs
  | .pick k, ram, i, evs => interp B img o (k (o i)) ram (i+1) evs
  | .load w a atomic k, ram, i, evs =>
    -- The E31 has no misaligned-access support: every misaligned load traps.
    if a.toNat % w.bytes ≠ 0 then .fault .misaligned
    else if B.inRam a w.bytes then interp B img o (k (ramRead ram a w)) ram i evs
    else if atomic then .fault (.unsupported "atomic access outside RAM")
    else match romRead? img a.toNat w.bytes false with
      | some v => interp B img o (k v) ram i evs
      | none => match B.device? a with
        | some d => if d.read && w = .w then interp B img o (k (o i)) ram (i+1) evs
                    else .fault (.unsupported "device read")
        | none => .fault (.unsupported "load from an unmodeled address")
  | .store w a v atomic k, ram, i, evs =>
    if a.toNat % w.bytes ≠ 0 then .fault .misaligned
    else if B.inRam a w.bytes then interp B img o k (ramWrite ram a v w) i evs
    else if atomic then .fault (.unsupported "atomic access outside RAM")
    else match B.device? a with
      | some d => if d.write && w = .w then interp B img o k ram i (evs ++ [⟨a, v⟩])
                  else .fault (.unsupported "device write")
      | none => .fault (.unsupported "store to an unmodeled address")

/-- Fetch from the executable image: a 16-bit parcel, and a second one when
    the low two bits say the instruction is 32 bits long. -/
def fetch (img : List Segment) (pc : Word) : Option (Word × Word) := do
  let lo ← romRead? img pc.toNat 2 true
  if lo &&& 3 ≠ 3 then return (lo, 2)
  let hi ← romRead? img (pc.toNat + 2) 2 true
  return ((hi <<< 16) ||| lo, 4)

def decode (bits len : Word) : Option Instr :=
  if len = 2 then decode16 bits else decode32 bits

def stepInstr (B : Board) (img : List Segment) (m : Machine) (o : Oracle) : Result :=
  if m.core.pc.getLsbD 0 then .fault (.trap .misalignedFetch) else
  match fetch img m.core.pc with
  | none => .fault (.unsupported "fetch outside the executable image")
  | some (bits, len) =>
    match decode bits len with
    | none => .fault (.trap .illegal)
    | some i => interp B img o (exec m.core len i) m.ram 0 []

/-- One machine transition: an instruction under some environment, or an
    enabled interrupt being taken. -/
inductive Step (B : Board) (img : List Segment) : Machine → Machine → List Event → Prop
  | instr {m c ram evs} (o : Oracle) :
      stepInstr B img m o = .ok c ram evs → Step B img m ⟨c, ram⟩ evs
  | irq {m c} (code : Nat) :
      irqEnabled m.core code = true → takeIrq m.core code = .done c →
      Step B img m ⟨c, m.ram⟩ []

/-- A machine that can leave the verified envelope in its next transition. -/
def Escapes (B : Board) (img : List Segment) (m : Machine) : Prop :=
  (∃ o f, stepInstr B img m o = .fault f) ∨
  (∃ code e, irqEnabled m.core code = true ∧ takeIrq m.core code = .trap e)

/-- Machines reachable from an initial set, with every event emitted on the
    way (oldest first). -/
inductive Reach (B : Board) (img : List Segment) (Init : Machine → Prop) :
    Machine → List Event → Prop
  | init {m} : Init m → Reach B img Init m []
  | step {m m' evs evs'} : Reach B img Init m evs → Step B img m m' evs' →
      Reach B img Init m' (evs ++ evs')

end E5R
