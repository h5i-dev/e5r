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

end Demo.Cobs
