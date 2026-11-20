import Demo.CobsSpec
import Demo.SumSpec
import Examples.Sum
import Examples.Hello

/-
For scripts/core/check-spec-references.py: evaluate the computable parts of the
example specifications on inputs from stdin, so that they can be compared
with independent reference implementations (in Python). Not used by any
proof; what it runs is the specification's own definitions.

One query per line, one answer per line:

  sum W...           Examples.Sum.sumW and Demo.Sum.sumW of the words (decimal), both
  cobs HEX           Demo.Cobs.report of the bytes: TAG A B|- HEX
  written FD EV...   NoCompiler.writtenTo FD: EV is w:FD:HEX, r:FD:HEX or x:CODE; HEX or none
  message            Examples.Hello.message: HEX
-/
open NoCompiler

def hexOf (bs : List Byte) : String :=
  String.join (bs.map fun b =>
    let n := b.toNat
    let d := fun k => if k < 10 then Char.ofNat (48 + k) else Char.ofNat (87 + k)
    String.ofList [d (n / 16), d (n % 16)])

def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87

def bytesOf (s : String) : List Byte :=
  let cs := s.toList
  (List.range (cs.length / 2)).map fun i =>
    BitVec.ofNat 8 (16 * hexVal (cs.getD (2 * i) '0') + hexVal (cs.getD (2 * i + 1) '0'))

def event (s : String) : Option Event :=
  match s.splitOn ":" with
  | ["w", fd, h] => fd.toNat?.map fun n => .write (BitVec.ofNat 64 n) (bytesOf h)
  | ["r", fd, h] => fd.toNat?.map fun n => .read (BitVec.ofNat 64 n) (bytesOf h)
  | ["x", c] => c.toNat?.map fun n => .exit (BitVec.ofNat 64 n)
  | _ => none

def answer (line : String) : String :=
  match line.splitOn " " |>.filter (· ≠ "") with
  | "sum" :: ws =>
    let xs := ws.map fun w => BitVec.ofNat 64 w.toNat!
    s!"{(Examples.Sum.sumW xs).toNat} {(Demo.Sum.sumW xs).toNat}"
  | ["cobs"] | ["cobs", _] =>
    let buf := bytesOf ((line.splitOn " ").getD 1 "")
    let ((t, a, b), out) := Demo.Cobs.report buf
    let bs := match b with | some b => toString b | none => "-"
    s!"{t} {a} {bs} {hexOf out}"
  | "written" :: fd :: evs =>
    match evs.mapM event with
    | none => "bad"
    | some es => match writtenTo (BitVec.ofNat 64 fd.toNat!) es with
      | some bs => hexOf bs
      | none => "none"
  | ["message"] => hexOf Examples.Hello.message
  | _ => "bad"

partial def loop (h : IO.FS.Stream) (o : IO.FS.Stream) : IO Unit := do
  let l ← h.getLine
  if l.isEmpty then return
  o.putStrLn (answer (String.ofList (l.toList.reverse.dropWhile Char.isWhitespace).reverse))
  loop h o

def main : IO UInt32 := do
  loop (← IO.getStdin) (← IO.getStdout)
  return 0
