/-
The model's side of the differential test (scripts/check-ptx-difftest.sh).

`ptxdiff CASES` runs every case of CASES (written by difftest/gen.py) with the
definitions of `Ptx.Semantics` themselves: `stepMem`, `action`, `exec`, `rd`
and `wr` are executed, not re-implemented. It prints the same lines as
`gpurun`: `result KERNEL OUTHEX`, or `fault KERNEL` if some thread faults.

Threads run one after another to completion, which is one of the
interleavings the model allows. The test kernels make every thread touch
only its own records, so every interleaving ends in the same memory; the GPU
result is compared against that memory byte for byte.

Initial registers are zero here. The test kernels write every register
before reading it, so the value does not matter; the theorems quantify over
all initial register contents.
-/
import Ptx.Semantics.SIMT
import Diff.Kernels
import Std.Data.HashMap

open Ptx

def inBase : Addr := 0x100000000
def outBase : Addr := 0x200000000

def memOf (inb outb : ByteArray) : Mem := fun a =>
  let i := (a - inBase).toNat
  if i < inb.size then BitVec.ofNat 8 (inb.get! i).toNat
  else
    let o := (a - outBase).toNat
    if o < outb.size then BitVec.ofNat 8 (outb.get! o).toNat else 0

def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else (c.toLower.toNat - 'a'.toNat) + 10

def unhex (s : String) : ByteArray := Id.run do
  let cs := s.toList.toArray
  let mut b := ByteArray.empty
  for i in [0:cs.size / 2] do
    b := b.push (UInt8.ofNat (hexDigit cs[2 * i]! * 16 + hexDigit cs[2 * i + 1]!))
  return b

def hex (b : ByteArray) : String := Id.run do
  let d := "0123456789abcdef".toList.toArray
  let mut s := ""
  for x in b.toList do
    s := (s.push d[x.toNat / 16]!).push d[x.toNat % 16]!
  return s

/-- Copy the bytes `[a, a + sz)` of the model memory `m` into the output
buffer, if they are inside it. Only the bytes a thread stored are copied
back, which keeps each thread's memory a short chain of `wr` closures; the
values themselves are read from the model's memory. -/
def copyBack (m : Mem) (outb : ByteArray) (a : Addr) (sz : Size) : ByteArray := Id.run do
  let mut b := outb
  for i in [0:sz.bytes] do
    let x := a + BitVec.ofNat 64 i
    let o := (x - outBase).toNat
    if o < b.size then b := b.set! o (UInt8.ofNat (m x).toNat)
  return b

/-- Run one thread to `ret`/`exit` from the given memory; returns the final
memory and the stores it made. -/
def runThread (K : Kernel) (L : Launch) (t : Tid) (m : Mem) (fuel : Nat) :
    Option (Mem × List (Addr × Size)) :=
  go fuel { pc := 0, r := fun _ => 0, p := fun _ => false } m []
where
  go : Nat → TState → Mem → List (Addr × Size) → Option (Mem × List (Addr × Size))
    | 0, _, _, _ => none
    | f + 1, s, m, ws =>
      let ws := match action K (L.ctx t) s with
        | .store a sz _ _ => (a, sz) :: ws
        | _ => ws
      match stepMem K L.alloc (L.ctx t) s m with
      | .ok s' m' => go f s' m' ws
      | .halted => some (m, ws)
      | .fault => none

def runCase (K : Kernel) (L : Launch) (inb : ByteArray) (outn : Nat) : Option ByteArray := Id.run do
  let mut outb := ByteArray.mk (Array.replicate outn 0xA5)
  for t in L.threads do
    match runThread K L t (memOf inb outb) 100000 with
    | some (m, ws) =>
      -- oldest store first, so a later store to the same bytes wins
      for (a, sz) in ws.reverse do
        outb := copyBack m outb a sz
    | none => return none
  return some outb

def kernels : Std.HashMap String Kernel :=
  Diff.Kernels.module.kernels.foldl (fun h k => h.insert k.name k) {}

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: ptxdiff CASES"; return 2
  let text ← IO.FS.readFile path
  for line in text.splitOn "\n" do
    match line.splitOn " " with
    | ["case", k, gx, gy, gz, bx, by_, bz, s, inhex, outn] =>
      let some K := kernels[k]? | IO.eprintln s!"ptxdiff: no kernel {k}"; return 2
      let n32 (x : String) : BitVec 32 := BitVec.ofNat 32 x.toNat!
      let inb := if inhex == "00" then ByteArray.empty else unhex inhex
      let L : Launch := {
        grid := ⟨n32 gx, n32 gy, n32 gz⟩
        block := ⟨n32 bx, n32 by_, n32 bz⟩
        params := fun p =>
          if p = k ++ "_in" then inBase else if p = k ++ "_out" then outBase
          else if p = k ++ "_s" then (n32 s).setWidth 64 else 0
        alloc := [⟨inBase, inb.size⟩, ⟨outBase, outn.toNat!⟩] }
      match runCase K L inb outn.toNat! with
      | some out => IO.println s!"result {k} {hex out}"
      | none => IO.println s!"fault {k}"
    | [""] => pure ()
    | _ => IO.eprintln s!"ptxdiff: bad line"; return 2
  return 0
