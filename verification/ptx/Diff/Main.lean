/-
The model's side of the differential test (scripts/check-ptx-difftest.sh).

`ptxdiff CASES` runs every case of CASES (written by difftest/gen.py) with the
definitions of `Ptx.Semantics` themselves: `tstep`, `action`, `exec`, `rd`
and `wr` are executed, not re-implemented. It prints the same lines as
`gpurun`: `result KERNEL OUTHEX`, or `fault KERNEL` if some thread faults or
a barrier diverges.

CTAs run one after another; inside a CTA every thread runs to its next
barrier, then the barrier is released. That is one of the executions the
model allows (`Step`). The test kernels are race-free and the values they
store do not depend on the order of atomics, so every execution ends in the
same memory; the GPU result is compared against that memory byte for byte.

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

/-- Where the difftest launch places the `.shared` variables: from offset 0,
in declaration order, each at the next multiple of its alignment (what
`e5r_ptx::interp::layout` does). The test kernels' outputs do not depend on
the placement. -/
def layout (K : Kernel) : (String → Addr) × Nat := Id.run do
  let mut pos := 0
  let mut f : String → Addr := fun _ => 0
  for v in K.shared do
    let a := max v.align 1
    pos := (pos + a - 1) / a * a
    let here := pos
    let g := f
    f := fun n => if n = v.name then BitVec.ofNat 64 here else g n
    pos := pos + v.size
  return (f, pos)

def bytesMem (b : ByteArray) (base : Addr) : Mem := fun a =>
  let i := (a - base).toNat
  if i < b.size then BitVec.ofNat 8 (b.get! i).toNat else 0

/-- Global memory: the input record buffer and the output buffer. -/
def globalMem (inb outb : ByteArray) : Mem := fun a =>
  let i := (a - inBase).toNat
  if i < inb.size then BitVec.ofNat 8 (inb.get! i).toNat else bytesMem outb outBase a

/-- Copy the bytes `[a, a + sz)` of `m` into `b` (based at `base`) where they
fall inside it. -/
def copyBack (m : Mem) (b : ByteArray) (base a : Addr) (sz : Size) : ByteArray := Id.run do
  let mut b := b
  for i in [0:sz.bytes] do
    let x := a + BitVec.ofNat 64 i
    let o := (x - base).toNat
    if o < b.size then b := b.set! o (UInt8.ofNat (m x).toNat)
  return b

/-- The memory a thread step touches, as byte arrays: the output buffer and
its CTA's shared memory (the input buffer is never written by the test
kernels; a store to it is outside `outb` and is dropped, which would show as
a difference from the GPU). -/
structure St where
  outb : ByteArray
  shb : ByteArray

instance : Inhabited TState := ⟨{ pc := 0, r := fun _ => 0, p := fun _ => false }⟩

inductive Ran where
  | wait (s : TState)
  | halted (s : TState)
  | fault

/-- Run one thread with `tstep` until it waits, halts or faults. After every
store or atomic, the bytes it wrote are read back from the model's memory
and copied into the arrays, so every later step of any thread sees them. -/
def runThread (K : Kernel) (L : Launch) (t : Tid) (inb : ByteArray) (shBase : Addr) :
    Nat → TState → St → Ran × St
  | 0, _, st => (.fault, st)
  | f + 1, s, st =>
    let c := L.ctx t
    let h : Heap := ⟨globalMem inb st.outb, bytesMem st.shb shBase⟩
    match tstep K (L.allocs K) c s h with
    | .ok s' h' =>
      let st' := match (action K c s).acc with
        | some ⟨.global, a, sz, k⟩ =>
          if k = .read then st else { st with outb := copyBack h'.g st.outb outBase a sz }
        | some ⟨.shared, a, sz, k⟩ =>
          if k = .read then st else { st with shb := copyBack h'.s st.shb shBase a sz }
        | none => st
      runThread K L t inb shBase f s' st'
    | .wait => (.wait s, st)
    | .halted => (.halted s, st)
    | .fault => (.fault, st)

/-- One CTA on the schedule of `e5r_ptx::interp::run_grid`: each thread in
`Launch.threads` order runs to its next barrier; when all wait at the same
`bar.sync` they are released (`Cfg.release`), and when all have halted the
CTA is done. Anything else is a fault or a diverged barrier. -/
def runCta (K : Kernel) (L : Launch) (cta : Dim3) (inb : ByteArray) (outb : ByteArray)
    (shSize : Nat) : Option ByteArray := Id.run do
  let tids := (dims L.block).map fun d => ({ ctaid := cta, tid := d } : Tid)
  let mut ts : Array TState := tids.toArray.map fun _ => { pc := 0, r := fun _ => 0, p := fun _ => false }
  let mut st : St := ⟨outb, ByteArray.mk (Array.replicate shSize 0)⟩
  for _ in [0:100000] do
    let mut waiting : List Nat := []
    let mut i := 0
    for t in tids do
      match runThread K L t inb 0 100000 ts[i]! st with
      | (.wait s, st') => ts := ts.set! i s; st := st'; waiting := waiting ++ [i]
      | (.halted s, st') => ts := ts.set! i s; st := st'
      | (.fault, _) => return none
      i := i + 1
    if waiting.isEmpty then return some st.outb
    let pc := ts[waiting.head!]!.pc
    if waiting.length != tids.length || waiting.any (fun j => ts[j]!.pc != pc) then return none
    ts := ts.map fun s => s.skip
  return none

def runCase (K : Kernel) (L : Launch) (inb : ByteArray) (outn : Nat) : Option ByteArray := Id.run do
  let mut outb := ByteArray.mk (Array.replicate outn 0xA5)
  let shSize := (layout K).2
  for cta in dims L.grid do
    match runCta K L cta inb outb shSize with
    | some o => outb := o
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
        alloc := [⟨inBase, inb.size⟩, ⟨outBase, outn.toNat!⟩]
        shared := (layout K).1 }
      match runCase K L inb outn.toNat! with
      | some out => IO.println s!"result {k} {hex out}"
      | none => IO.println s!"fault {k}"
    | [""] => pure ()
    | _ => IO.eprintln s!"ptxdiff: bad line"; return 2
  return 0
