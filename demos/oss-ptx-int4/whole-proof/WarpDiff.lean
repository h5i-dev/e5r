/- Executable semantic regression only. Uses Ptx.Warp.res/action, with
byte-array backing to avoid unbounded store closure chains. Tests do not prove
readonly safety or schedule independence. Generic initialized globals and
arbitrary-memory symbolic execution remain separate whole-proof obligations.
The test driver refuses writes outside its input/output/shared backing arrays.
-/
import Ptx.Logic.WarpSchedule
import WarpKernels
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

def localState (s : TState) (inb : ByteArray) (initialOut : ByteArray) (st : St) : Warp.State :=
  { cfg := { ts := fun _ => s
             mem := globalMem inb st.outb
             sh := fun _ => bytesMem st.shb 0
             ph := fun _ => 0 }
    initial := globalMem inb initialOut
    phase := fun _ => 0 }

def runThread (K : Kernel) (L : Launch) (t : Tid) (inb initialOut : ByteArray) :
    Nat → TState → St → Ran × St
  | 0, _, st => (.fault, st)
  | f + 1, s, st =>
    let c := localState s inb initialOut st
    match Warp.res K L c t with
    | .ok s' h' =>
      let st' := match (Warp.action K (L.ctx t) s).acc with
        | some ⟨.global, a, sz, k⟩ =>
          if k = .read then st else { st with outb := copyBack h'.g st.outb outBase a sz }
        | some ⟨.shared, a, sz, k⟩ =>
          if k = .read then st else { st with shb := copyBack h'.s st.shb 0 a sz }
        | none => st
      -- These fixtures have disjoint readonly input and writable output;
      -- enforce this test restriction instead of silently dropping writes.
      match (Warp.action K (L.ctx t) s).acc with
      | some ⟨.global, a, sz, k⟩ =>
        if k != .read && !Region.holds ⟨outBase, st.outb.size⟩ a sz.bytes then (.fault, st)
        else runThread K L t inb initialOut f s' st'
      | _ => runThread K L t inb initialOut f s' st'
    | .wait => (.wait s, st)
    | .halted => (.halted s, st)
    | .fault => (.fault, st)

def runCta (K : Kernel) (L : Launch) (cta : Dim3) (inb initialOut outb : ByteArray) (shSize : Nat) : Option ByteArray := Id.run do
  let tids := ((dims L.block).map fun d => ({ ctaid := cta, tid := d } : Tid)).toArray
  let mut ts : Array TState := tids.map fun _ => { pc := 0, r := fun _ => 0, p := fun _ => false }
  let mut st : St := ⟨outb, ByteArray.mk (Array.replicate shSize 0x5a)⟩
  let mut status : Array Nat := Array.replicate tids.size 0
  for _ in [0:1000] do
    for i in [0:tids.size] do
      match runThread K L tids[i]! inb initialOut 100000 ts[i]! st with
      | (.wait s, st') => ts := ts.set! i s; st := st'; status := status.set! i 1
      | (.halted s, st') => ts := ts.set! i s; st := st'; status := status.set! i 2
      | (.fault, _) => return none
    if status.all (· == 2) then return some st.outb
    let mut released := false
    for first in [0:(tids.size+31)/32] do
      let start := first*32
      let members := (List.range 32).map (start+·)
      if members.all (fun i => i < tids.size && status[i]! == 1 &&
          ts[i]!.pc == ts[start]!.pc && Warp.atWarp K ts[i]!) then
        for i in members do
          ts := ts.set! i ts[i]!.skip
          status := status.set! i 0
        released := true
    if !tids.isEmpty && (List.range tids.size).all (fun i => status[i]! == 1 &&
        ts[i]!.pc == ts[0]!.pc && !Warp.atWarp K ts[i]!) then
      ts := ts.map TState.skip
      released := true
    if !released then return none
  return none

def runCase (K : Kernel) (L : Launch) (inb : ByteArray) (outn : Nat) : Option ByteArray := Id.run do
  let initialOut := ByteArray.mk (Array.replicate outn 0xA5)
  let mut outb := initialOut
  for cta in dims L.grid do
    match runCta K L cta inb initialOut outb (layout K).2 with
    | some o => outb := o
    | none => return none
  return some outb

def kernels : Std.HashMap String Kernel :=
  WarpKernels.module.kernels.foldl (fun h k => h.insert k.name k) {}

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
