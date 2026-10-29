/-
  Audit regression matrix (tests, not proofs): the emitted memmove of the
  pinned RMK image executed in the model over a bounded input matrix.

  Original e5r code, Apache-2.0. Uses only the model (`stepInstr`), the
  QEMU-virt board and the checker's reader applied to the runner-generated
  packed file; independent of the proofs under Projects/rmk.

  usage: memmove_matrix main SHARD SHARDS      (the length/residue/placement matrix)
         memmove_matrix bounds                 (RAM-edge, frame and sp-boundary cases)

  For every case the machine starts at the trampoline 0x80020c1e with a0 =
  dst, a1 = src, a2 = n, sp, ra = 0x80000100, interrupts off, other
  registers 0, and RAM a non-zero pattern (the snapshot). The run must return
  to ra within 20000 steps. Checked against the snapshot, byte by byte over
  [dst-16, dst+n+16), [src-16, src+n+16) and [sp-64, sp+16):
    * every destination byte equals memmove of the snapshot;
    * every other changed byte lies in the frame [sp-48, sp); the changed
      frame offsets are recorded per case;
    * every register the ABI preserves (all but t0-t6, a1-a7) is unchanged.
  A case line is printed for every failure (all parameters, so it can be
  rerun), and a summary per path class (n<16 / n>=16, src≡dst mod 4 or not,
  placement) with the set of changed frame offsets.

  Speed: image segments are tried memmove's code first. That is the same
  lookup only because the segments are pairwise disjoint, which is checked at
  start (the run refuses otherwise).
-/
import Std.Data.HashMap
import Theories.Chunk
import Theories.Board.QemuVirtRv32
import Projects.rmk.Elf
open E5R

def image : RamElf.Image := RamElf.imageOf 0x80000000 0x1000000 E5R.Rmk.Image.elf
def img0 : List Segment := chunkImg 256 image.ro
def img : List Segment :=
  let (a, b) := img0.partition fun s => 0x80020c00 ≤ s.base ∧ s.base < 0x80021100
  a ++ b
def disjoint : Bool :=
  let l := (img0.map fun s => (s.base, s.base + s.bytes.length)).mergeSort (·.1 ≤ ·.1)
  (l.zip (l.drop 1)).all fun (x, y) => x.2 ≤ y.1
def B : Board := QemuVirtRv32.board image.rwBase
def RA : Word := 0x80000100

def pat (a : Word) : BitVec 8 := BitVec.ofNat 8 ((a.toNat * 7 + 3) % 251 + 1)

def start (dst src n sp : Nat) : Machine :=
  { core := { pc := 0x80020c1e,
              x := fun r => if r.val = 10 then BitVec.ofNat 32 dst else if r.val = 11 then BitVec.ofNat 32 src
                else if r.val = 12 then BitVec.ofNat 32 n else if r.val = 2 then BitVec.ofNat 32 sp
                else if r.val = 1 then RA else 0,
              mie_ := false, mpie := false, mpp := 3, mieReg := 0, mtvec := 0, mepc := 0, mcause := 0,
              mscratch := 0, resv := false },
    ram := pat }

def run (bd : Board) : Nat → Machine → Nat → Except String (Machine × Nat)
  | 0, _, k => .error s!"no return after {k} steps"
  | fuel+1, m, k =>
    if m.core.pc = RA then .ok (m, k) else
    match stepInstr bd img m (fun _ => 0) with
    | .ok c ram _ => run bd fuel ⟨c, ram⟩ (k + 1)
    | .fault f => .error s!"fault at pc {m.core.pc.toNat} after {k} steps: {repr f}"

def moved (dst src n x : Nat) : BitVec 8 :=
  if dst ≤ x ∧ x < dst + n then pat (BitVec.ofNat 32 (src + (x - dst))) else pat (BitVec.ofNat 32 x)

structure Out where
  ok : Bool
  steps : Nat
  frame : List Int   -- changed bytes in [sp-48, sp), as offsets from sp
  why : String

def check (bd : Board) (dst src n sp : Nat) (refSrc : Nat := src) (spAt : Nat := sp) : Out :=
  match run bd 20000 (start dst src n sp) 0 with
  | .error e => ⟨false, 0, [], e⟩
  | .ok (m, k) =>
    let win := (List.range (n + 32)).map (dst - 16 + ·) ++ (List.range (n + 32)).map (src - 16 + ·) ++
      (List.range 80).map (sp - 64 + ·)
    let bad := win.eraseDups.filter fun x => m.ram (BitVec.ofNat 32 x) ≠ moved dst refSrc n x
    let inDst := bad.filter fun x => dst ≤ x ∧ x < dst + n
    let inFrame := bad.filter fun x => sp - 48 ≤ x ∧ x < sp ∧ ¬ (dst ≤ x ∧ x < dst + n)
    let stray := bad.filter fun x => ¬ (dst ≤ x ∧ x < dst + n) ∧ ¬ (sp - 48 ≤ x ∧ x < sp)
    let s0 := (start dst src n spAt).core
    let regs := (List.finRange 32).filter fun r =>
      !([5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31].contains r.val) && m.core.get r ≠ s0.get r
    let frame := (inFrame.map fun x => Int.ofNat x - Int.ofNat sp).mergeSort (· ≤ ·)
    let ok := inDst.isEmpty && stray.isEmpty && regs.isEmpty
    ⟨ok, k, frame, if ok then "" else
      s!"dst wrong {inDst.length}, stray changes {stray.map fun x => Int.ofNat x - Int.ofNat sp}, regs {regs.map (·.val)}"⟩

/-- Placements: (name, dst) for a source at `src`, length `n`, destination residue `rd`. -/
def placements (src n rd : Nat) : List (String × Nat) :=
  let rs := src % 4
  let d0 := (rs + 4 - rd) % 4          -- dst = src - d needs d ≡ rs - rd (mod 4)
  let dFwd1 := if d0 = 0 then 4 else d0
  let dFwd2 := if n ≤ 1 then dFwd1 else dFwd1 + 4 * ((n - 1 - dFwd1) / 4)
  let e0 := (rd + 4 - rs) % 4          -- dst = src + e needs e ≡ rd - rs (mod 4)
  let eB1 := if e0 = 0 then 4 else e0
  let eB2 := if n ≤ 1 then eB1 else eB1 + 4 * ((n - 1 - eB1) / 4)
  [("disjoint-below", 0x80100000 + rd), ("disjoint-above", 0x80300000 + rd)] ++
  (if rs = rd then [("same", src)] else []) ++
  (if dFwd1 < n then [("fwd-overlap-near", src - dFwd1)] else []) ++
  (if dFwd2 < n ∧ dFwd2 ≠ dFwd1 then [("fwd-overlap-far", src - dFwd2)] else []) ++
  (if eB1 < n then [("bwd-overlap-near", src + eB1)] else []) ++
  (if eB2 < n ∧ eB2 ≠ eB1 then [("bwd-overlap-far", src + eB2)] else [])

def SP : Nat := 0x80800000

def mainMatrix (shard shards : Nat) : IO UInt32 := do
  let mut runs := 0
  let mut fails := 0
  let mut steps := 0
  let mut classes : Std.HashMap String (Nat × List (List Int)) := {}
  for n in List.range 489 do
    if n % shards ≠ shard then continue
    for rs in List.range 4 do
      for rd in List.range 4 do
        let src := 0x80200000 + rs
        for (pl, dst) in placements src n rd do
          let o := check B dst src n SP
          runs := runs + 1
          steps := steps + o.steps
          let cls := s!"{if n < 16 then "n<16" else "n>=16"} {if rs = rd then "src≡dst" else "src≢dst"} {pl}"
          let (c, fs) := classes.getD cls (0, [])
          classes := classes.insert cls (c + 1, if fs.contains o.frame then fs else o.frame :: fs)
          if !o.ok then
            fails := fails + 1
            IO.println s!"FAIL main n={n} src={src} dst={dst} sp={SP} ({cls}): {o.why}"
  for (cls, (c, fs)) in classes.toList.mergeSort (·.1 ≤ ·.1) do
    IO.println s!"class [{cls}] {c} runs; changed frame offsets (distinct sets): {fs.reverse}"
  IO.println s!"shard {shard}/{shards}: {runs} runs, {fails} failures, {steps} model steps"
  return if fails = 0 then 0 else 1

/-- The highest address `a` with `a % 4 = r` and `a + n ≤ lim`. -/
def below (lim n r : Nat) : Nat := let s := lim - n; s - (s + 4 - r) % 4

def mainBounds : IO UInt32 := do
  let ns := [0, 1, 3, 4, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 255, 256, 487, 488]
  let mut runs := 0
  let mut fails := 0
  let mut tally : Std.HashMap String Nat := {}
  let report (name : String) (bd : Board) (dst src n sp : Nat) (expectFault : Bool) : IO Bool := do
    let o := check bd dst src n sp
    let faulted := o.why.startsWith "fault"
    let good := if expectFault then faulted else o.ok
    unless good do
      IO.println s!"FAIL bounds {name} n={n} src={src} dst={dst} sp={sp} lo={bd.ramBase}: {if o.why = "" then "no fault" else o.why}"
    return good
  for n in ns do
    for rs in List.range 4 do
      for rd in List.range 4 do
        -- model RAM cut at the source's first byte / after its last byte, the same for the destination
        let cases : List (String × Board × Nat × Nat) := [
          ("src at RAM start", QemuVirtRv32.board (0x80200000 + rs), 0x80300000 + rd, 0x80200000 + rs),
          ("src ends at RAM end (last byte within 3 of it)", B, 0x80300000 + rd, below 0x81000000 n rs),
          ("dst at RAM start", QemuVirtRv32.board (0x80200000 + rd), 0x80200000 + rd, 0x80300000 + rs),
          ("dst ends at RAM end (last byte within 3 of it)", B, below 0x81000000 n rd, 0x80300000 + rs),
          ("dst ends just below the frame", B, below (SP - 48) n rd, 0x80300000 + rs),
          ("src ends just below the frame", B, 0x80300000 + rd, below (SP - 48) n rs),
          ("dst starts at sp", B, SP + rd, 0x80300000 + rs)]
        for (name, bd, dst, src) in cases do
          let g ← report name bd dst src n SP false
          runs := runs + 1
          tally := tally.insert name (tally.getD name 0 + 1)
          unless g do fails := fails + 1
  -- The lowest stack pointer each path tolerates, with the frame's 34 used bytes (M1/M2):
  -- misaligned forward needs sp-34 >= rwBase, so sp = rwBase+36 runs and rwBase+32 faults.
  let rw := image.rwBase
  for (name, sp, src, dst, n, fault) in [
      ("misaligned fwd, sp = rwBase+36", rw + 36, 0x80200001, 0x80100000, 40, false),
      ("misaligned fwd, sp = rwBase+32", rw + 32, 0x80200001, 0x80100000, 40, true),
      ("misaligned bwd, sp = rwBase+24", rw + 24, 0x80200000, 0x80200005, 40, false),
      ("misaligned bwd, sp = rwBase+20", rw + 20, 0x80200000, 0x80200005, 40, true),
      ("aligned fwd, sp = rwBase+12", rw + 12, 0x80200000, 0x80100000, 40, false),
      ("small, sp = rwBase+12", rw + 12, 0x80200001, 0x80100000, 10, false)] do
    let g ← report name B dst src n sp fault
    runs := runs + 1
    tally := tally.insert name 1
    unless g do fails := fails + 1
  for (k, v) in tally.toList.mergeSort (·.1 ≤ ·.1) do IO.println s!"bounds [{k}] {v} runs"
  IO.println s!"bounds: {runs} runs, {fails} failures"
  return if fails = 0 then 0 else 1

/-- Controls: each case must be reported as a failure, or the checker is blind. -/
def mainControls : IO UInt32 := do
  let mut blind := 0
  for (name, o) in [
      ("reference shifted by one source byte (misaligned, n=40)",
        check B 0x80100000 0x80200001 40 SP (refSrc := 0x80200002)),
      ("reference shifted by one source byte (aligned, n=200)",
        check B 0x80100000 0x80200000 200 SP (refSrc := 0x80200001)),
      ("M3: dst over the stack temporaries (misaligned, n=20)", check B (SP - 40) 0x80200401 20 SP),
      ("M3: src over the stack temporaries (misaligned, n=20)", check B 0x80100000 (SP - 39) 20 SP),
      ("sp expected 4 lower at return (register check)", check B 0x80100000 0x80200001 40 SP (spAt := SP - 4)),
      ("M2: misaligned with sp = rwBase+12", check B 0x80100000 0x80200001 40 (image.rwBase + 12))] do
    IO.println s!"control {name}: {if o.ok then "NOT DETECTED" else "detected: " ++ o.why}"
    if o.ok then blind := blind + 1
  return if blind = 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  unless disjoint do IO.eprintln "image segments overlap: reordering would change lookups"; return 2
  unless RamElf.accepts 0x80000000 0x1000000 E5R.Rmk.Image.elf do IO.eprintln "reader refuses the ELF"; return 2
  match args with
  | ["main", s, k] => mainMatrix s.toNat! k.toNat!
  | ["bounds"] => mainBounds
  | ["controls"] => mainControls
  | _ => IO.eprintln "usage: memmove_matrix main SHARD SHARDS | bounds"; return 2
