/-
  Audit (not a proof): run the emitted memmove of the pinned RMK image in the
  model on concrete inputs and compare the result with memmove's meaning.

  Original e5r code, Apache-2.0. Independent of the proofs under
  Projects/rmk: it uses only the model (`stepInstr`), the board, and the
  checker's reader applied to the runner-generated packed file. Execution
  evidence about chosen inputs; it proves nothing for other inputs.

  For each case: pc = 0x80020c1e (the trampoline), a0 = dst, a1 = src,
  a2 = n, sp, ra = a fixed even return address, interrupts off, every other
  register 0; RAM is a non-zero pattern, so every write that changes a byte
  is visible. The run stops at ra, on a fault, or after 4000 steps. Reported:
  bytes of the destination that differ from memmove's result, and bytes
  outside the destination that changed, split into the three save slots
  [sp-12, sp) (all PostB excludes) and the rest.
-/
import Theories.Chunk
import Theories.Board.QemuVirtRv32
import Projects.rmk.Elf
open E5R

def image : RamElf.Image := RamElf.imageOf 0x80000000 0x1000000 E5R.Rmk.Image.elf
def img : List Segment := chunkImg 256 image.ro
def B : Board := QemuVirtRv32.board image.rwBase

def pat (a : Word) : BitVec 8 := BitVec.ofNat 8 ((a.toNat * 7 + 3) % 251 + 1)

def RA : Word := 0x80000100

def start (dst src n sp : Nat) : Machine :=
  { core := { pc := 0x80020c1e,
              x := fun r => if r.val = 10 then BitVec.ofNat 32 dst else if r.val = 11 then BitVec.ofNat 32 src
                else if r.val = 12 then BitVec.ofNat 32 n else if r.val = 2 then BitVec.ofNat 32 sp
                else if r.val = 1 then RA else 0,
              mie_ := false, mpie := false, mpp := 3, mieReg := 0, mtvec := 0, mepc := 0, mcause := 0,
              mscratch := 0, resv := false },
    ram := pat }

/-- `bd` is the board: normally `B`; the read-bound cases move model RAM's
    start or end to the source or destination, so any access outside faults. -/
def run (bd : Board) : Nat → Machine → Nat → Except String (Machine × Nat)
  | 0, _, k => .error s!"no return after {k} steps"
  | fuel+1, m, k =>
    if m.core.pc = RA then .ok (m, k) else
    match stepInstr bd img m (fun _ => 0) with
    | .ok c ram _ => run bd fuel ⟨c, ram⟩ (k + 1)
    | .fault f => .error s!"fault at pc {m.core.pc} after {k} steps: {repr f}"

def moved (dst src n x : Nat) : BitVec 8 :=
  if dst ≤ x ∧ x < dst + n then pat (BitVec.ofNat 32 (src + (x - dst))) else pat (BitVec.ofNat 32 x)

def case_ (name : String) (dst src n sp : Nat) (bd : Board := B) : IO Bool := do
  match run bd 4000 (start dst src n sp) 0 with
  | .error e => IO.println s!"{name}: {e}"; return false
  | .ok (m, k) =>
    -- Two windows: the destination ±16 bytes and the stack from sp-64 to sp+16.
    let window := (List.range (n + 32)).map (dst - 16 + ·) ++ (List.range 80).map (sp - 64 + ·)
    let bad := (window.eraseDups).filter fun x => m.ram (BitVec.ofNat 32 x) ≠ moved dst src n x
    let inDst := bad.filter fun x => dst ≤ x ∧ x < dst + n
    let slots := bad.filter fun x => sp - 12 ≤ x ∧ x < sp ∧ ¬ (dst ≤ x ∧ x < dst + n)
    let other := bad.filter fun x => ¬ (sp - 12 ≤ x ∧ x < sp) ∧ ¬ (dst ≤ x ∧ x < dst + n)
    let rel := other.map fun x => Int.ofNat x - Int.ofNat sp
    let regsOk := (List.finRange 32).all fun r =>
      [5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31].contains r.val ||
        m.core.get r = (start dst src n sp).core.get r
    IO.println s!"{name}: returned after {k} steps; dst bytes wrong: {inDst.length}; save-slot bytes changed: {slots.length}; other bytes changed (offset from caller sp): {rel}; ABI registers preserved: {regsOk}"
    return inDst.isEmpty

def main : IO UInt32 := do
  IO.println s!"rwBase {image.rwBase}, reader accepts: {RamElf.accepts 0x80000000 0x1000000 E5R.Rmk.Image.elf}"
  let b := 0x80100000
  let sp := 0x80800000
  let mut ok := true
  for (name, dst, src, n, s) in [
      ("small n=10 forward (contractB)", b + 0x100, b + 0x400, 10, sp),
      ("aligned n=40 forward, src≡dst (contractB)", b + 0x100, b + 0x400, 40, sp),
      ("misaligned o=1 n=40 forward", b + 0x100, b + 0x401, 40, sp),
      ("misaligned o=2 n=40 forward", b + 0x100, b + 0x402, 40, sp),
      ("misaligned o=3 n=40 forward", b + 0x101, b + 0x400, 40, sp),
      ("misaligned o=1 n=40 forward, overlap dst = src-1", b + 0x100, b + 0x101, 40, sp),
      ("backward n=40 overlap dst = src+5", b + 0x105, b + 0x100, 40, sp),
      ("backward n=40 overlap dst = src+4", b + 0x104, b + 0x100, 40, sp),
      ("misaligned o=1, sp = rwBase+12 (PreB's Slots lower bound)", b + 0x100, b + 0x401, 40, 0x80029bc8 + 12),
      ("aligned n=40, sp = rwBase+12", b + 0x100, b + 0x400, 40, 0x80029bc8 + 12),
      ("aligned n=40 ending at the last RAM byte", 0x81000000 - 40, b + 0x400, 40, sp)] do
    let r ← case_ name dst src n s
    ok := ok && r
  -- Destination or source over the stack temporaries, both allowed by PreB's dstSep/srcSep
  -- (they only keep dst/src off [sp-12, sp)): dst/src = [sp-40, sp-20), n = 20, misaligned.
  for (name, dst, src, n) in [
      ("dst over the stack temps (PreB dstSep holds)", sp - 40, b + 0x401, 20),
      ("src over the stack temps (PreB srcSep holds)", b + 0x100, sp - 39, 20)] do
    let r ← case_ name dst src n sp
    ok := ok && r
  -- Read and write bounds: model RAM is [lo, 0x81000000); the image ends far below, so any
  -- access below lo or at/after 0x81000000 faults ("unmodeled address").
  let mut bounds : List (String × Nat × Nat × Nat × Nat × Nat) := []
  for o in [1, 2, 3] do
    bounds := bounds ++ [
      (s!"bounds o={o}: source starts at RAM start", b + 0x100, b + o, 41, sp, b + o),
      (s!"bounds o={o}: source ends at RAM end", b + 0x100, 0x81000000 - 41, 41, sp, b),
      (s!"bounds o={o}: destination starts at RAM start", b + o, b + 0x400, 41, sp, b + o),
      (s!"bounds o={o}: destination ends at RAM end", 0x81000000 - 41 - o, b + 0x400, 41 + o, sp, b)]
  for (name, dst, src, n, s, lo) in bounds do
    let r ← case_ name dst src n s (QemuVirtRv32.board lo)
    ok := ok && r
  return if ok then 0 else 1
