/-
  Independent reader of a bare-metal ELF32 image as flash contents, for the
  image-fidelity theorem. Original e5r code, Apache-2.0.

  This is a second implementation of the rules in
  `crates/e5r-verify/src/flash.rs`, written against the ELF specification,
  not translated from the Rust. The theorem `loadFlash elfBytes = .ok
  (entry, segments)` makes the exported image a checked function of the
  original file bytes.
-/
import Theories.Platform

-- The image-fidelity theorem is decided by the kernel.
deriving instance DecidableEq for Except

namespace E5R.FlashElf
open E5R

structure Windows where
  flashBase : Nat
  flashSize : Nat
  ramBase : Nat
  ramSize : Nat

/-- Little-endian field of `width` bytes; every byte must be a byte. -/
def le (bs : List Nat) (off width : Nat) : Except String Nat := do
  if off + width > bs.length then throw s!"truncated at {off}"
  let field := (bs.drop off).take width
  if field.any (· ≥ 256) then throw "not a byte"
  return field.foldr (fun b acc => acc * 256 + b) 0

def inside (a n base size : Nat) : Bool := base ≤ a && a + n ≤ base + size

/-- The segments of program headers `i, i+1, ...`; `last` is the end address
    of the previous file-backed segment, for the ordering/overlap rule. -/
def headers (w : Windows) (bs : List Nat) (phoff : Nat) :
    Nat → Nat → Nat → Except String (List Segment)
  | 0, _, _ => pure []
  | n+1, i, last => do
    let at_ (k : Nat) := le bs (phoff + 32 * i + k) 4
    let kind ← at_ 0
    if kind = 0 || kind = 0x6474e551 || kind = 0x70000003 then
      return ← headers w bs phoff n (i+1) last
    if kind ≠ 1 then throw "unsupported program header"
    let file ← at_ 4
    let vaddr ← at_ 8
    let paddr ← at_ 12
    let filesz ← at_ 16
    let memsz ← at_ 20
    let flags ← at_ 24
    if flags > 7 || filesz > memsz || memsz = 0 then throw "bad PT_LOAD"
    let exec := flags % 2 = 1
    let write := flags / 2 % 2 = 1
    if exec && write then throw "writable and executable"
    if filesz = 0 then
      if !write || !inside vaddr memsz w.ramBase w.ramSize then throw "bss outside RAM"
      return ← headers w bs phoff n (i+1) last
    if file + filesz > bs.length then throw "file bytes outside the file"
    if !inside paddr filesz w.flashBase w.flashSize then throw "not in flash"
    if write then
      if !inside vaddr memsz w.ramBase w.ramSize then throw "data run address not in RAM"
    else if vaddr ≠ paddr || filesz ≠ memsz then throw "read-only segment not in place"
    if paddr < last then throw "overlapping or out of order"
    let rest ← headers w bs phoff n (i+1) (paddr + filesz)
    return ⟨paddr, (bs.drop file).take filesz, exec⟩ :: rest

def loadFlash (w : Windows) (bs : List Nat) : Except String (Nat × List Segment) := do
  if bs.length < 52 || bs.length > 1048576 then throw "size"
  if (← le bs 0 4) ≠ 0x464c457f || (← le bs 4 3) ≠ 0x010101 then throw "not ELF32 LE"
  if (← le bs 16 2) ≠ 2 || (← le bs 18 2) ≠ 243 || (← le bs 20 4) ≠ 1 then throw "not RISC-V ET_EXEC"
  let flags ← le bs 36 4
  if flags ≠ 0 && flags ≠ 1 then throw "e_flags"
  if (← le bs 40 2) ≠ 52 || (← le bs 42 2) ≠ 32 then throw "header sizes"
  let count ← le bs 44 2
  if count = 0 || count > 16 then throw "program header count"
  let segs ← headers w bs (← le bs 28 4) count 0 0
  if segs.foldl (fun n s => n + s.bytes.length) 0 > 262144 then throw "too much flash"
  let entry ← le bs 24 4
  if entry % 2 ≠ 0 || !segs.any (fun s => s.exec && inside entry 2 s.base s.bytes.length) then
    throw "entry"
  return (entry, segs)

end E5R.FlashElf
