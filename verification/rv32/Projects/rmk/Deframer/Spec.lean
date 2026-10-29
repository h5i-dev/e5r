/-
  R2: the host-input property for RMK's Rynk deframer, as Lean statements.
  Original e5r code, Apache-2.0.

  STATUS: SPECIFICATION ONLY. Nothing here is proved; every definition below is a proof
  obligation, and the constants marked CANDIDATE are read from the disassembly of the pinned ELF
  (f39d833f..., review/rmk/deframer-contracts.md on the review branch) and must be confirmed by
  the proof that uses them. No theorem in this file claims safety. Proved elsewhere so far:
  `Deframer/TailNoCopy.lean` (`tail` with consumed = 0 meets `TailPost`); `CallEnv.selfAl/spAl`
  and `CopyEnv.spAl` were added for it (ABI alignment; the model faults misaligned word access).

  The property (R2), in words: whatever bytes a host sends on the UART, the deframer's state
  invariant `consumed ≤ filled ≤ len` holds whenever its methods return, and no method reaches
  the slice-index panic (`core::slice::index::slice_index_fail`, which ends in panic-halt's
  infinite loop: the keyboard stops answering). `LockConfig { insecure: true }` makes every
  command authorized, so an authorization property would be vacuous for this example and is not
  claimed.

  Function contracts have the shape of E5R.Rmk.Memmove.contract: from a machine meeting `Pre`,
  a quiet run (no interrupt enabled at any machine, every step deterministic, no event, no fault)
  reaches a machine meeting `Post`. Because each step of such a run is the only behaviour of the
  model there, a returning run also shows the panic is not reached on the way.
-/
import Projects.rmk.MemmoveContract

namespace E5R.Rmk.Deframer
open E5R E5R.Rmk

-- The runner's one image module (Projects.rmk.Elf, as the memmove job uses), so these statements
-- compose with E5R.Rmk.Memmove.contractB.
abbrev B : Board := E5R.Rmk.B
abbrev img : List Segment := E5R.Rmk.img

/-! ## Constants read from the ELF (CANDIDATE until a proof uses them) -/

def tailPc : Nat := 0x8001d576
def parkPc : Nat := 0x8001d388
def unparkPc : Nat := 0x8001d3f2
def nextPc : Nat := 0x8001d43a
/-- `core::slice::index::slice_index_fail`: every bounds failure of the deframer calls it. -/
def panicPc : Nat := 0x8001fafc
/-- `core::panicking::panic_bounds_check`: the COBS decoder's two bounds checks call it. -/
def boundsPanicPc : Nat := 0x8001f83a
/-- `rust_begin_unwind`: every panic path ends here (panic-halt). -/
def unwindPc : Nat := 0x8001e148

/-- The firmware's buffer length (`RYNK_BUFFER_SIZE`; `li a2, 0x1e8` at every call site). -/
def bufLen : Nat := 488
/-- `compiler_builtins::mem::memmove`'s whole frame (`addi sp, sp, -0x30` at 0x80020d9e). The
    proved small/aligned paths only write its three save slots (12 bytes, Memmove.Slots); the
    misaligned paths may use the rest, so a caller must allow all 48 bytes. -/
def memmoveFrame : Nat := 0x30

/-- `tail`'s stack frame (`addi sp, sp, -0x20`; saves ra, s0-s3 at sp+0x1c..0xc) plus memmove's
    frame below it: every stack byte a `tail` call writes lies in `[sp - tailStack, sp)`. Read from
    the bytes at 0x8001d576 (corrected from 0x20 + 12, which only covered memmove's proved paths). -/
def tailStack : Nat := 0x20 + memmoveFrame

/-! ## The deframer in memory: `consumed @ +0`, `filled @ +4`, `discarding @ +8` -/

def word (ram : Word → BitVec 8) (a : Word) : Nat := (ramRead ram a .w).toNat
def consumed (ram : Word → BitVec 8) (p : Word) : Nat := word ram p
def filled (ram : Word → BitVec 8) (p : Word) : Nat := word ram (p + 4)

/-- Byte `x` is outside the deframer at `p` (12 bytes), the buffer `[buf, buf+len)` and the
    `frame` stack bytes below `sp`: a call's RAM writes are confined to those. -/
def Outside (p buf : Word) (len : Nat) (sp : Word) (frame : Nat) (x : Word) : Prop :=
  ¬ (p.toNat ≤ x.toNat ∧ x.toNat < p.toNat + 12) ∧
  ¬ (buf.toNat ≤ x.toNat ∧ x.toNat < buf.toNat + len) ∧
  ¬ (sp.toNat - frame ≤ x.toNat ∧ x.toNat < sp.toNat)

/-- The RAM frame of a call from `m₀` (a0 = deframer, a1 = buffer, a2 = len). -/
def KeepsRam (frame : Nat) (m₀ m : Machine) : Prop :=
  ∀ x, Outside (m₀.core.get 10) (m₀.core.get 11) (m₀.core.get 12).toNat (m₀.core.get 2) frame x →
    m.ram x = m₀.ram x

/-- The state invariant. -/
def Inv (ram : Word → BitVec 8) (p : Word) (len : Nat) : Prop :=
  consumed ram p ≤ filled ram p ∧ filled ram p ≤ len

/-! ## `Deframer::tail` (first contract to prove) -/

/-- Calling environment of `tail(&mut self, buf: &mut [u8]) -> &mut [u8]` (ABI read from the
    bytes: a0 = &mut Deframer, (a1, a2) = buf; returns (a0, a1) = the free tail): the deframer and the
    buffer in model RAM and disjoint; the `frame` stack bytes below sp in RAM and disjoint from both;
    a quiet machine; an even return address. Use `frame = tailStack`. -/
structure CallEnv (entry frame : Nat) (m : Machine) : Prop where
  pc : m.core.pc = BitVec.ofNat 32 entry
  quiet : Quiet m.core
  self : B.inRam (m.core.get 10) 12 = true
  buf : B.inRam (m.core.get 11) (m.core.get 12).toNat = true
  len : (m.core.get 12).toNat = bufLen
  sep : (m.core.get 10).toNat + 12 ≤ (m.core.get 11).toNat ∨
    (m.core.get 11).toNat + (m.core.get 12).toNat ≤ (m.core.get 10).toNat
  stack : B.inRam (m.core.get 2 - BitVec.ofNat 32 frame) frame = true
  stackSep : (m.core.get 10).toNat + 12 ≤ (m.core.get 2).toNat - frame ∧
    (m.core.get 11).toNat + (m.core.get 12).toNat ≤ (m.core.get 2).toNat - frame
  ra : (m.core.get 1).getLsbD 0 = false
  /-- The deframer (three `usize` fields) and the stack pointer are word-aligned (Rust layout and
      the RISC-V psABI; added when the first proof step needed it: the model faults a misaligned
      word access). -/
  selfAl : (m.core.get 10).toNat % 4 = 0
  spAl : (m.core.get 2).toNat % 4 = 0

abbrev TailEnv (frame : Nat) (m : Machine) : Prop := CallEnv tailPc frame m

/-- The precondition: the environment and the invariant. -/
def TailPre (frame : Nat) (m : Machine) : Prop :=
  TailEnv frame m ∧ Inv m.ram (m.core.get 10) (m.core.get 12).toNat

/-- `tail`'s result: the pending bytes `buf[consumed..filled)` moved to the front (when
    `consumed > 0`), consumed := 0, filled := filled - consumed; returns `(buf + filled', len -
    filled')`; callee-saved registers, CSRs and RAM outside the deframer, the buffer and the frame
    unchanged; the invariant again. -/
structure TailPost (frame : Nat) (m₀ m : Machine) : Prop where
  pc : m.core.pc = m₀.core.get 1
  csr : m.core.sameCsr m₀.core
  sp : m.core.get 2 = m₀.core.get 2
  /-- Every register but a0-a4, a6 and t1 (tail's results and memmove's clobbers) is kept. -/
  saved : ∀ r : Reg, r.val ∉ [6, 10, 11, 12, 13, 14, 16] → m.core.get r = m₀.core.get r
  hconsumed : consumed m.ram (m₀.core.get 10) = 0
  hfilled : filled m.ram (m₀.core.get 10) =
    filled m₀.ram (m₀.core.get 10) - consumed m₀.ram (m₀.core.get 10)
  ret : m.core.get 10 = m₀.core.get 11 + BitVec.ofNat 32 (filled m.ram (m₀.core.get 10)) ∧
    (m.core.get 11).toNat = (m₀.core.get 12).toNat - filled m.ram (m₀.core.get 10)
  moved : ∀ k < filled m.ram (m₀.core.get 10),
    m.ram (m₀.core.get 11 + BitVec.ofNat 32 k) =
      m₀.ram (m₀.core.get 11 + BitVec.ofNat 32 (consumed m₀.ram (m₀.core.get 10) + k))
  inv : Inv m.ram (m₀.core.get 10) (m₀.core.get 12).toNat
  ram : KeepsRam frame m₀ m

/-- The obligation (not proved): `tail` returns, satisfying its postcondition. -/
def TailContract (frame : Nat) : Prop :=
  ∀ m₀, TailPre frame m₀ → ∃ k m, QRun B img k m₀ m ∧ TailPost frame m₀ m

/-- The falsifiable control (not proved): in the same environment with the invariant broken
    (`filled = len + 1`), `tail` reaches the panic. Together with `TailContract` it shows the
    contract's invariant premise is what keeps `tail` from panicking. -/
def TailPanicControl (frame : Nat) : Prop :=
  ∀ m₀, TailEnv frame m₀ → filled m₀.ram (m₀.core.get 10) = bufLen + 1 →
    ∃ k m, QRun B img k m₀ m ∧ m.core.pc = BitVec.ofNat 32 panicPc

/-! ## `park_pending` and `unpark_pending` (read from the bytes at 0x8001d388 and 0x8001d3f2)

Both: a 0x10-byte frame (ra, s0, s1) and one memmove call, so `parkStack = 0x10 + 0x30`;
clobbers a0-a4, a6, t1. -/

def parkStack : Nat := 0x10 + memmoveFrame

/-- `park_pending(&mut self, buf) -> usize`: `k = filled - consumed` pending bytes moved to the
    end of the buffer, the deframer emptied, `k` returned. -/
structure ParkPost (m₀ m : Machine) : Prop where
  pc : m.core.pc = m₀.core.get 1
  csr : m.core.sameCsr m₀.core
  sp : m.core.get 2 = m₀.core.get 2
  saved : ∀ r : Reg, r.val ∉ [6, 10, 11, 12, 13, 14, 16] → m.core.get r = m₀.core.get r
  hconsumed : consumed m.ram (m₀.core.get 10) = 0
  hfilled : filled m.ram (m₀.core.get 10) = 0
  ret : (m.core.get 10).toNat = filled m₀.ram (m₀.core.get 10) - consumed m₀.ram (m₀.core.get 10)
  moved : ∀ j < (m.core.get 10).toNat,
    m.ram (m₀.core.get 11 + BitVec.ofNat 32 ((m₀.core.get 12).toNat - (m.core.get 10).toNat + j)) =
      m₀.ram (m₀.core.get 11 + BitVec.ofNat 32 (consumed m₀.ram (m₀.core.get 10) + j))
  ram : KeepsRam parkStack m₀ m

def ParkContract : Prop :=
  ∀ m₀, CallEnv parkPc parkStack m₀ → Inv m₀.ram (m₀.core.get 10) (m₀.core.get 12).toNat →
    ∃ k m, QRun B img k m₀ m ∧ ParkPost m₀ m

/-- The control: with `filled = len + 1`, `park_pending` reaches the panic. -/
def ParkPanicControl : Prop :=
  ∀ m₀, CallEnv parkPc parkStack m₀ → filled m₀.ram (m₀.core.get 10) = bufLen + 1 →
    ∃ k m, QRun B img k m₀ m ∧ m.core.pc = BitVec.ofNat 32 panicPc

/-- `unpark_pending(&mut self, buf, parked)` (a3 = parked): the `parked` bytes at the end of the
    buffer moved to its front; consumed := 0, filled := parked. It reads neither field. -/
structure UnparkPost (m₀ m : Machine) : Prop where
  pc : m.core.pc = m₀.core.get 1
  csr : m.core.sameCsr m₀.core
  sp : m.core.get 2 = m₀.core.get 2
  saved : ∀ r : Reg, r.val ∉ [6, 10, 11, 12, 13, 14, 16] → m.core.get r = m₀.core.get r
  hconsumed : consumed m.ram (m₀.core.get 10) = 0
  hfilled : filled m.ram (m₀.core.get 10) = (m₀.core.get 13).toNat
  moved : ∀ j < (m₀.core.get 13).toNat,
    m.ram (m₀.core.get 11 + BitVec.ofNat 32 j) =
      m₀.ram (m₀.core.get 11 + BitVec.ofNat 32 ((m₀.core.get 12).toNat - (m₀.core.get 13).toNat + j))
  ram : KeepsRam parkStack m₀ m

def UnparkContract : Prop :=
  ∀ m₀, CallEnv unparkPc parkStack m₀ → (m₀.core.get 13).toNat ≤ bufLen →
    ∃ k m, QRun B img k m₀ m ∧ UnparkPost m₀ m

/-- The control: with `parked = len + 1`, `unpark_pending` reaches the panic. -/
def UnparkPanicControl : Prop :=
  ∀ m₀, CallEnv unparkPc parkStack m₀ → (m₀.core.get 13).toNat = bufLen + 1 →
    ∃ k m, QRun B img k m₀ m ∧ m.core.pc = BitVec.ofNat 32 panicPc

/-! ## `next` (read from the bytes at 0x8001d43a)

A 0x40-byte frame saving ra and s0-s11; callees: `cobs::dec::decode_in_place_report` (0x8001e02e,
0x10-byte frame, leaf but for `panic_bounds_check`), the slice-range check 0x8001ad76 (frameless)
and memmove (0x30 bytes), so `nextStack = 0x40 + 0x30`. Entry panics iff `filled > len` or
`consumed > filled`. It scans `buf[consumed..filled)` for a 0 delimiter; a frame found moves
`consumed` past it and, unless discarding, is COBS-decoded in place (errors are skipped); a decoded
frame longer than 2 bytes is moved to the buffer's front and returned as `Some`. A full buffer
without a delimiter is discarded (`consumed := filled`, `discarding := 1`). Returns
`Option<usize>` as (a0 = tag, a1 = value). The contract below is the SAFETY part R2 needs: no panic,
the invariant kept, writes confined; the decoded value is not specified here. -/

def nextStack : Nat := 0x40 + max 0x10 memmoveFrame

def discarding (ram : Word → BitVec 8) (p : Word) : Nat := (ram (p + 8)).toNat

structure NextPost (m₀ m : Machine) : Prop where
  pc : m.core.pc = m₀.core.get 1
  csr : m.core.sameCsr m₀.core
  sp : m.core.get 2 = m₀.core.get 2
  saved : ∀ r : Reg, r.val ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → m.core.get r = m₀.core.get r
  tag : (m.core.get 10).toNat ≤ 1
  inv : Inv m.ram (m₀.core.get 10) (m₀.core.get 12).toNat
  disc : discarding m.ram (m₀.core.get 10) ≤ 1
  ram : KeepsRam nextStack m₀ m

def NextContract : Prop :=
  ∀ m₀, CallEnv nextPc nextStack m₀ → Inv m₀.ram (m₀.core.get 10) (m₀.core.get 12).toNat →
    discarding m₀.ram (m₀.core.get 10) ≤ 1 → ∃ k m, QRun B img k m₀ m ∧ NextPost m₀ m

def NextPanicControl : Prop :=
  ∀ m₀, CallEnv nextPc nextStack m₀ → filled m₀.ram (m₀.core.get 10) = bufLen + 1 →
    ∃ k m, QRun B img k m₀ m ∧ m.core.pc = BitVec.ofNat 32 panicPc

/-! ## The copy contract the methods need (DEPENDENCY, not proved)

Every method copies with `memmove(dst, src, n)`, n up to `bufLen`, src and dst anywhere in the
buffer (either direction, any alignment). The review worker's `E5R.Rmk.Memmove.contractB` proves
n < 16 (either direction) and n ≥ 16 forward with src ≡ dst (mod 4); the n ≥ 16 backward and
misaligned paths are in progress. `CopyContract` is the full statement the deframer proofs take as
an explicit HYPOTHESIS until that work proves it; no result below holds without it. -/

/-- memmove's calling environment for a deframer call: trampoline pc, quiet, both ranges in model
    RAM, n ≤ bufLen, its 48-byte frame below sp in RAM and disjoint from both ranges. -/
structure CopyEnv (m : Machine) : Prop where
  pc : m.core.pc = 0x80020c1e
  quiet : Quiet m.core
  n : (m.core.get 12).toNat ≤ bufLen
  dst : B.inRam (m.core.get 10) (m.core.get 12).toNat = true
  src : B.inRam (m.core.get 11) (m.core.get 12).toNat = true
  frame : B.inRam (m.core.get 2 - BitVec.ofNat 32 memmoveFrame) memmoveFrame = true
  dstSep : (m.core.get 10).toNat + (m.core.get 12).toNat ≤ (m.core.get 2).toNat - memmoveFrame
  srcSep : (m.core.get 11).toNat + (m.core.get 12).toNat ≤ (m.core.get 2).toNat - memmoveFrame
  ra : (m.core.get 1).getLsbD 0 = false
  /-- As `Memmove.Slots` needs (memmove's save slots are word stores). -/
  spAl : (m.core.get 2).toNat % 4 = 0

/-- memmove's effect, as Memmove.PostB states it, with the frame widened to 48 bytes. -/
structure CopyPost (m₀ m : Machine) : Prop where
  pc : m.core.pc = m₀.core.get 1
  regs : ∀ r : Reg, r.val ∉ [5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31] → m.core.get r = m₀.core.get r
  csr : m.core.sameCsr m₀.core
  ram : ∀ x, ¬ ((m₀.core.get 2).toNat - memmoveFrame ≤ x.toNat ∧ x.toNat < (m₀.core.get 2).toNat) →
    m.ram x = Memmove.moved m₀.ram (m₀.core.get 10) (m₀.core.get 11) (m₀.core.get 12).toNat x

/-- The dependency: memmove does what it should for every deframer call. -/
def CopyContract : Prop := ∀ m₀, CopyEnv m₀ → ∃ k m, QRun B img k m₀ m ∧ CopyPost m₀ m

/-- The deframer obligations, stated against the dependency (each to be proved as an
    implication, then instantiated when `CopyContract` is a theorem). -/
def TailFromCopy : Prop := CopyContract → TailContract tailStack
def ParkFromCopy : Prop := CopyContract → ParkContract
def UnparkFromCopy : Prop := CopyContract → UnparkContract
def NextFromCopy : Prop := CopyContract → NextContract

/-! ## The session-level target (R2 acceptance; not proved) -/

/-- The program point of `run_session`'s receive loop and where its deframer and buffer live. -/
structure SessionPoint where
  loopPc : Nat
  deframer : Word
  buf : Word

/-- DERIVED (bytes + replay; to be confirmed by the proof): `run_session` is inlined into the main
    task's poll. Its deframer is zeroed once at 0x80003e0a..0x80003e12 (`sw zero, 0x2cf(s6)`,
    `sw zero, 0x2d3(s6)`, `sb zero, 0x2d7(s6)`); the receive loop head is 0x80003e1a (visited 14
    times, the init once, in the 300,000-state replay with 13 input bytes), which sets
    a0 = s6 + 0x2cf (the deframer), a1 = s7 + 0x1c1 (the buffer), a2 = 488 and calls `next`; on
    `None` it calls `tail` (0x80003f74) and reads the UART. The task future is a static, so the
    addresses are fixed: deframer 0x8002a78c..0x8002a798, buffer 0x8002a590..0x8002a778 (disjoint,
    both above rwBase 0x80029bc8), sp = 0x80fffe10 and mstatus = mie = 0 there in the replay. -/
def rynkSession : SessionPoint := ⟨0x80003e1a, 0x8002a78c, 0x8002a590⟩

/-- The R2 theorem to prove: from every machine at the session loop with the invariant, every
    machine the model can reach (any UART input, any environment) is not at the panic, and the
    invariant holds whenever the loop head is reached again. -/
def SessionSafe (sp : SessionPoint) : Prop :=
  ∀ m evs, Reach B img (fun m₀ => m₀.core.pc = BitVec.ofNat 32 sp.loopPc ∧ Inv m₀.ram sp.deframer bufLen) m evs →
    m.core.pc ≠ BitVec.ofNat 32 panicPc ∧ m.core.pc ≠ BitVec.ofNat 32 boundsPanicPc ∧
    m.core.pc ≠ BitVec.ofNat 32 unwindPc ∧
    (m.core.pc = BitVec.ofNat 32 sp.loopPc → Inv m.ram sp.deframer bufLen)

end E5R.Rmk.Deframer
