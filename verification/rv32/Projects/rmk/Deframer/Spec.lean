/-
  R2: the host-input property for RMK's Rynk deframer, as Lean statements.
  Original e5r code, Apache-2.0.

  STATUS: SPECIFICATION ONLY. Nothing here is proved; every definition below is a proof
  obligation, and the constants marked CANDIDATE are read from the disassembly of the pinned ELF
  (f39d833f..., review/rmk/deframer-contracts.md on the review branch) and must be confirmed by
  the proof that uses them. No theorem in this file claims safety.

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
import Projects.rmk.Run
import Projects.rmk.QemuRiscvRynk.Coherence

namespace E5R.Rmk.Deframer
open E5R E5R.Rmk

abbrev B : Board := Rmk.QemuRiscvRynk.board
abbrev img : List Segment := Rmk.QemuRiscvRynk.img

/-! ## Constants read from the ELF (CANDIDATE until a proof uses them) -/

def tailPc : Nat := 0x8001d576
def parkPc : Nat := 0x8001d388
def unparkPc : Nat := 0x8001d3f2
def nextPc : Nat := 0x8001d43a
/-- `core::slice::index::slice_index_fail`: every bounds failure of the deframer calls it. -/
def panicPc : Nat := 0x8001fafc
/-- The firmware's buffer length (`RYNK_BUFFER_SIZE`). -/
def bufLen : Nat := 488

/-! ## The deframer in memory: `consumed @ +0`, `filled @ +4`, `discarding @ +8` -/

def word (ram : Word → BitVec 8) (a : Word) : Nat := (ramRead ram a .w).toNat
def consumed (ram : Word → BitVec 8) (p : Word) : Nat := word ram p
def filled (ram : Word → BitVec 8) (p : Word) : Nat := word ram (p + 4)

/-- The state invariant. -/
def Inv (ram : Word → BitVec 8) (p : Word) (len : Nat) : Prop :=
  consumed ram p ≤ filled ram p ∧ filled ram p ≤ len

/-! ## `Deframer::tail` (first contract to prove) -/

/-- CANDIDATE calling environment of `tail(&mut self, buf: &mut [u8]) -> &mut [u8]`: a0 = the
    deframer, (a1, a2) = the buffer; both in model RAM and disjoint; a quiet machine; an even return
    address; `frame` bytes below sp are the callee's stack frame (size to be read from the prologue;
    CANDIDATE), in RAM. -/
structure TailEnv (frame : Nat) (m : Machine) : Prop where
  pc : m.core.pc = BitVec.ofNat 32 tailPc
  quiet : Quiet m.core
  self : B.inRam (m.core.get 10) 12 = true
  buf : B.inRam (m.core.get 11) (m.core.get 12).toNat = true
  len : (m.core.get 12).toNat = bufLen
  sep : (m.core.get 10).toNat + 12 ≤ (m.core.get 11).toNat ∨
    (m.core.get 11).toNat + (m.core.get 12).toNat ≤ (m.core.get 10).toNat
  stack : B.inRam (m.core.get 2 - BitVec.ofNat 32 frame) frame = true
  ra : (m.core.get 1).getLsbD 0 = false

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
  saved : ∀ r : Reg, r.val ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] → m.core.get r = m₀.core.get r
  hconsumed : consumed m.ram (m₀.core.get 10) = 0
  hfilled : filled m.ram (m₀.core.get 10) =
    filled m₀.ram (m₀.core.get 10) - consumed m₀.ram (m₀.core.get 10)
  ret : m.core.get 10 = m₀.core.get 11 + BitVec.ofNat 32 (filled m.ram (m₀.core.get 10)) ∧
    (m.core.get 11).toNat = (m₀.core.get 12).toNat - filled m.ram (m₀.core.get 10)
  moved : ∀ k < filled m.ram (m₀.core.get 10),
    m.ram (m₀.core.get 11 + BitVec.ofNat 32 k) =
      m₀.ram (m₀.core.get 11 + BitVec.ofNat 32 (consumed m₀.ram (m₀.core.get 10) + k))
  inv : Inv m.ram (m₀.core.get 10) (m₀.core.get 12).toNat

/-- The obligation (not proved): `tail` returns, satisfying its postcondition. -/
def TailContract (frame : Nat) : Prop :=
  ∀ m₀, TailPre frame m₀ → ∃ k m, QRun B img k m₀ m ∧ TailPost frame m₀ m

/-- The falsifiable control (not proved): in the same environment with the invariant broken
    (`filled = len + 1`), `tail` reaches the panic. Together with `TailContract` it shows the
    contract's invariant premise is what keeps `tail` from panicking. -/
def TailPanicControl (frame : Nat) : Prop :=
  ∀ m₀, TailEnv frame m₀ → filled m₀.ram (m₀.core.get 10) = bufLen + 1 →
    ∃ k m, QRun B img k m₀ m ∧ m.core.pc = BitVec.ofNat 32 panicPc

/-! ## The session-level target (R2 acceptance; not proved) -/

/-- CANDIDATE: the program point of `run_session`'s receive loop and where its deframer lives;
    both still to be fixed from the disassembly (peer). -/
structure SessionPoint where
  loopPc : Nat
  deframer : Word
  buf : Word

/-- The R2 theorem to prove: from every machine at the session loop with the invariant, every
    machine the model can reach (any UART input, any environment) is not at the panic, and the
    invariant holds whenever the loop head is reached again. -/
def SessionSafe (sp : SessionPoint) : Prop :=
  ∀ m evs, Reach B img (fun m₀ => m₀.core.pc = BitVec.ofNat 32 sp.loopPc ∧ Inv m₀.ram sp.deframer bufLen) m evs →
    m.core.pc ≠ BitVec.ofNat 32 panicPc ∧
    (m.core.pc = BitVec.ofNat 32 sp.loopPc → Inv m.ram sp.deframer bufLen)

end E5R.Rmk.Deframer
