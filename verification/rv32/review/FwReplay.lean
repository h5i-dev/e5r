/-
  Review replay of a whole-firmware QEMU trace (from review/fwtrace.py),
  written independently of tools/Replay.lean to audit it.

  Original review code, Apache-2.0. Per transition it checks:
  * every GPR, the PC and the modeled CSRs (as Replay.lean does);
  * that the model's device events equal the MMIO writes QEMU performed in
    that transition, address and value, in order (Replay.lean only counts
    them);
  * interrupt boundaries from QEMU's own `epc`: the model must reach exactly
    that PC with at most one instruction, the source must be enabled, and
    entry must produce the next state. No mepc heuristic.

  Run: `lake env lean --run review/FwReplay.lean <trace>`.
-/
import Theories.Board.Hifive1Revb
import Projects.hifive1.Image
open E5R

namespace FwReplay

def hexNat (s : String) : Option Nat :=
  s.foldl (fun acc c => acc.bind fun n =>
    if '0' ≤ c ∧ c ≤ '9' then some (n * 16 + (c.toNat - '0'.toNat))
    else if 'a' ≤ c ∧ c ≤ 'f' then some (n * 16 + (c.toNat - 'a'.toNat + 10)) else none) (some 0)

inductive Item where
  | state (v : Array Word)
  | irq (cause epc : Word)
  | write (addr val : Word) (size : Nat)

def parse (line : String) : Option Item := do
  let ws := (line.splitOn " ").filter (· ≠ "")
  let tag ← ws.head?
  let vs ← (ws.drop 1).mapM hexNat
  match tag, vs with
  | "S", _ => if vs.length = 38 then some (.state (vs.toArray.map (BitVec.ofNat 32))) else none
  | "I", [c, e] => some (.irq (BitVec.ofNat 32 c) (BitVec.ofNat 32 e))
  | "W", [a, v, s] => some (.write (BitVec.ofNat 32 a) (BitVec.ofNat 32 v) s)
  | _, _ => none

def img : List Segment := Firmware.segments
def B : Board := Hifive1Revb.board
def reg (i : Nat) : Reg := ⟨i % 32, Nat.mod_lt _ (by decide)⟩

def coreOf (v : Array Word) : Core :=
  let ms := v[32]!
  { pc := v[0]!, x := fun r => if r.val = 0 then 0 else v[r.val]!, mie_ := ms.getLsbD 3,
    mpie := ms.getLsbD 7, mpp := ms.extractLsb' 11 2, mieReg := v[33]!, mtvec := v[34]!,
    mepc := v[35]!, mcause := v[36]!, mscratch := v[37]!, resv := false }

def diff (c : Core) (v : Array Word) : List String := Id.run do
  let mut d := []
  if c.pc ≠ v[0]! then d := d ++ [s!"pc model {c.pc.toHex} qemu {v[0]!.toHex}"]
  for i in [1:32] do
    if c.get (reg i) ≠ v[i]! then d := d ++ [s!"x{i} model {(c.get (reg i)).toHex} qemu {v[i]!.toHex}"]
  for (n, a, b) in [("mstatus", mstatusOf c, v[32]!), ("mie", c.mieReg, v[33]!), ("mtvec", c.mtvec, v[34]!),
      ("mepc", c.mepc, v[35]!), ("mcause", c.mcause, v[36]!), ("mscratch", c.mscratch, v[37]!)] do
    if a ≠ b then d := d ++ [s!"{n} model {a.toHex} qemu {b.toHex}"]
  return d

def oracleFor (m : Machine) (next : Array Word) : Oracle :=
  match fetch img m.core.pc with
  | some (bits, len) => match decode bits len with
    | some (.sc rd _ _) => fun _ => if rd.val ≠ 0 ∧ next[rd.val]! = 0 then 1 else 0
    | some (.load _ _ rd _ _) => fun _ => if rd.val = 0 then 0 else next[rd.val]!
    | some (.csr _ rd _ _) => fun _ => if rd.val = 0 then 0 else next[rd.val]!
    | _ => fun _ => 0
  | none => fun _ => 0

def regOf (xs : Array Word) (r : Reg) : Word := xs[r.val]!

/-- Look up RAM in a flattened copy. Takes the array as an argument: a helper
    that built the array and returned a closure let the compiler move the
    construction into the closure, rebuilding 16 KiB on every read. -/
def ramOf (arr : Array (BitVec 8)) (a : Word) : BitVec 8 :=
  if B.ramBase ≤ a.toNat ∧ a.toNat < B.ramBase + B.ramSize then arr[a.toNat - B.ramBase]! else 0

end FwReplay

open FwReplay in
def main (args : List String) : IO UInt32 := do
  let lines := (← IO.FS.lines args[0]!).toList.filter (· ≠ "")
  let items := lines.filterMap parse
  if items.length ≠ lines.length then IO.eprintln "unparsable trace line"; return 2
  let some (.state first) := items.head? | IO.eprintln "trace must start with a state"; return 2
  let mut m : Machine := ⟨coreOf first, fun _ => 0⟩
  let mut pendI : List (Word × Word) := []
  let mut pendW : List Event := []
  let mut steps := 0
  let mut irqs := 0
  let mut writes := 0
  let mut instrs := 0
  for it in items.drop 1 do
    match it with
    | .irq c e => pendI := pendI ++ [(c, e)]
    | .write a v s =>
      if s ≠ 4 then IO.eprintln s!"step {steps}: {s}-byte MMIO write at {a.toHex}"; return 1
      pendW := pendW ++ [⟨a, v⟩]
    | .state next =>
      let mut cur := m
      let mut evs : List Event := []
      let mut stepped := false
      if pendI.length > 1 then IO.eprintln s!"step {steps}: {pendI.length} interrupts in one transition"; return 1
      match pendI with
      | [(cause, epc)] =>
        if cur.core.pc ≠ epc then
          match stepInstr B img cur (oracleFor cur next) with
          | .ok c ram e => cur := ⟨c, ram⟩; evs := e; stepped := true
          | .fault f => IO.eprintln s!"step {steps}: model fault {repr f} at {cur.core.pc.toHex}"; return 1
        if cur.core.pc ≠ epc then
          IO.eprintln s!"step {steps}: QEMU interrupt epc {epc.toHex}, model at {cur.core.pc.toHex}"; return 1
        let code := cause.toNat % 2^31
        if cause.toNat < 2^31 then IO.eprintln s!"step {steps}: synchronous cause {cause.toHex}"; return 1
        if !irqEnabled cur.core code then
          IO.eprintln s!"step {steps}: QEMU took interrupt {code}, model says not enabled"; return 1
        match takeIrq cur.core code with
        | .done c => cur := ⟨c, cur.ram⟩; irqs := irqs + 1
        | _ => IO.eprintln s!"step {steps}: interrupt entry faulted"; return 1
      | _ =>
        match stepInstr B img cur (oracleFor cur next) with
        | .ok c ram e => cur := ⟨c, ram⟩; evs := e; stepped := true
        | .fault f => IO.eprintln s!"step {steps}: model fault {repr f} at {cur.core.pc.toHex}"; return 1
      if stepped then instrs := instrs + 1
      let ew := evs.map fun e => (e.addr, e.val)
      let qw := pendW.map fun e => (e.addr, e.val)
      if ew ≠ qw then
        IO.eprintln s!"step {steps} (pc {m.core.pc.toHex}): device writes model {ew.map fun (a, v) => (a.toHex, v.toHex)} qemu {qw.map fun (a, v) => (a.toHex, v.toHex)}"
        return 1
      writes := writes + ew.length
      let d := diff cur.core next
      if !d.isEmpty then IO.eprintln s!"step {steps} (pc {m.core.pc.toHex}): {d}"; return 1
      -- Flatten the register closure chain (values unchanged; nothing is
      -- taken from QEMU here) so the replay stays linear.
      let xs : Array Word := Array.ofFn (n := 32) fun i => cur.core.x ⟨i.val, i.isLt⟩
      m := { cur with core := { cur.core with x := regOf xs } }
      pendI := []
      pendW := []
      steps := steps + 1
      if steps % 256 == 0 then
        let ram := m.ram
        let arr : Array (BitVec 8) := Array.ofFn (n := B.ramSize) fun i => ram (BitVec.ofNat 32 (B.ramBase + i))
        m := { m with ram := ramOf arr }
  IO.println s!"review replay: {steps} transitions ({instrs} instructions, {irqs} interrupts), {writes} device writes equal to QEMU's; every GPR/PC/CSR equal"
  return 0
