/-
  Differential testing against QEMU: replay a single-instruction trace in
  the Lean model and compare every architectural register after every
  transition. The oracle answers each environmental choice with what QEMU
  observed; everything else must be computed by the model.
-/
import Theories.Platform
open E5R

namespace Replay

def hex (s : String) : Option Nat :=
  s.foldl (fun acc c => acc.bind fun n =>
    if '0' ≤ c ∧ c ≤ '9' then some (n * 16 + (c.toNat - '0'.toNat))
    else if 'a' ≤ c ∧ c ≤ 'f' then some (n * 16 + (c.toNat - 'a'.toNat + 10)) else none) (some 0)

structure Obs where
  irq : Bool
  pc : Word
  x : Array Word
  mstatus : Word
  mie : Word
  mtvec : Word
  mepc : Word
  mcause : Word
  mscratch : Word

def parse (line : String) : Option Obs := do
  let ws := (line.splitOn " ").filter (· ≠ "")
  let tag ← ws.head?
  let vs ← (ws.drop 1).mapM fun w => (hex w).map (BitVec.ofNat 32)
  if vs.length ≠ 38 then none
  let a := vs.toArray
  return { irq := tag == "I", pc := a[0]!, x := #[0] ++ a.extract 1 32,
           mstatus := a[32]!, mie := a[33]!, mtvec := a[34]!, mepc := a[35]!,
           mcause := a[36]!, mscratch := a[37]! }

def coreOf (o : Obs) : Core :=
  { pc := o.pc, x := fun r => o.x[r.val]!, mie_ := o.mstatus.getLsbD 3,
    mpie := o.mstatus.getLsbD 7, mpp := o.mstatus.extractLsb' 11 2, mieReg := o.mie,
    mtvec := o.mtvec, mepc := o.mepc, mcause := o.mcause, mscratch := o.mscratch,
    resv := false }

def diff (csrs : Bool) (c : Core) (o : Obs) : List String := Id.run do
  let mut d := []
  if c.pc ≠ o.pc then d := d ++ [s!"pc model {c.pc.toHex} qemu {o.pc.toHex}"]
  for i in [1:32] do
    let r : Reg := ⟨i % 32, Nat.mod_lt _ (by decide)⟩
    if c.get r ≠ o.x[i]! then d := d ++ [s!"x{i} model {(c.get r).toHex} qemu {(o.x[i]!).toHex}"]
  if !csrs then return d
  if mstatusOf c ≠ o.mstatus then d := d ++ [s!"mstatus model {(mstatusOf c).toHex} qemu {o.mstatus.toHex}"]
  for (n, a, b) in [("mie", c.mieReg, o.mie), ("mtvec", c.mtvec, o.mtvec), ("mepc", c.mepc, o.mepc),
      ("mcause", c.mcause, o.mcause), ("mscratch", c.mscratch, o.mscratch)] do
    if a ≠ b then d := d ++ [s!"{n} model {a.toHex} qemu {b.toHex}"]
  return d

/-- The environment value QEMU's next state implies for the instruction at
    `m`: the destination register of a device load or CSR read, and SC
    success as `rd = 0`. -/
def oracleFor (img : List Segment) (m : Machine) (next : Obs) : Oracle :=
  match fetch img m.core.pc with
  | some (bits, len) => match decode bits len with
    | some (.sc rd _ _) => fun _ => if next.x[rd.val]! = 0 then 1 else 0
    | some (.load _ _ rd _ _) => fun _ => next.x[rd.val]!
    | some (.csr _ rd _ _) => fun _ => next.x[rd.val]!
    | _ => fun _ => 0
  | none => fun _ => 0

def stepI (B : Board) (img : List Segment) (m : Machine) (o : Oracle) : Except String (Machine × List Event) :=
  match stepInstr B img m o with
  | .ok c ram evs => .ok (⟨c, ram⟩, evs)
  | .fault f => .error s!"model fault {repr f} at {m.core.pc.toHex}"

/-- Replay the trace in `path`; `csrs` compares the modeled CSRs too (QEMU
    user mode does not print them). `watch` lists the values written to one
    device register. -/
def replay (B : Board) (img : List Segment) (csrs : Bool) (watch : Nat) (path : String) :
    IO UInt32 := do
  let lines := (← IO.FS.lines path).toList
  let obs := lines.filterMap parse
  if obs.length ≠ lines.length then
    IO.eprintln "unparsable trace line"; return 2
  let some first := obs.head? | return 2
  let mut m : Machine := ⟨coreOf first, fun _ => 0⟩
  let mut steps := 0
  let mut irqs := 0
  let mut events := 0
  let mut pwm : List Nat := []
  for next in obs.drop 1 do
    let mut cur := m
    if next.irq then
      -- QEMU may retire the instruction at the boundary first (WFI).
      if next.mepc ≠ cur.core.pc then
        match stepI B img cur (oracleFor img cur next) with
        | .ok (m', _) => cur := m'
        | .error e => IO.eprintln s!"step {steps}: {e}"; return 1
      let code := next.mcause.toNat % 2^31
      if !irqEnabled cur.core code then
        IO.eprintln s!"step {steps}: QEMU took interrupt {code}, model says not enabled"; return 1
      match takeIrq cur.core code with
      | .done c => cur := ⟨c, cur.ram⟩; irqs := irqs + 1
      | _ => IO.eprintln s!"step {steps}: interrupt entry faulted"; return 1
    else
      match stepI B img cur (oracleFor img cur next) with
      | .ok (m', evs) =>
        cur := m'
        events := events + evs.length
        pwm := pwm ++ (evs.filter (·.addr.toNat = watch)).map (·.val.toNat)
      | .error e => IO.eprintln s!"step {steps}: {e}"; return 1
    -- QEMU does not track the reservation; the model's is compared through
    -- SC results.
    let d := diff csrs cur.core next
    if !d.isEmpty then
      IO.eprintln s!"step {steps} (pc {m.core.pc.toHex}): {d}"; return 1
    m := cur
    steps := steps + 1
    -- RAM is a closure chain in the model; flatten it now and then so the
    -- replay stays linear. Only RAM addresses are ever written.
    if steps % 256 == 0 then
      let ram := m.ram
      let arr : Array (BitVec 8) := Array.ofFn (n := B.ramSize) fun i => ram (BitVec.ofNat 32 (B.ramBase + i))
      m := { m with ram := fun a =>
        if B.ramBase ≤ a.toNat ∧ a.toNat < B.ramBase + B.ramSize then arr[a.toNat - B.ramBase]! else 0 }
  IO.println s!"replayed {steps} transitions, {irqs} interrupts, {events} device writes; model and QEMU agree"
  IO.println s!"writes to {watch}: {pwm}"
  return 0

end Replay
