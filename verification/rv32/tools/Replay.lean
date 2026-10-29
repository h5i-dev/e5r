/-
  Replay a QEMU sifive_e trace of the Embassy firmware (trace format 2,
  written by tools/qemu_trace.py) in the Lean model.

  After every transition the model must match QEMU's next state in every
  register and modeled CSR, and its device traffic must match QEMU's MMIO
  log, which is QEMU's own observation, not the model's output:
  * each device write the model performs must be the next MMIO write QEMU
    performed, at the same address, with the same value, as a word, and QEMU
    must perform no other;
  * each device read the model performs must be the next MMIO read QEMU
    performed, at the same address, as a word; the value the model receives
    is the value QEMU read. QEMU must perform no other read.
  The remaining environment values are SC success (`rd = 0` in QEMU's next
  state) and the mip read (`rd`); RAM and every other CSR are computed by
  the model alone.

  Interrupt boundaries are explicit: QEMU reports the interrupt with its
  epc. If the model is not at epc it must get there in exactly one
  instruction (QEMU retired one first, e.g. WFI), the interrupt must be
  enabled in the model, and entry must produce QEMU's next state.

  Exit status: 0 agreement; 1 a semantic mismatch between the model and
  QEMU (the first one is reported); 2 the trace is malformed, cut off or
  edited, or the tool itself is inconsistent. A 2 is never evidence about
  the model.
-/
import tools.ReplayLib
import Theories.Board.Hifive1Revb
import Projects.hifive1.Image
open E5R

namespace Replay.Mmio

/-- An MMIO access as QEMU logged it. -/
structure Access where
  addr : Word
  val : Word
  size : Nat

inductive Item where
  | state (o : Obs)
  | read (a : Access)
  | write (a : Access)
  | irq (cause epc : Word)
  | done (states reads writes irqs : Nat)

def words (line : String) : List String := (line.splitOn " ").filter (· ≠ "")

def parseItem (line : String) : Option Item := do
  match words line with
  | "S" :: _ => (Replay.parse line).map .state
  | ["R", a, v, s] => return .read ⟨BitVec.ofNat 32 (← hex a), BitVec.ofNat 32 (← hex v), ← hex s⟩
  | ["W", a, v, s] => return .write ⟨BitVec.ofNat 32 (← hex a), BitVec.ofNat 32 (← hex v), ← hex s⟩
  | ["I", c, e] => return .irq (BitVec.ofNat 32 (← hex c)) (BitVec.ofNat 32 (← hex e))
  | ["E", n, r, w, i] => return .done (← hex n) (← hex r) (← hex w) (← hex i)
  | _ => none

/-- The environment value QEMU's next state implies for a `choose` (SC
    success: `rd = 0`) or `pick` (a mip read: `rd`). None for any other
    instruction: the model then has no business asking. -/
def choiceFor (img : List Segment) (m : Machine) (next : Obs) : Option Word :=
  match fetch img m.core.pc with
  | some (bits, len) => match decode bits len with
    | some (.sc rd _ _) => some (if next.x[rd.val]! = 0 then 1 else 0)
    | some (.csr _ rd _ _) => some next.x[rd.val]!
    | _ => none
  | none => none

/-- Environment values handed to the model so far, and QEMU's MMIO reads not
    yet matched by a model device read. -/
structure Supply where
  vals : Array Word := #[]
  reads : List Access

def hx (w : Word) : String := w.toHex

/-- Follow the effect tree of one step exactly as `interp` does (same order
    of checks, same board predicates), answering each environment request
    from QEMU's evidence. `.error` is a semantic mismatch. The result is the
    environment as an oracle plus the step outcome this walk reached, which
    the caller checks against `stepInstr` under that oracle, so a walk that
    strayed from `interp` is a tool error, not an accepted step. -/
def walk (B : Board) (img : List Segment) (choice : Option Word) :
    Eff → (Word → BitVec 8) → List Event → Supply → Except String (Supply × Result)
  | .done c, ram, evs, s => .ok (s, .ok c ram evs)
  | .trap e, _, _, s => .ok (s, .fault (.trap e))
  | .unsupported why, _, _, s => .ok (s, .fault (.unsupported why))
  | .choose k, ram, evs, s => do
    let some v := choice | .error "the model asks for an environment choice at an instruction that has none"
    walk B img choice (k (v.getLsbD 0)) ram evs { s with vals := s.vals.push v }
  | .pick k, ram, evs, s => do
    let some v := choice | .error "the model asks for an environment value at an instruction that has none"
    walk B img choice (k v) ram evs { s with vals := s.vals.push v }
  | .load wd a atomic k, ram, evs, s =>
    if a.toNat % wd.bytes ≠ 0 then .ok (s, .fault .misaligned)
    else if B.inRam a wd.bytes then walk B img choice (k (ramRead ram a wd)) ram evs s
    else if atomic then .ok (s, .fault (.unsupported "atomic access outside RAM"))
    else match romRead? img a.toNat wd.bytes false with
      | some v => walk B img choice (k v) ram evs s
      | none => match B.device? a with
        | some d =>
          if d.read && wd = .w then
            match s.reads with
            | r :: rest =>
              if r.addr ≠ a ∨ r.size ≠ 4 then
                .error s!"model reads device {hx a}, QEMU's next MMIO read is {hx r.addr} ({r.size} bytes)"
              else walk B img choice (k r.val) ram evs { vals := s.vals.push r.val, reads := rest }
            | [] => .error s!"model reads device {hx a}, QEMU performed no further MMIO read"
          else .ok (s, .fault (.unsupported "device read"))
        | none => .ok (s, .fault (.unsupported "load from an unmodeled address"))
  | .store wd a v atomic k, ram, evs, s =>
    if a.toNat % wd.bytes ≠ 0 then .ok (s, .fault .misaligned)
    else if B.inRam a wd.bytes then walk B img choice k (ramWrite ram a v wd) evs s
    else if atomic then .ok (s, .fault (.unsupported "atomic access outside RAM"))
    else match B.device? a with
      | some d => if d.write && wd = .w then walk B img choice k ram (evs ++ [⟨a, v⟩]) s
                  else .ok (s, .fault (.unsupported "device write"))
      | none => .ok (s, .fault (.unsupported "store to an unmodeled address"))

def sameCore (a b : Core) : Bool :=
  a.pc == b.pc && (List.range 32).all (fun i => a.get ⟨i % 32, Nat.mod_lt _ (by decide)⟩ ==
    b.get ⟨i % 32, Nat.mod_lt _ (by decide)⟩) &&
  a.mie_ == b.mie_ && a.mpie == b.mpie && a.mpp == b.mpp && a.mieReg == b.mieReg &&
  a.mtvec == b.mtvec && a.mepc == b.mepc && a.mcause == b.mcause && a.mscratch == b.mscratch &&
  a.resv == b.resv

inductive Outcome where
  | mismatch (msg : String)
  | toolError (msg : String)

/-- The model's step, before it is compared with QEMU's next state. -/
structure Stepped where
  m : Machine
  /-- The walk reached the step's outcome too, so its device reads are the
      ones `stepInstr` performed. Checked after the state comparison, so a
      changed model shows up as a mismatch with QEMU where it can. -/
  walkAgrees : Bool
  /-- QEMU's MMIO reads in the transition the model did not perform. -/
  extraReads : List Access

/-- One instruction of the model, its device writes checked against QEMU's
    MMIO `writes` for the transition and its device reads answered from
    QEMU's `reads`. -/
def instr (B : Board) (img : List Segment) (m : Machine) (next : Obs)
    (reads writes : List Access) : Except Outcome Stepped := do
  if m.core.pc.getLsbD 0 then throw (.mismatch s!"model fault: misaligned fetch at {hx m.core.pc}")
  let some (bits, len) := fetch img m.core.pc
    | throw (.mismatch s!"model fault: fetch outside the executable image at {hx m.core.pc}")
  let some i := decode bits len | throw (.mismatch s!"model fault: illegal instruction at {hx m.core.pc}")
  let (s, walked) ← (walk B img (choiceFor img m next) (exec m.core len i) m.ram [] ⟨#[], reads⟩).mapError .mismatch
  match stepInstr B img m (fun k => s.vals.getD k 0) with
  | .fault f => throw (.mismatch s!"model fault {repr f} at {hx m.core.pc}")
  | .ok c ram evs =>
    let ew : List (Word × Word × Nat) := evs.map fun e => (e.addr, e.val, 4)
    let qw : List (Word × Word × Nat) := writes.map fun w => (w.addr, w.val, w.size)
    if ew ≠ qw then
      let fmt := fun (l : List (Word × Word × Nat)) => l.map fun (a, v, n) => s!"{hx a}<-{hx v}/{n}"
      throw (.mismatch s!"device writes: model {fmt ew}, QEMU {fmt qw}")
    let agrees := match walked with
      | .ok c' _ evs' => sameCore c c' && evs == evs'
      | .fault _ => false
    return ⟨⟨c, ram⟩, agrees, s.reads⟩

def regOf (xs : Array Word) (r : Reg) : Word := xs[r.val]!

/-- Look up RAM in a flattened copy. Takes the array as an argument, so the
    compiler cannot move the array's construction into the closure. -/
def ramOf (B : Board) (arr : Array (BitVec 8)) (a : Word) : BitVec 8 :=
  if B.ramBase ≤ a.toNat ∧ a.toNat < B.ramBase + B.ramSize then arr[a.toNat - B.ramBase]! else 0

def report (code : UInt32) (msg : String) : IO UInt32 := do
  IO.eprintln (if code == 1 then s!"MISMATCH: {msg}" else s!"TRACE OR TOOL ERROR: {msg}")
  return code

/-- Replay a format 2 trace. `watch` lists the values written to one device
    register. -/
def replay (B : Board) (img : List Segment) (watch : Nat) (path : String) : IO UInt32 := do
  let lines := (← IO.FS.lines path).toList.filter (· ≠ "")
  match lines with
  | "V 2" :: _ => pure ()
  | _ => return ← report 2 "not a format 2 trace (`V 2` header missing); regenerate it with tools/qemu_trace.py from a log with -trace memory_region_ops_read -trace memory_region_ops_write"
  let body := lines.drop 1
  let items := body.filterMap parseItem
  if items.length ≠ body.length then return ← report 2 "unparsable trace line"
  let some (.done ns nr nw ni) := items.getLast? | return ← report 2 "end marker missing: the trace is cut off"
  let items := items.dropLast
  let cnt (p : Item → Bool) := (items.filter p).length
  if cnt (fun | .done .. => true | _ => false) ≠ 0 then return ← report 2 "end marker before the end"
  if (ns, nr, nw, ni) ≠ (cnt (fun | .state _ => true | _ => false), cnt (fun | .read _ => true | _ => false),
      cnt (fun | .write _ => true | _ => false), cnt (fun | .irq .. => true | _ => false)) then
    return ← report 2 "the end marker's counts do not match the trace: lines were removed or added"
  let some (.state first) := items.head? | return ← report 2 "the trace must start with a state"
  let mut m : Machine := ⟨coreOf first, fun _ => 0⟩
  -- QEMU's events since the last state: before an interrupt, after it.
  let mut reads : List Access := []
  let mut writes : List Access := []
  let mut irq : Option (Word × Word) := none
  let mut steps := 0
  let mut irqs := 0
  let mut nreads := 0
  let mut nwrites := 0
  let mut pwm : List Nat := []
  for it in items.drop 1 do
    match it with
    | .read a =>
      if irq.isSome then return ← report 2 s!"step {steps}: MMIO read after the interrupt entry, before the next state"
      reads := reads ++ [a]
    | .write a =>
      if irq.isSome then return ← report 2 s!"step {steps}: MMIO write after the interrupt entry, before the next state"
      writes := writes ++ [a]
    | .irq c e =>
      if irq.isSome then return ← report 2 s!"step {steps}: two interrupts in one transition"
      if c.toNat < 2^31 then return ← report 2 s!"step {steps}: synchronous cause {hx c} reported as an interrupt"
      irq := some (c, e)
    | .done .. => return ← report 2 "unreachable"
    | .state next =>
      let pc0 := m.core.pc
      let mut cur := m
      let mut checked : Option Stepped := none
      let stepped := irq.isNone || cur.core.pc ≠ (irq.map (·.2)).getD 0
      if stepped then
        match instr B img cur next reads writes with
        | .ok st => cur := st.m; checked := some st
        | .error (.mismatch e) => return ← report 1 s!"step {steps} (pc {hx pc0}): {e}"
        | .error (.toolError e) => return ← report 2 s!"step {steps} (pc {hx pc0}): {e}"
      else if !(reads.isEmpty && writes.isEmpty) then
        return ← report 1 s!"step {steps} (pc {hx pc0}): QEMU accessed devices before an interrupt taken at the model's pc, without retiring an instruction"
      if let some (cause, epc) := irq then
        if cur.core.pc ≠ epc then
          return ← report 1 s!"step {steps} (pc {hx pc0}): QEMU took an interrupt with epc {hx epc}, the model is at {hx cur.core.pc}"
        let code := cause.toNat % 2^31
        if !irqEnabled cur.core code then
          return ← report 1 s!"step {steps} (pc {hx pc0}): QEMU took interrupt {code}, the model says it is not enabled"
        match takeIrq cur.core code with
        | .done c => cur := ⟨c, cur.ram⟩; irqs := irqs + 1
        | _ => return ← report 1 s!"step {steps} (pc {hx pc0}): interrupt entry faulted in the model"
      let d := diff true cur.core next
      if !d.isEmpty then return ← report 1 s!"step {steps} (pc {hx pc0}): {d}"
      if let some st := checked then
        if !st.walkAgrees then
          return ← report 2 s!"step {steps} (pc {hx pc0}): the replay's walk of the effect tree disagrees with stepInstr (Platform.interp changed, or the replay is stale)"
        if let r :: _ := st.extraReads then
          return ← report 1 s!"step {steps} (pc {hx pc0}): QEMU read device {hx r.addr}, the model performed no such read"
      nreads := nreads + reads.length
      nwrites := nwrites + writes.length
      pwm := pwm ++ (writes.filter (·.addr.toNat = watch)).map (·.val.toNat)
      -- Flatten the register closure chain so the replay stays linear. The
      -- values are the model's; nothing is taken from QEMU here.
      let xs : Array Word := Array.ofFn (n := 32) fun i => cur.core.x ⟨i.val, i.isLt⟩
      m := { cur with core := { cur.core with x := regOf xs } }
      reads := []; writes := []; irq := none
      steps := steps + 1
      -- RAM is a closure chain in the model; flatten it now and then. Only
      -- RAM addresses are ever written.
      if steps % 256 == 0 then
        let ram := m.ram
        let arr : Array (BitVec 8) := Array.ofFn (n := B.ramSize) fun i => ram (BitVec.ofNat 32 (B.ramBase + i))
        m := { m with ram := ramOf B arr }
  IO.println s!"replayed {steps} transitions, {irqs} interrupts, {nreads} device reads and {nwrites} device writes equal to QEMU's MMIO log; model and QEMU agree"
  IO.println s!"writes to {watch}: {pwm}"
  return 0

end Replay.Mmio

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: replay TRACE"; return 2
  Replay.Mmio.replay E5R.Hifive1Revb.board E5R.Firmware.segments 0x10015024 path
