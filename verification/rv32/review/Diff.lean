/-
  Review harness, model side: compare QEMU sifive_e records written by the
  bare-metal firmware of `review/harness.py` with `stepInstr`/`takeIrq`.

  Original review code, Apache-2.0. Each input line is `R` followed by 144
  hex words: the 64-word descriptor (pre-state as written), 16 words of code
  from the candidate address, and the 64-word record (post-state, plus the
  CSR values QEMU read back after setup). The model's pre-state is built from
  the descriptor and the read-backs only; the post-state is never fed back,
  except for the environment's choices (SC success, mip and device reads),
  which come from the register the instruction wrote. Output: one verdict per
  case.

  Run: `lake env lean --run review/Diff.lean <qemu.txt> <verdicts.txt>`.
-/
import Theories.Board.Hifive1Revb
open E5R

namespace Review

def hexNat (s : String) : Option Nat :=
  s.foldl (fun acc c => acc.bind fun n =>
    if '0' ≤ c ∧ c ≤ '9' then some (n * 16 + (c.toNat - '0'.toNat))
    else if 'a' ≤ c ∧ c ≤ 'f' then some (n * 16 + (c.toNat - 'a'.toNat + 10)) else none) (some 0)

structure Rec where
  desc : Array Word
  code : Array Word
  post : Array Word

def parse (line : String) : Option Rec := do
  let ws := (line.splitOn " ").filter (· ≠ "")
  guard (ws.head? = some "R")
  let vs ← (ws.drop 1).mapM fun w => (hexNat w).map (BitVec.ofNat 32)
  guard (vs.length = 144)
  let a := vs.toArray
  return { desc := a.extract 0 64, code := a.extract 64 80, post := a.extract 80 144 }

def recordBase : Nat := 0x80001000
def B : Board := Hifive1Revb.board

def reg (i : Nat) : Reg := ⟨i % 32, Nat.mod_lt _ (by decide)⟩

/-- The RAM the candidate sees: record words 0..41 zeroed by setup, 42..47
    the CSR read-backs, 48..63 the window; everything else zero (the
    candidates are written to touch only the window). -/
def preRam (r : Rec) : Word → BitVec 8 := fun a =>
  if recordBase ≤ a.toNat ∧ a.toNat < recordBase + 256 then
    let off := a.toNat - recordBase
    let i := off / 4
    let w : Word := if i < 42 then 0 else if i < 48 then r.post[i]! else r.desc[i]!
    BitVec.ofNat 8 (w.toNat / 256 ^ (off % 4))
  else 0

def preCore (r : Rec) : Core :=
  let ms := r.post[42]!
  { pc := r.desc[41]!, x := fun i => if i.val = 0 then 0 else r.desc[i.val - 1]!,
    mie_ := ms.getLsbD 3, mpie := ms.getLsbD 7, mpp := ms.extractLsb' 11 2,
    mieReg := r.post[43]! &&& mieMask, mtvec := r.post[44]!, mepc := r.post[45]!,
    mcause := r.post[46]!, mscratch := r.post[47]!, resv := false }

def img (r : Rec) : List Segment :=
  let bytes := (List.range 64).map fun k => (r.code[k / 4]!.toNat / 256 ^ (k % 4)) % 256
  [{ base := r.desc[41]!.toNat, bytes := bytes, exec := true }]

/-- The environment's answer for the instruction at `m`, read off what QEMU
    wrote to its destination register. -/
def oracleFor (r : Rec) (m : Machine) : Oracle :=
  match fetch (img r) m.core.pc with
  | some (bits, len) => match decode bits len with
    | some (.sc rd _ _) => fun _ => if r.post[rd.val]! = 0 ∧ rd.val ≠ 0 then 1 else 0
    | some (.load _ _ rd _ _) => fun _ => r.post[rd.val]!
    | some (.csr _ rd _ _) => fun _ => r.post[rd.val]!
    | _ => fun _ => 0
  | none => fun _ => 0

def gprDiff (c : Core) (r : Rec) : List String := Id.run do
  let mut d := []
  for i in [1:32] do
    if c.get (reg i) ≠ r.post[i]! then
      d := d ++ [s!"x{i} model {(c.get (reg i)).toHex} qemu {r.post[i]!.toHex}"]
  return d

def csrDiff (c : Core) (r : Rec) (withScratch : Bool) : List String := Id.run do
  let mut d := []
  let mut l := [("mstatus", mstatusOf c, r.post[32]!), ("mie", c.mieReg, r.post[33]!),
                ("mtvec", c.mtvec, r.post[34]!), ("mepc", c.mepc, r.post[35]!),
                ("mcause", c.mcause, r.post[36]!)]
  if withScratch then l := l ++ [("mscratch", c.mscratch, r.post[37]!)]
  for (n, a, b) in l do
    if a ≠ b then d := d ++ [s!"{n} model {a.toHex} qemu {b.toHex}"]
  return d

def faultName : Fault → String
  | .trap e => s!"trap {repr e}"
  | .misaligned => "misaligned"
  | .unsupported why => s!"unsupported({why})"

/-- Does a model fault describe the synchronous exception QEMU took? -/
def faultMatches (f : Fault) (cause : Nat) : Bool :=
  match f, cause with
  | .trap .misalignedFetch, 0 => true
  | .trap .illegal, 2 => true
  | .trap .ebreak, 3 => true
  | .trap .ecall, 11 => true
  | .misaligned, 4 => true
  | .misaligned, 6 => true
  | _, _ => false

def postPc (r : Rec) : Option Word :=
  if r.post[38]! = 0 then some r.desc[44]!
  else if r.post[38]!.toNat = recordBase then some r.desc[45]! else none

def winDiff (ram : Word → BitVec 8) (r : Rec) : List String := Id.run do
  let mut d := []
  for k in [0:16] do
    let a : Word := BitVec.ofNat 32 (recordBase + 192 + 4 * k)
    let v := ramRead ram a .w
    if v ≠ r.post[48 + k]! then d := d ++ [s!"mem[{a.toHex}] model {v.toHex} qemu {r.post[48 + k]!.toHex}"]
  return d

def msipDiff (r : Rec) (evs : List Event) : List String :=
  let w := (evs.filter (·.addr = 0x02000000)).getLast?.map (·.val)
  let v := (w.getD r.desc[37]!) &&& 1
  if v ≠ r.post[41]! then [s!"msip model {v.toHex} qemu {r.post[41]!.toHex}"] else []

def showDiff (d : List String) : String := String.intercalate "; " d

def verdict (r : Rec) : String := Id.run do
  let n := r.desc[40]!.toNat
  let status := r.post[0]!.toNat
  let cause := r.post[36]!.toNat
  let async := status = 2 ∧ cause ≥ 2^31
  let mut m : Machine := ⟨preCore r, preRam r⟩
  let mut evs : List Event := []
  let mut k := 0
  while k < n do
    if async ∧ m.core.pc = r.post[35]! then break
    match stepInstr B (img r) m (oracleFor r m) with
    | .ok c ram e => m := ⟨c, ram⟩; evs := evs ++ e; k := k + 1
    | .fault f =>
      if status = 1 then
        match f with
        | .unsupported why => return s!"DECLINE step {k}: {why}"
        | _ => return s!"MISMATCH step {k}: model {faultName f}, QEMU completed normally"
      if async then
        match f with
        | .unsupported why => return s!"DECLINE step {k}: {why} (QEMU took interrupt {cause % 2^31})"
        | _ => return s!"MISMATCH step {k}: model {faultName f}, QEMU interrupt {cause % 2^31}"
      if status ≠ 2 then return s!"MISMATCH QEMU record status {status}"
      let d := gprDiff m.core r ++
        (if m.core.pc ≠ r.post[35]! then [s!"faulting pc model {m.core.pc.toHex} qemu mepc {r.post[35]!.toHex}"] else [])
      match f with
      | .unsupported why =>
        -- Declining is fail-closed whatever the hardware does instead.
        return if d.isEmpty then s!"DECLINE step {k}: {why} (QEMU exception {cause})"
               else s!"MISMATCH step {k}: {showDiff d}"
      | _ =>
        if !faultMatches f cause then
          return s!"MISMATCH step {k}: model {faultName f}, QEMU exception {cause}"
        return if d.isEmpty then s!"AGREE-TRAP {cause} at step {k}" else s!"MISMATCH step {k}: {showDiff d}"
  if status = 1 then
    let d := (match postPc r with
        | some p => if m.core.pc ≠ p then [s!"pc model {m.core.pc.toHex} qemu {p.toHex}"] else []
        | none => [s!"unrecognized landing pad {r.post[38]!.toHex}"]) ++
      gprDiff m.core r ++ csrDiff m.core r true ++ winDiff m.ram r ++ msipDiff r evs
    return if d.isEmpty then s!"AGREE {n}" else s!"MISMATCH {showDiff d}"
  if async then
    if m.core.pc ≠ r.post[35]! then
      return s!"MISMATCH interrupt at qemu mepc {r.post[35]!.toHex}, model pc {m.core.pc.toHex} after {k} steps"
    let code := cause % 2^31
    if !irqEnabled m.core code then return s!"MISMATCH QEMU took interrupt {code}, model says not enabled"
    match takeIrq m.core code with
    | .done c =>
      let d := (if c.pc ≠ r.post[38]! then [s!"entry pc model {c.pc.toHex} qemu {r.post[38]!.toHex}"] else []) ++
        gprDiff c r ++ csrDiff c r false ++ winDiff m.ram r ++ msipDiff r evs
      return if d.isEmpty then s!"AGREE-IRQ {code} after {k} steps" else s!"MISMATCH {showDiff d}"
    | _ => return "MISMATCH interrupt entry faulted in the model"
  return s!"MISMATCH QEMU status {status} cause {cause}, model completed {k} steps"

end Review

def main (args : List String) : IO UInt32 := do
  let lines := (← IO.FS.lines args[0]!).toList
  let mut out := ""
  for line in lines do
    if line.isEmpty then continue
    match Review.parse line with
    | none => IO.eprintln s!"unparsable record: {line.take 40}"; return 2
    | some r => out := out ++ s!"{r.desc[42]!.toNat} {Review.verdict r}\n"
  IO.FS.writeFile args[1]! out
  return 0
