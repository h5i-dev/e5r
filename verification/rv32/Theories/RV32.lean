import Std

/- A deliberately small RV32I execution environment. Word values are Nat modulo
   2^32; signed interpretation is explicit. Bytes outside a permitted mapping,
   misalignment, and declined encodings are errors. No instruction halts. -/
deriving instance DecidableEq for Except

namespace RV32

def modulus : Nat := 4294967296
def word (n : Nat) : Nat := n % modulus
def signed (n : Nat) (bits : Nat) : Int :=
  if n < 2^(bits-1) then n else (n : Int) - (2^bits : Nat)
def addSigned (a : Nat) (b : Int) : Nat := ((a : Int) + b) % modulus |>.toNat

def field (w lo width : Nat) : Nat := w / 2^lo % 2^width

structure Region where
  base : Nat
  bytes : List Nat
  read : Bool
  write : Bool
  exec : Bool
  deriving Repr, DecidableEq

inductive Fault where
  | unmapped | permission | alignment | unsupported | malformed | fuel
  deriving Repr, DecidableEq

inductive Access where
  | load (addr : Nat)
  | store (addr value : Nat)
  deriving Repr, DecidableEq

structure State where
  pc : Nat
  regs : List Nat := List.replicate 32 0
  mem : List Region
  accesses : List Access := []
  deriving Repr, DecidableEq

def reg (s : State) (r : Nat) : Nat := if r = 0 then 0 else word (s.regs[r]?.getD 0)
def put (s : State) (r v : Nat) : State :=
  if r = 0 then s else { s with regs := s.regs.set r (word v) }

def byteAt (m : List Region) (a : Nat) (execute : Bool) : Except Fault Nat := do
  if a ≥ modulus then throw .unmapped
  let some r := m.find? (fun r => r.base ≤ a && a - r.base < r.bytes.length)
    | throw .unmapped
  if !(if execute then r.exec else r.read) then throw .permission
  let some b := r.bytes[a-r.base]? | throw .unmapped
  if b ≥ 256 then throw .malformed
  return b

def readWord (m : List Region) (a : Nat) (execute := false) : Except Fault Nat := do
  if a % 4 != 0 then throw .alignment
  let b0 ← byteAt m a execute
  let b1 ← byteAt m (a+1) execute
  let b2 ← byteAt m (a+2) execute
  let b3 ← byteAt m (a+3) execute
  return b0 + 256*b1 + 65536*b2 + 16777216*b3

def writeByte (m : List Region) (a b : Nat) : Except Fault (List Region) := do
  if a ≥ modulus then throw .unmapped
  match m with
  | [] => throw .unmapped
  | r :: rs =>
    if r.base ≤ a && a-r.base < r.bytes.length then
      if !r.write then throw .permission
      return { r with bytes := r.bytes.set (a-r.base) (b % 256) } :: rs
    else return r :: (← writeByte rs a b)

def writeWord (m : List Region) (a v : Nat) : Except Fault (List Region) := do
  if a % 4 != 0 then throw .alignment
  let m ← writeByte m a v
  let m ← writeByte m (a+1) (v/256)
  let m ← writeByte m (a+2) (v/65536)
  writeByte m (a+3) (v/16777216)

def branchImm (w : Nat) : Int :=
  signed (field w 31 1 * 4096 + field w 7 1 * 2048 +
    field w 25 6 * 32 + field w 8 4 * 2) 13

def jumpImm (w : Nat) : Int :=
  signed (field w 31 1 * 1048576 + field w 12 8 * 4096 +
    field w 20 1 * 2048 + field w 21 10 * 2) 21

def target (s : State) (pc : Nat) : Except Fault State :=
  if pc % 4 = 0 then .ok { s with pc := pc } else .error .alignment

/- Decode the fetched word here, not an exporter-supplied instruction AST.
   The whitelist is LUI, AUIPC, ADDI, ADD, SUB, all six base branches, LW, SW,
   JAL and JALR. Everything else (including M/C/CSR/ECALL) is declined. -/
def step (s : State) : Except Fault State := do
  let w ← readWord s.mem s.pc true
  let op := field w 0 7
  let rd := field w 7 5
  let f3 := field w 12 3
  let rs1 := field w 15 5
  let rs2 := field w 20 5
  let f7 := field w 25 7
  let a := reg s rs1
  let b := reg s rs2
  let imm := signed (field w 20 12) 12
  let next := { s with pc := word (s.pc+4) }
  match op with
  | 55 => return put next rd (w / 4096 * 4096)
  | 23 => return put next rd (s.pc + w / 4096 * 4096)
  | 19 =>
    if f3 != 0 then throw .unsupported
    return put next rd (addSigned a imm)
  | 51 =>
    if f3 != 0 then throw .unsupported
    if f7 = 0 then return put next rd (a+b)
    else if f7 = 32 then return put next rd (addSigned a (-(b : Int)))
    else throw .unsupported
  | 99 =>
    let take ← match f3 with
      | 0 => pure (a == b)
      | 1 => pure (a != b)
      | 4 => pure (signed a 32 < signed b 32)
      | 5 => pure (signed a 32 ≥ signed b 32)
      | 6 => pure (a < b)
      | 7 => pure (a ≥ b)
      | _ => throw .unsupported
    if take then target s (addSigned s.pc (branchImm w)) else pure next
  | 3 =>
    if f3 != 2 then throw .unsupported
    let addr := addSigned a imm
    let v ← readWord s.mem addr
    return put { next with accesses := s.accesses ++ [.load addr] } rd v
  | 35 =>
    if f3 != 2 then throw .unsupported
    let offset := signed (field w 25 7 * 32 + field w 7 5) 12
    let addr := addSigned a offset
    let mem ← writeWord s.mem addr b
    return { next with mem := mem, accesses := s.accesses ++ [.store addr b] }
  | 111 => target (put s rd (word (s.pc+4))) (addSigned s.pc (jumpImm w))
  | 103 =>
    if f3 != 0 then throw .unsupported
    target (put s rd (word (s.pc+4))) (addSigned a imm / 2 * 2)
  | _ => throw .unsupported

/- Reaching an explicit observation boundary is success, never a fault or
   exhausted fuel. The result records how many instruction transitions occurred. -/
def reach : Nat → Nat → State → Except Fault (Nat × State)
  | 0, _, _ => .error .fuel
  | n+1, stop, s => do
    if s.pc = stop then return (0, s)
    let s' ← step s
    let (k, final) ← reach n stop s'
    return (k+1, final)

end RV32
