import E5R.Isa

/-
Machine state and the deterministic part of the semantics: what one
instruction other than ECALL does to the registers, the program counter and
memory. ECALL is given meaning by the environment model (E5R/Env.lean).

Part of the trusted base, together with E5R/Isa.lean and E5R/Env.lean. The
semantics follow the RISC-V unprivileged specification (version 20240411) for
RV64I, M, Zba and Zbb, restricted to user mode. Two profile choices narrow it
(docs/isa/profile.md, section 3):

* A misaligned load or store has no successor. The hardware may trap or may
  perform it slowly; the profile excludes it, so a proof has to show every
  access is naturally aligned.
* A jump or taken branch to an address that is not a multiple of 4 has no
  successor (instruction-address-misaligned, since C is not enabled).
-/
namespace E5R

/-- An observable interaction with the environment, in program order. -/
inductive Event
  | write (fd : Word) (bytes : List Byte)
  | read (fd : Word) (bytes : List Byte)
  | exit (code : Word)
  deriving DecidableEq, Repr

structure State where
  regs : Reg → Word
  pc : Word
  mem : Word → Byte
  /-- Events so far, oldest first. -/
  trace : List Event
  /-- `some c` once the process has called exit with status `c`. -/
  exit : Option Word

namespace State

/-- Register read; x0 always reads as zero. -/
def reg (s : State) (r : Reg) : Word := if r = 0 then 0 else s.regs r

def upd {α : Type} (f : Reg → α) (r : Reg) (v : α) : Reg → α :=
  fun x => if x = r then v else f x

/-- Register write; writes to x0 are discarded. -/
def setReg (s : State) (r : Reg) (v : Word) : State :=
  if r = 0 then s else { s with regs := upd s.regs r v }

def setPc (s : State) (p : Word) : State := { s with pc := p }
def setMem (s : State) (m : Word → Byte) : State := { s with mem := m }
def emit (s : State) (e : Event) : State := { s with trace := s.trace ++ [e] }
def halt (s : State) (code : Word) : State := { s with exit := some code }

end State

/-! ## Memory, little-endian -/

/-- `n` bytes from `a` as a natural number, least significant byte first. -/
def readLE (m : Word → Byte) (a : Word) : Nat → Nat
  | 0 => 0
  | n + 1 => (m a).toNat + 256 * readLE m (a + 1) n

/-- Store the low `n` bytes of `v` at `a`. -/
def writeLE (m : Word → Byte) (a : Word) (v : Nat) : Nat → (Word → Byte)
  | 0 => m
  | n + 1 =>
    let m' := writeLE m (a + 1) (v / 256) n
    fun x => if x = a then BitVec.ofNat 8 v else m' x

def read8 (m : Word → Byte) (a : Word) : Word := BitVec.ofNat 64 (readLE m a 1)
def read16 (m : Word → Byte) (a : Word) : Word := BitVec.ofNat 64 (readLE m a 2)
def read32 (m : Word → Byte) (a : Word) : Word := BitVec.ofNat 64 (readLE m a 4)
def read64 (m : Word → Byte) (a : Word) : Word := BitVec.ofNat 64 (readLE m a 8)

/-- `len` bytes from `a`, as a list. -/
def readBytes (m : Word → Byte) (a : Word) : Nat → List Byte
  | 0 => []
  | n + 1 => m a :: readBytes m (a + 1) n

/-- Store a list of bytes at `a`. -/
def writeBytes (m : Word → Byte) (a : Word) : List Byte → (Word → Byte)
  | [] => m
  | b :: bs =>
    let m' := writeBytes m (a + 1) bs
    fun x => if x = a then b else m' x

/-! ## Arithmetic helpers -/

/-- Sign-extend the low 32 bits. -/
def sext32 (x : Word) : Word := (x.setWidth 32).signExtend 64
def zext32 (x : Word) : Word := (x.setWidth 32).setWidth 64

def mulhSS (x y : Word) : Word := ((x.signExtend 128 * y.signExtend 128) >>> 64).setWidth 64
def mulhSU (x y : Word) : Word := ((x.signExtend 128 * y.setWidth 128) >>> 64).setWidth 64
def mulhUU (x y : Word) : Word := ((x.setWidth 128 * y.setWidth 128) >>> 64).setWidth 64

/-- RISC-V division: by zero gives all ones; `MIN / -1` gives `MIN`. -/
def rvDiv {n : Nat} (x y : BitVec n) : BitVec n := if y = 0 then BitVec.allOnes n else x.sdiv y
def rvDivu {n : Nat} (x y : BitVec n) : BitVec n := if y = 0 then BitVec.allOnes n else x / y
/-- RISC-V remainder: by zero gives the dividend; `MIN % -1` gives 0. -/
def rvRem {n : Nat} (x y : BitVec n) : BitVec n := if y = 0 then x else x.srem y
def rvRemu {n : Nat} (x y : BitVec n) : BitVec n := if y = 0 then x else x % y

/-- Apply a 32-bit operation to the low halves and sign-extend. -/
def w32 (f : BitVec 32 → BitVec 32 → BitVec 32) (x y : Word) : Word :=
  (f (x.setWidth 32) (y.setWidth 32)).signExtend 64

def bool64 (b : Bool) : Word := if b then 1 else 0

def orcb (x : Word) : Word :=
  BitVec.ofNat 64 <| (List.range 8).foldl
    (fun acc i => if (x >>> (8 * i)).setWidth 8 = 0 then acc else acc + 0xff * 256 ^ i) 0

def rev8 (x : Word) : Word :=
  BitVec.ofNat 64 <| (List.range 8).foldl
    (fun acc i => acc + ((x >>> (8 * i)).setWidth 8).toNat * 256 ^ (7 - i)) 0

def evalR : ROp → Word → Word → Word
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .sll, x, y => x <<< (y.toNat % 64)
  | .slt, x, y => bool64 (x.slt y)
  | .sltu, x, y => bool64 (x.ult y)
  | .xor, x, y => x ^^^ y
  | .srl, x, y => x >>> (y.toNat % 64)
  | .sra, x, y => x.sshiftRight (y.toNat % 64)
  | .or, x, y => x ||| y
  | .and, x, y => x &&& y
  | .mul, x, y => x * y
  | .mulh, x, y => mulhSS x y
  | .mulhsu, x, y => mulhSU x y
  | .mulhu, x, y => mulhUU x y
  | .div, x, y => rvDiv x y
  | .divu, x, y => rvDivu x y
  | .rem, x, y => rvRem x y
  | .remu, x, y => rvRemu x y
  | .sh1add, x, y => (x <<< 1) + y
  | .sh2add, x, y => (x <<< 2) + y
  | .sh3add, x, y => (x <<< 3) + y
  | .andn, x, y => x &&& ~~~y
  | .orn, x, y => x ||| ~~~y
  | .xnor, x, y => ~~~(x ^^^ y)
  | .max, x, y => if x.slt y then y else x
  | .maxu, x, y => if x.ult y then y else x
  | .min, x, y => if x.slt y then x else y
  | .minu, x, y => if x.ult y then x else y
  | .rol, x, y => x.rotateLeft (y.toNat % 64)
  | .ror, x, y => x.rotateRight (y.toNat % 64)

def evalRW : RWOp → Word → Word → Word
  | .addw, x, y => w32 (· + ·) x y
  | .subw, x, y => w32 (· - ·) x y
  | .sllw, x, y => w32 (fun a b => a <<< (b.toNat % 32)) x y
  | .srlw, x, y => w32 (fun a b => a >>> (b.toNat % 32)) x y
  | .sraw, x, y => w32 (fun a b => a.sshiftRight (b.toNat % 32)) x y
  | .mulw, x, y => w32 (· * ·) x y
  | .divw, x, y => w32 rvDiv x y
  | .divuw, x, y => w32 rvDivu x y
  | .remw, x, y => w32 rvRem x y
  | .remuw, x, y => w32 rvRemu x y
  | .adduw, x, y => zext32 x + y
  | .sh1adduw, x, y => (zext32 x <<< 1) + y
  | .sh2adduw, x, y => (zext32 x <<< 2) + y
  | .sh3adduw, x, y => (zext32 x <<< 3) + y
  | .rolw, x, y => w32 (fun a b => a.rotateLeft (b.toNat % 32)) x y
  | .rorw, x, y => w32 (fun a b => a.rotateRight (b.toNat % 32)) x y

def evalU : UOp → Word → Word
  | .clz, x => x.clz
  | .ctz, x => x.ctz
  | .cpop, x => x.cpop
  | .clzw, x => ((x.setWidth 32).clz).setWidth 64
  | .ctzw, x => ((x.setWidth 32).ctz).setWidth 64
  | .cpopw, x => ((x.setWidth 32).cpop).setWidth 64
  | .sextb, x => (x.setWidth 8).signExtend 64
  | .sexth, x => (x.setWidth 16).signExtend 64
  | .zexth, x => (x.setWidth 16).setWidth 64
  | .rev8, x => rev8 x
  | .orcb, x => orcb x

def evalI : IOp → Word → Word → Word
  | .addi, x, i => x + i
  | .slti, x, i => bool64 (x.slt i)
  | .sltiu, x, i => bool64 (x.ult i)
  | .xori, x, i => x ^^^ i
  | .ori, x, i => x ||| i
  | .andi, x, i => x &&& i

def evalSh : ShOp → Word → Nat → Word
  | .slli, x, n => x <<< n
  | .srli, x, n => x >>> n
  | .srai, x, n => x.sshiftRight n
  | .rori, x, n => x.rotateRight n
  | .slliuw, x, n => zext32 x <<< n

def evalShW : ShWOp → Word → Nat → Word
  | .slliw, x, n => ((x.setWidth 32) <<< n).signExtend 64
  | .srliw, x, n => ((x.setWidth 32) >>> n).signExtend 64
  | .sraiw, x, n => ((x.setWidth 32).sshiftRight n).signExtend 64
  | .roriw, x, n => ((x.setWidth 32).rotateRight n).signExtend 64

def evalBr : BrOp → Word → Word → Bool
  | .beq, x, y => x == y
  | .bne, x, y => x != y
  | .blt, x, y => x.slt y
  | .bge, x, y => !(x.slt y)
  | .bltu, x, y => x.ult y
  | .bgeu, x, y => !(x.ult y)

def LdOp.width : LdOp → Nat
  | .lb | .lbu => 1 | .lh | .lhu => 2 | .lw | .lwu => 4 | .ld => 8

def StOp.width : StOp → Nat
  | .sb => 1 | .sh => 2 | .sw => 4 | .sd => 8

/-- The loaded value, extended to 64 bits as the opcode says. -/
def loadVal (op : LdOp) (m : Word → Byte) (a : Word) : Word :=
  match op with
  | .lb => (BitVec.ofNat 8 (readLE m a 1)).signExtend 64
  | .lh => (BitVec.ofNat 16 (readLE m a 2)).signExtend 64
  | .lw => (BitVec.ofNat 32 (readLE m a 4)).signExtend 64
  | .ld => read64 m a
  | .lbu => read8 m a
  | .lhu => read16 m a
  | .lwu => read32 m a

def aligned (a : Word) (n : Nat) : Prop := a.toNat % n = 0

instance (a : Word) (n : Nat) : Decidable (aligned a n) := inferInstanceAs (Decidable (_ = _))

/-- The effective address of a load or store. -/
def ea (s : State) (rs1 : Reg) (off : BitVec 12) : Word := s.reg rs1 + off.signExtend 64

/-- Continue at `t`, which must be 4-byte aligned. -/
def jumpTo (s : State) (t : Word) : Option State :=
  if aligned t 4 then some (s.setPc t) else none

/-- One step of every instruction except ECALL, which returns `none` here. -/
def exec (i : Instr) (s : State) : Option State :=
  let next := s.pc + 4
  match i with
  | .lui rd imm => some ((s.setReg rd ((imm.setWidth 32 <<< 12).signExtend 64)).setPc next)
  | .auipc rd imm =>
    some ((s.setReg rd (s.pc + (imm.setWidth 32 <<< 12).signExtend 64)).setPc next)
  | .jal rd off => jumpTo (s.setReg rd next) (s.pc + off.signExtend 64)
  | .jalr rd rs1 off =>
    -- The target is computed from rs1 before rd is written (rd may equal rs1).
    let t := (s.reg rs1 + off.signExtend 64) &&& ~~~1
    jumpTo (s.setReg rd next) t
  | .branch op rs1 rs2 off =>
    if evalBr op (s.reg rs1) (s.reg rs2) then jumpTo s (s.pc + off.signExtend 64)
    else some (s.setPc next)
  | .load op rd rs1 off =>
    let a := ea s rs1 off
    if aligned a op.width then some ((s.setReg rd (loadVal op s.mem a)).setPc next)
    else none
  | .store op rs1 rs2 off =>
    let a := ea s rs1 off
    if aligned a op.width then
      some ((s.setMem (writeLE s.mem a (s.reg rs2).toNat op.width)).setPc next)
    else none
  | .iop op rd rs1 imm => some ((s.setReg rd (evalI op (s.reg rs1) (imm.signExtend 64))).setPc next)
  | .addiw rd rs1 imm =>
    some ((s.setReg rd (sext32 (s.reg rs1 + imm.signExtend 64))).setPc next)
  | .shift op rd rs1 sh => some ((s.setReg rd (evalSh op (s.reg rs1) sh.toNat)).setPc next)
  | .shiftw op rd rs1 sh => some ((s.setReg rd (evalShW op (s.reg rs1) sh.toNat)).setPc next)
  | .rop op rd rs1 rs2 => some ((s.setReg rd (evalR op (s.reg rs1) (s.reg rs2))).setPc next)
  | .rwop op rd rs1 rs2 => some ((s.setReg rd (evalRW op (s.reg rs1) (s.reg rs2))).setPc next)
  | .uop op rd rs1 => some ((s.setReg rd (evalU op (s.reg rs1))).setPc next)
  | .ecall => none

-- Rewritten by its equation lemmas only (simp [exec]), never unfolded by
-- unification; see E5R/Step.lean at `Reach.opt`.
attribute [irreducible] exec

end E5R

