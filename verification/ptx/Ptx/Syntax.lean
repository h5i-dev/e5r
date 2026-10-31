/-
PTX abstract syntax for the supported subset.

One constructor per supported instruction form. Register, parameter and label
names are kept as the strings written in the `.ptx` file, so a generated
`Kernel` value reads like the source it came from. `crates/e5r-ptx` produces
these values; it is untrusted, and its output is checked by a token-level
round trip against the original file (docs/verification-ptx.md, "Parser").

Anything not listed here is refused by the parser, not approximated.
-/
namespace Ptx

/-- Scalar types of the subset. `pred` is only used by `.reg .pred`
declarations; predicate registers live in their own file. -/
inductive Ty where
  | u32 | s32 | b32 | u64 | s64 | b64 | pred
  deriving Repr, DecidableEq, Inhabited

/-- Operand width of a data type. -/
inductive Width where
  | w32 | w64
  deriving Repr, DecidableEq, Inhabited

def Ty.width : Ty → Width
  | .u64 | .s64 | .b64 => .w64
  | _ => .w32

def Ty.signed : Ty → Bool
  | .s32 | .s64 => true
  | _ => false

inductive Dim where
  | x | y | z
  deriving Repr, DecidableEq, Inhabited

/-- Special registers of the subset: `%tid`, `%ntid`, `%ctaid`, `%nctaid`. -/
inductive Sreg where
  | tid (d : Dim) | ntid (d : Dim) | ctaid (d : Dim) | nctaid (d : Dim)
  deriving Repr, DecidableEq, Inhabited

inductive Operand where
  | reg (r : String)
  | imm (v : Int)
  | sreg (s : Sreg)
  deriving Repr, DecidableEq, Inhabited

/-- `[%rd8]`, `[%rd8+4]` or `[name]` (a kernel parameter). -/
inductive Address where
  | reg (r : String) (off : Int)
  | param (name : String) (off : Int)
  deriving Repr, DecidableEq, Inhabited

/-- `setp` comparison operators. `lo ls hi hs` are the unsigned spellings;
`lt le gt ge` are signed or unsigned according to the type. -/
inductive CmpOp where
  | eq | ne | lt | le | gt | ge | lo | ls | hi | hs
  deriving Repr, DecidableEq, Inhabited

inductive Space where
  | global | param
  deriving Repr, DecidableEq, Inhabited

inductive Instr where
  | add (t : Ty) (d : String) (a b : Operand)
  | sub (t : Ty) (d : String) (a b : Operand)
  | mulLo (t : Ty) (d : String) (a b : Operand)
  /-- `mul.wide.{u32,s32}`: 32 x 32 -> 64. `t` is the source type. -/
  | mulWide (t : Ty) (d : String) (a b : Operand)
  | madLo (t : Ty) (d : String) (a b c : Operand)
  | and (t : Ty) (d : String) (a b : Operand)
  | or (t : Ty) (d : String) (a b : Operand)
  | xor (t : Ty) (d : String) (a b : Operand)
  | not (t : Ty) (d : String) (a : Operand)
  | shl (t : Ty) (d : String) (a b : Operand)
  | shr (t : Ty) (d : String) (a b : Operand)
  | mov (t : Ty) (d : String) (a : Operand)
  | setp (c : CmpOp) (t : Ty) (p : String) (a b : Operand)
  | selp (t : Ty) (d : String) (a b : Operand) (p : String)
  /-- `cvt.dt.st`: integer conversion (no rounding modifiers in the subset). -/
  | cvt (dt st : Ty) (d : String) (a : Operand)
  /-- `cvta.to.global.u64`. -/
  | cvtaGlobal (d : String) (a : Operand)
  | ld (sp : Space) (t : Ty) (d : String) (a : Address)
  | st (sp : Space) (t : Ty) (a : Address) (v : Operand)
  /-- `bra` or `bra.uni` (same semantics in the single-thread view). -/
  | bra (uni : Bool) (label : String)
  | ret
  | exit
  deriving Repr, DecidableEq, Inhabited

/-- `@%p` (`neg = false`) or `@!%p` (`neg = true`). -/
structure Guard where
  pred : String
  neg : Bool
  deriving Repr, DecidableEq, Inhabited

structure Stmt where
  guard : Option Guard
  instr : Instr
  deriving Repr, DecidableEq, Inhabited

/-- `.reg .t name<n>;` (`count = some n`) or `.reg .t name;`. -/
structure RegDecl where
  ty : Ty
  name : String
  count : Option Nat
  deriving Repr, DecidableEq, Inhabited

/-- One `.entry` kernel. `labels` maps a label to the index of the statement
that follows it. -/
structure Kernel where
  name : String
  params : List (String × Ty)
  regs : List RegDecl
  body : List Stmt
  labels : List (String × Nat)
  deriving Repr, Inhabited

/-- Module header (`.version`, `.target`, `.address_size`) and its kernels. -/
structure Module where
  version : String
  target : String
  addressSize : Nat
  kernels : List Kernel
  deriving Repr, Inhabited

def lookupLabel : List (String × Nat) → String → Option Nat
  | [], _ => none
  | (k, v) :: t, l => if k = l then some v else lookupLabel t l

def Kernel.label? (k : Kernel) (l : String) : Option Nat := lookupLabel k.labels l

end Ptx
