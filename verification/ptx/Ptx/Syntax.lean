/-
PTX abstract syntax for the supported subset.

One constructor per supported instruction form. Register, parameter and label
names are kept as the strings written in the `.ptx` file, so a generated
`Kernel` value reads like the source it came from. `crates/e5r-ptx` produces
these values; it is untrusted, and its output is checked by a token-level
round trip against the original file (docs/verification/ptx.md, "Parser").

Anything not listed here is refused by the parser, not approximated.
-/
import Ptx.Semantics.Float

namespace Ptx
open Ptx.Fp (RMode FCmp)

/-- Scalar types of the subset. `pred` is only used by `.reg .pred`
declarations; predicate registers live in their own file. -/
inductive Ty where
  | u32 | s32 | b32 | u64 | s64 | b64 | pred | f32 | f64
  deriving Repr, DecidableEq, Inhabited

/-- Operand width of a data type. -/
inductive Width where
  | w32 | w64
  deriving Repr, DecidableEq, Inhabited

def Ty.width : Ty → Width
  | .u64 | .s64 | .b64 | .f64 => .w64
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
  /-- The address of a `.shared` variable (`mov.u32 %r1, sdata`). -/
  | sym (name : String)
  deriving Repr, DecidableEq, Inhabited

/-- `[%rd8]`, `[%rd8+4]` or `[name]`: a kernel parameter in `ld.param`, a
`.shared` variable in a shared-memory access. -/
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
  | global | param | shared
  deriving Repr, DecidableEq, Inhabited

/-- Operations of `atom` and `red` (`cas` is its own instruction). -/
inductive AtomOp where
  | add | min | max | exch | and | or | xor
  deriving Repr, DecidableEq, Inhabited

inductive FBin where
  | add | sub | mul | div
  deriving Repr, DecidableEq, Inhabited

/-- The rounding of a `cvt`: none (exact widening), floating-point
(`.rn .rz .rm .rp`) or integer (`.rni .rzi .rmi .rpi`). -/
inductive CvtRnd where
  | none
  | f (m : RMode)
  | i (m : RMode)
  deriving Repr, DecidableEq, Inhabited

inductive Instr where
  /-- `or.pred d, a, b`: Boolean OR of predicate registers. -/
  | por (d a b : String)
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
  | bfi32 (d : String) (a b : Operand) (pos len : Nat)
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
  /-- `atom.sp.op.t d, [a], b`: `d` gets the old value. -/
  | atom (sp : Space) (op : AtomOp) (t : Ty) (d : String) (a : Address) (b : Operand)
  /-- `atom.sp.cas.t d, [a], b, c`: store `c` if the old value is `b`. -/
  | cas (sp : Space) (t : Ty) (d : String) (a : Address) (b c : Operand)
  /-- `red.sp.op.t [a], b`: an atomic without a result. -/
  | red (sp : Space) (op : AtomOp) (t : Ty) (a : Address) (b : Operand)
  /-- `bar.sync 0`: wait until every thread of the CTA is at this barrier. -/
  | bar
  /-- `add sub mul div` on `.f32`/`.f64` with a rounding modifier
  (`Ptx/Semantics/Float.lean`); `.sat` only on `.f32` add, sub, mul. -/
  | fbin (op : FBin) (m : RMode) (ftz sat : Bool) (t : Ty) (d : String) (a b : Operand)
  | ffma (m : RMode) (ftz sat : Bool) (t : Ty) (d : String) (a b c : Operand)
  | fsqrt (m : RMode) (ftz : Bool) (t : Ty) (d : String) (a : Operand)
  | frcp (m : RMode) (ftz : Bool) (t : Ty) (d : String) (a : Operand)
  | fneg (ftz : Bool) (t : Ty) (d : String) (a : Operand)
  | fabs (ftz : Bool) (t : Ty) (d : String) (a : Operand)
  /-- `min`/`max{.ftz}{.NaN}`. -/
  | fminmax (isMax ftz nan : Bool) (t : Ty) (d : String) (a b : Operand)
  | fsetp (c : FCmp) (ftz : Bool) (t : Ty) (p : String) (a b : Operand)
  /-- `cvt{.rnd}{.ftz}{.sat}.dt.st` with a floating-point side. -/
  | cvtF (dt st : Ty) (r : CvtRnd) (ftz sat : Bool) (d : String) (a : Operand)
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

/-- `.shared .align a .b8 name[size];` (sizes in bytes). Where a variable is
placed in the CTA's shared window is up to ptxas; the launch carries the
placement and the theorems quantify over every valid one (`LayoutOk`). -/
structure SharedVar where
  name : String
  align : Nat
  size : Nat
  deriving Repr, DecidableEq, Inhabited

/-- An explicit `.param .align align .b8 name[size]` argument passed by value. -/
structure AggregateParam where
  name : String
  align : Nat
  size : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Original mixed scalar/aggregate ABI declaration order. -/
inductive ParamDecl where
  | scalar (index : Nat)
  | aggregate (index : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- One `.entry` kernel. `labels` maps a label to the index of the statement
that follows it. -/
structure Kernel where
  name : String
  params : List (String × Ty)
  aggregateParams : List AggregateParam := []
  paramOrder : List ParamDecl := []
  regs : List RegDecl
  shared : List SharedVar := []
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
