/-
Single-thread instruction semantics.

`action K c s` is what thread state `s` does next, as one of: an internal step,
a load (with a continuation that receives the bytes read), a store, `done`
(the thread executed `ret` or `exit`), or `fault`. Memory never appears here:
every interaction with global memory is a visible `load` or `store` with its
address and size, so locality and race freedom can be stated over actions
without re-deriving them from the instruction table.

Registers are 64 bits wide in the model. A 32-bit operation reads the low 32
bits of its operands and writes its result zero-extended; for a well-typed
kernel (32-bit registers are only used at 32-bit types) this is exactly PTX's
`.b32` register file. Arithmetic wraps (`add.u32 a b = (a + b) mod 2^32`).

Initial register contents are not fixed by this file: the launch takes them as
parameters, and the theorems quantify over all of them, so a kernel that reads
an uninitialised register cannot be proved correct by accident.
-/
import Ptx.Syntax
import Ptx.Semantics.Memory

namespace Ptx

structure Dim3 where
  x : BitVec 32
  y : BitVec 32
  z : BitVec 32
  deriving Repr, DecidableEq, Inhabited

def Dim3.get (v : Dim3) : Dim → BitVec 32
  | .x => v.x | .y => v.y | .z => v.z

/-- What one thread can observe of its launch: its indices, the launch shape
and the raw bits of the kernel parameters (`.u32` parameters zero-extended). -/
structure Ctx where
  tid : Dim3
  ntid : Dim3
  ctaid : Dim3
  nctaid : Dim3
  params : String → Val

def Ctx.sreg (c : Ctx) : Sreg → BitVec 32
  | .tid d => c.tid.get d
  | .ntid d => c.ntid.get d
  | .ctaid d => c.ctaid.get d
  | .nctaid d => c.nctaid.get d

structure TState where
  pc : Nat
  r : String → Val
  p : String → Bool

def upd {α : Type} (f : String → α) (k : String) (v : α) : String → α :=
  fun x => if x = k then v else f x

@[simp] theorem upd_same {α} (f : String → α) (k : String) (v : α) : upd f k v k = v := by
  simp [upd]

theorem upd_other {α} (f : String → α) {k x : String} (v : α) (h : x ≠ k) :
    upd f k v x = f x := by
  simp [upd, h]

def lo32 (v : Val) : BitVec 32 := v.setWidth 32
def ext32 (v : BitVec 32) : Val := v.setWidth 64

/-- Write register `d` and fall through. -/
def TState.set (s : TState) (d : String) (v : Val) : TState :=
  { s with r := upd s.r d v, pc := s.pc + 1 }

def TState.setp (s : TState) (d : String) (v : Bool) : TState :=
  { s with p := upd s.p d v, pc := s.pc + 1 }

def TState.skip (s : TState) : TState := { s with pc := s.pc + 1 }

/-- An immediate is read at the instruction's width (two's complement). -/
def opVal (c : Ctx) (s : TState) : Operand → Val
  | .reg r => s.r r
  | .imm v => BitVec.ofInt 64 v
  | .sreg x => ext32 (c.sreg x)

/-- Result of a width-polymorphic operation, zero-extended into a register. -/
def atWidth (w : Width) (f : (n : Nat) → BitVec n → BitVec n → BitVec n) (a b : Val) : Val :=
  match w with
  | .w32 => ext32 (f 32 (lo32 a) (lo32 b))
  | .w64 => f 64 a b

def shiftBy (w : Width) (f : (n : Nat) → BitVec n → Nat → BitVec n) (a b : Val) : Val :=
  match w with
  | .w32 => ext32 (f 32 (lo32 a) (lo32 b).toNat)
  | .w64 => f 64 a (lo32 b).toNat

/-- `setp.c.t a b`. Ordered comparisons on `.b` types are not PTX (`none`). -/
def compare (c : CmpOp) (t : Ty) (a b : Val) : Option Bool :=
  let go {n : Nat} (x y : BitVec n) : Option Bool :=
    match c, t.signed, t with
    | .eq, _, _ => some (x == y)
    | .ne, _, _ => some (x != y)
    | _, _, .b32 | _, _, .b64 | _, _, .pred => none
    | .lt, true, _ => some (x.slt y)
    | .le, true, _ => some (x.sle y)
    | .gt, true, _ => some (y.slt x)
    | .ge, true, _ => some (y.sle x)
    | .lt, false, _ | .lo, _, _ => some (x.ult y)
    | .le, false, _ | .ls, _, _ => some (x.ule y)
    | .gt, false, _ | .hi, _, _ => some (y.ult x)
    | .ge, false, _ | .hs, _, _ => some (y.ule x)
  match t.width with
  | .w32 => go (lo32 a) (lo32 b)
  | .w64 => go a b

/-- `cvt.dt.st` between integer types: extend by the source's signedness,
or truncate. -/
def convert (dt st : Ty) (a : Val) : Val :=
  match st.width, dt.width with
  | .w32, .w32 => ext32 (lo32 a)
  | .w64, .w64 => a
  | .w64, .w32 => ext32 (lo32 a)
  | .w32, .w64 => if st.signed then (lo32 a).signExtend 64 else ext32 (lo32 a)

def Ty.size : Ty → Size
  | t => match t.width with | .w32 => .b4 | .w64 => .b8

/-- Truncate a value to the width of `t` (a register write of type `t`). -/
def fit (t : Ty) (v : Val) : Val :=
  match t.width with
  | .w32 => ext32 (lo32 v)
  | .w64 => v

inductive Action where
  | next (s : TState)
  | load (a : Addr) (sz : Size) (k : Val → TState)
  | store (a : Addr) (sz : Size) (v : Val) (s : TState)
  | done
  | fault

def jump (K : Kernel) (s : TState) (l : String) : Action :=
  match K.label? l with
  | some pc => .next { s with pc := pc }
  | none => .fault

/-- The effect of one (unguarded) instruction. -/
def exec (K : Kernel) (c : Ctx) (s : TState) : Instr → Action
  | .add t d a b => .next (s.set d (atWidth t.width (fun _ x y => x + y) (opVal c s a) (opVal c s b)))
  | .sub t d a b => .next (s.set d (atWidth t.width (fun _ x y => x - y) (opVal c s a) (opVal c s b)))
  | .mulLo t d a b => .next (s.set d (atWidth t.width (fun _ x y => x * y) (opVal c s a) (opVal c s b)))
  | .mulWide t d a b =>
    match t with
    | .u32 => .next (s.set d (ext32 (lo32 (opVal c s a)) * ext32 (lo32 (opVal c s b))))
    | .s32 => .next (s.set d ((lo32 (opVal c s a)).signExtend 64 * (lo32 (opVal c s b)).signExtend 64))
    | _ => .fault
  | .madLo t d a b e =>
    .next (s.set d (atWidth t.width (fun _ x y => x + y)
      (atWidth t.width (fun _ x y => x * y) (opVal c s a) (opVal c s b)) (opVal c s e)))
  | .and t d a b => .next (s.set d (atWidth t.width (fun _ x y => x &&& y) (opVal c s a) (opVal c s b)))
  | .or t d a b => .next (s.set d (atWidth t.width (fun _ x y => x ||| y) (opVal c s a) (opVal c s b)))
  | .xor t d a b => .next (s.set d (atWidth t.width (fun _ x y => x ^^^ y) (opVal c s a) (opVal c s b)))
  | .not t d a => .next (s.set d (fit t (~~~ (opVal c s a))))
  | .shl t d a b => .next (s.set d (shiftBy t.width (fun _ x n => x <<< n) (opVal c s a) (opVal c s b)))
  | .shr t d a b =>
    if t.signed then .next (s.set d (shiftBy t.width (fun _ x n => x.sshiftRight n) (opVal c s a) (opVal c s b)))
    else .next (s.set d (shiftBy t.width (fun _ x n => x >>> n) (opVal c s a) (opVal c s b)))
  | .mov t d a => .next (s.set d (fit t (opVal c s a)))
  | .setp op t p a b =>
    match compare op t (opVal c s a) (opVal c s b) with
    | some v => .next (s.setp p v)
    | none => .fault
  | .selp t d a b p => .next (s.set d (fit t (if s.p p then opVal c s a else opVal c s b)))
  | .cvt dt st d a => .next (s.set d (convert dt st (opVal c s a)))
  | .cvtaGlobal d a => .next (s.set d (opVal c s a))
  | .ld .param t d (.param n 0) => .next (s.set d (fit t (c.params n)))
  | .ld .global t d (.reg r off) =>
    .load (s.r r + BitVec.ofInt 64 off) t.size (fun v => s.set d v)
  | .st .global t (.reg r off) v =>
    .store (s.r r + BitVec.ofInt 64 off) t.size (opVal c s v) s.skip
  | .ld .. | .st .. => .fault
  | .bra _ l => jump K s l
  | .ret | .exit => .done

def guardHolds (s : TState) : Option Guard → Bool
  | none => true
  | some g => s.p g.pred != g.neg

/-- The next action of thread state `s`. Falling off the end of the body is a
fault: a kernel must end every path with `ret` or `exit`. -/
def action (K : Kernel) (c : Ctx) (s : TState) : Action :=
  match K.body[s.pc]? with
  | none => .fault
  | some st => if guardHolds s st.guard then exec K c s st.instr else .next s.skip

/-- The memory access an action is about to make: address, size, is-write. -/
def Action.acc : Action → Option (Addr × Size × Bool)
  | .load a sz _ => some (a, sz, false)
  | .store a sz _ _ => some (a, sz, true)
  | _ => none

/-- Outcome of one step of a thread against memory. -/
inductive Res where
  | ok (s : TState) (m : Mem)
  | halted
  | fault

/-- One step of a thread with global memory `m` and allocations `al`. -/
def stepMem (K : Kernel) (al : List Region) (c : Ctx) (s : TState) (m : Mem) : Res :=
  match action K c s with
  | .next s' => .ok s' m
  | .load a sz k => if accessOk al a sz then .ok (k (rd m a sz)) m else .fault
  | .store a sz v s' => if accessOk al a sz then .ok s' (wr m a sz v) else .fault
  | .done => .halted
  | .fault => .fault

end Ptx
