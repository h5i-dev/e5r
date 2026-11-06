/-
Single-thread instruction semantics.

`action K c s` is what thread state `s` does next, as one of: an internal step,
a load (with a continuation that receives the bytes read), a store, an atomic
read-modify-write, a wait at `bar.sync`, `done` (the thread executed `ret` or
`exit`), or `fault`. Memory never appears here: every interaction with global
or shared memory is a visible action with its space, address and size, so
locality and race freedom can be stated over actions without re-deriving them
from the instruction table.

Registers are 64 bits wide in the model. An 8/16/32-bit operation reads the
low bits of its operands and writes its result zero-extended. Logic and
arithmetic require matching operand widths. The admitted integer ld/st/cvt
forms may use wider registers: the instruction type determines truncation
and conversion extension. Arithmetic wraps (`add.u32 a b = (a + b) mod 2^32`).

A shared-memory address is the value of its register (plus offset), as for
global memory. A 32-bit address register written by the kernel is
zero-extended, so this is its value; one with stray upper bits (never
written) points outside every shared variable and faults, where hardware
would use the low 32 bits. The model is stricter there, never more lenient.

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

/-- What one thread can observe of its launch: its indices, the launch shape,
the raw bits of the kernel parameters (`.u32` parameters zero-extended), and
the addresses of the kernel's `.shared` variables in the CTA's shared window. -/
structure TState where
  pc : Nat
  r : String → Val
  p : String → Bool

structure Ctx where
  tid : Dim3
  ntid : Dim3
  ctaid : Dim3
  nctaid : Dim3
  params : String → Val
  /-- Aggregate arguments retain all ABI bytes, independently of scalar bits. -/
  byteParams : String → Nat → BitVec 8 := fun _ _ => 0
  sym : String → Val := fun _ => 0
  /-- The NaN oracle (`Launch.nan`): the bits of a NaN result, from the
  state of the thread at the instruction. -/
  nan : TState → Val := fun _ => 0

def Ctx.sreg (c : Ctx) : Sreg → BitVec 32
  | .laneid => (c.tid.x + c.ntid.x * (c.tid.y + c.ntid.y * c.tid.z)) &&& 31
  | .tid d => c.tid.get d
  | .ntid d => c.ntid.get d
  | .ctaid d => c.ctaid.get d
  | .nctaid d => c.nctaid.get d

def upd {α : Type} (f : String → α) (k : String) (v : α) : String → α :=
  fun x => if x = k then v else f x

@[simp] theorem upd_same {α} (f : String → α) (k : String) (v : α) : upd f k v k = v := by
  simp [upd]

theorem upd_other {α} (f : String → α) {k x : String} (v : α) (h : x ≠ k) :
    upd f k v x = f x := by
  simp [upd, h]

def lo32 (v : Val) : BitVec 32 := v.setWidth 32
def ext32 (v : BitVec 32) : Val := v.setWidth 64

@[simp] theorem lo32_ext32 (v : BitVec 32) : lo32 (ext32 v) = v := by
  simp [lo32, ext32]

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
  | .sym n => c.sym n

/-- Result of a width-polymorphic operation, zero-extended into a register. -/
def atWidth (w : Width) (f : (n : Nat) → BitVec n → BitVec n → BitVec n) (a b : Val) : Val :=
  match w with
  | .w8 => (f 8 (a.setWidth 8) (b.setWidth 8)).setWidth 64
  | .w16 => (f 16 (a.setWidth 16) (b.setWidth 16)).setWidth 64
  | .w32 => ext32 (f 32 (lo32 a) (lo32 b))
  | .w64 => f 64 a b

/-- `shl`/`shr`: the shift amount is the unsigned 32-bit operand, and amounts
greater than the register width are clamped to the width (PTX ISA, `shl` and
`shr`). The clamp does not change the result of a `BitVec` shift; it is
written out so the definition reads like the ISA, and so that executing it
(the GPU differential test) does not build a 2^32-bit number. -/
def shiftBy (w : Width) (f : (n : Nat) → BitVec n → Nat → BitVec n) (a b : Val) : Val :=
  match w with
  | .w8 => (f 8 (a.setWidth 8) (min (lo32 b).toNat 8)).setWidth 64
  | .w16 => (f 16 (a.setWidth 16) (min (lo32 b).toNat 16)).setWidth 64
  | .w32 => ext32 (f 32 (lo32 a) (min (lo32 b).toNat 32))
  | .w64 => f 64 a (min (lo32 b).toNat 64)

/-- `setp.c.t a b`. Ordered comparisons on `.b` types are not PTX (`none`). -/
def cmpVal (c : CmpOp) (t : Ty) (a b : Val) : Option Bool :=
  let go {n : Nat} (x y : BitVec n) : Option Bool :=
    match c, t.signed, t with
    | _, _, .f32 | _, _, .f64 => none
    | .eq, _, _ => some (x == y)
    | .ne, _, _ => some (x != y)
    | _, _, .b16 | _, _, .b32 | _, _, .b64 | _, _, .pred => none
    | .lt, true, _ => some (x.slt y)
    | .le, true, _ => some (x.sle y)
    | .gt, true, _ => some (y.slt x)
    | .ge, true, _ => some (y.sle x)
    | .lt, false, _ | .lo, _, _ => some (x.ult y)
    | .le, false, _ | .ls, _, _ => some (x.ule y)
    | .gt, false, _ | .hi, _, _ => some (y.ult x)
    | .ge, false, _ | .hs, _, _ => some (y.ule x)
  match t.width with
  | .w8 => go (a.setWidth 8) (b.setWidth 8)
  | .w16 => go (a.setWidth 16) (b.setWidth 16)
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
  | _, .w8 => (a.setWidth 8).setWidth 64
  | _, .w16 => (a.setWidth 16).setWidth 64
  | .w8, .w32 => (a.setWidth 8).setWidth 64
  | .w8, .w64 => (a.setWidth 8).setWidth 64
  | .w16, .w32 =>
    if st.signed then ((a.setWidth 16).signExtend 32).setWidth 64
    else (a.setWidth 16).setWidth 64
  | .w16, .w64 =>
    if st.signed then (a.setWidth 16).signExtend 64 else (a.setWidth 16).setWidth 64

def Ty.size : Ty → Size
  | t => match t.width with | .w8 => .b1 | .w16 => .b2 | .w32 => .b4 | .w64 => .b8

/-- Truncate a value to the width of `t` (a register write of type `t`). -/
def fit (t : Ty) (v : Val) : Val :=
  match t.width with
  | .w8 => (v.setWidth 8).setWidth 64
  | .w16 => (v.setWidth 16).setWidth 64
  | .w32 => ext32 (lo32 v)
  | .w64 => v

/-- The new value an `atom`/`red` stores, from the old value and the operand,
at the instruction's width (`min`/`max` signed for `.s` types). -/
def atomVal (op : AtomOp) (t : Ty) (old b : Val) : Val :=
  match op with
  | .add => atWidth t.width (fun _ x y => x + y) old b
  | .and => atWidth t.width (fun _ x y => x &&& y) old b
  | .or => atWidth t.width (fun _ x y => x ||| y) old b
  | .xor => atWidth t.width (fun _ x y => x ^^^ y) old b
  | .exch => fit t b
  | .min => atWidth t.width (fun _ x y => if (if t.signed then x.sle y else x.ule y) then x else y) old b
  | .max => atWidth t.width (fun _ x y => if (if t.signed then y.sle x else y.ule x) then x else y) old b

/-- The two data spaces a thread accesses. -/
inductive Sp where
  | global | shared
  deriving Repr, DecidableEq, Inhabited

/-- What one thread sees: global memory and its CTA's shared memory. -/
structure Heap where
  g : Mem
  s : Mem

def Heap.at (h : Heap) : Sp → Mem
  | .global => h.g
  | .shared => h.s

def Heap.set (h : Heap) : Sp → Mem → Heap
  | .global, m => { h with g := m }
  | .shared, m => { h with s := m }

@[simp] theorem Heap.at_global (h : Heap) : h.at .global = h.g := rfl
@[simp] theorem Heap.at_shared (h : Heap) : h.at .shared = h.s := rfl
@[simp] theorem Heap.set_global (h : Heap) (m : Mem) : h.set .global m = { h with g := m } := rfl
@[simp] theorem Heap.set_shared (h : Heap) (m : Mem) : h.set .shared m = { h with s := m } := rfl

/-- The next thing a thread does. `atom sp a sz f k` reads the `sz` bytes at
`a`, stores `f old` there and continues with `k old`, as one indivisible
step. `bar` waits at `bar.sync` (the grid releases a whole CTA at once). -/
inductive Action where
  | next (s : TState)
  | load (sp : Sp) (a : Addr) (sz : Size) (k : Val → TState)
  | store (sp : Sp) (a : Addr) (sz : Size) (v : Val) (s : TState)
  | atom (sp : Sp) (a : Addr) (sz : Size) (f : Val → Val) (k : Val → TState)
  | bar
  | done
  | fault

def jump (K : Kernel) (s : TState) (l : String) : Action :=
  match K.label? l with
  | some pc => .next { s with pc := pc }
  | none => .fault

/-- The address of a data access: a register plus offset, or a shared
variable plus offset. A named address in global memory is not in the
subset. -/
def dataAddr (c : Ctx) (s : TState) (sp : Space) : Address → Option (Sp × Addr)
  | .reg r off =>
    match sp with
    | .global => some (.global, s.r r + BitVec.ofInt 64 off)
    | .shared => some (.shared, s.r r + BitVec.ofInt 64 off)
    | .param => none
  | .param n off =>
    match sp with
    | .shared => some (.shared, c.sym n + BitVec.ofInt 64 off)
    | _ => none

/-- An `atom`/`cas`/`red`: the access, the stored value and the result. -/
def atomic (c : Ctx) (s : TState) (sp : Space) (t : Ty) (a : Address) (f : Val → Val)
    (k : Val → TState) : Action :=
  match dataAddr c s sp a with
  | some (sp', x) => .atom sp' x t.size f k
  | none => .fault

/-- The format of a float type (`.f64`, else `.f32`). -/
def Ty.fmt : Ty → Fp.Fmt
  | .f64 => Fp.Fmt.f64
  | _ => Fp.Fmt.f32

/-- The bits of a float operand at the type's width. -/
def fbits (t : Ty) (v : Val) : Nat :=
  match t.width with
  | .w8 => (v.setWidth 8).toNat
  | .w16 => (v.setWidth 16).toNat
  | .w32 => (lo32 v).toNat
  | .w64 => v.toNat

/-- The register value of a float result; a NaN result takes its bits from
the oracle, forced to be a NaN of the format. -/
def fres (c : Ctx) (s : TState) (t : Ty) : Option Nat → Val
  | some x => BitVec.ofNat 64 x
  | none =>
    let v := fbits t (c.nan s)
    BitVec.ofNat 64 (if t.fmt.isNaN v then v else t.fmt.qnan)

/-- The integer an operand of an integer type holds. -/
def intOf (t : Ty) (v : Val) : Int :=
  match t.width, t.signed with
  | .w8, true => (v.setWidth 8).toInt
  | .w8, false => (v.setWidth 8).toNat
  | .w16, true => (v.setWidth 16).toInt
  | .w16, false => (v.setWidth 16).toNat
  | .w32, true => (lo32 v).toInt
  | .w32, false => (lo32 v).toNat
  | .w64, true => v.toInt
  | .w64, false => v.toNat

def Ty.isFloat : Ty → Bool
  | .f32 | .f64 => true
  | _ => false

/-- `cvt` with a floating-point side (`Fp.toInt`, `Fp.ofInt`,
`Fp.roundIntegral`, `Fp.convertF`). Combinations PTX does not define are
refused by the parser and fault here. -/
def cvtFloat (c : Ctx) (s : TState) (dt st : Ty) (r : CvtRnd) (ftz sat : Bool) (a : Val) : Option Val :=
  match dt.isFloat, st.isFloat, r with
  | false, true, .i m =>
    let w := match dt.width with | .w8 => 8 | .w16 => 16 | .w32 => 32 | .w64 => 64
    let v := Fp.toInt st.fmt m (ftz && st = .f32) dt.signed w (fbits st a)
    some (fit dt (BitVec.ofNat 64 v))
  | true, false, .f m =>
    some (fres c s dt (dt.fmt.sat sat (some (Fp.ofInt dt.fmt m false (intOf st a)))))
  | true, true, .i m =>
    if dt = st then some (fres c s dt (dt.fmt.sat sat (Fp.roundIntegral dt.fmt m (ftz && dt = .f32) (fbits st a))))
    else none
  | true, true, .f m =>
    if dt = .f32 ∧ st = .f64 then some (fres c s dt (Fp.convertF dt.fmt st.fmt m ftz sat (fbits st a)))
    else none
  | true, true, .none =>
    if dt = .f64 ∧ st = .f32 then some (fres c s dt (Fp.convertF dt.fmt st.fmt .rn ftz sat (fbits st a)))
    else none
  | _, _, _ => none

/-- Immediate bfi.b32; the frontend admits position+length <= 32.
NVIDIA PTX ISA 9.2, bfi: copy low source bits into the
clipped destination interval, preserving all other bits. -/
def bfi32 (a b : BitVec 32) (pos len : Nat) : BitVec 32 :=
  let mask := ((-1 : BitVec 32) >>> (32 - min len 32)) <<< pos
  ((a <<< pos) &&& mask) ||| (b &&& ~~~mask)

/-- Little-endian bytes at a natural parameter offset, without address wrapping. -/
def paramRead32 (bytes : Nat → BitVec 8) (off : Nat) : BitVec 32 :=
  bytes (off + 3) ++ bytes (off + 2) ++ bytes (off + 1) ++ bytes off

def paramRead (bytes : Nat → BitVec 8) (off : Nat) : Size → Val
  | .b1 => (bytes off).setWidth 64
  | .b2 => (bytes (off + 1) ++ bytes off).setWidth 64
  | .b4 => (paramRead32 bytes off).setWidth 64
  | .b8 => paramRead32 bytes (off + 4) ++ paramRead32 bytes off

/-- Read-only aggregate loads have declaration bounds and natural alignment.
The scalar case retains its original bits and zero-offset behavior. -/
def paramValue (K : Kernel) (c : Ctx) (t : Ty) (name : String) (off : Int) : Option Val :=
  match K.aggregateParams.find? (fun p => p.name == name) with
  | none => if off = 0 then some (fit t (c.params name)) else none
  | some p =>
    if 0 ≤ off ∧ off.toNat + t.size.bytes ≤ p.size ∧ t.size.bytes ≤ p.align ∧
        p.align % t.size.bytes = 0 ∧ off.toNat % t.size.bytes = 0 then
      some (paramRead (c.byteParams name) off.toNat t.size)
    else none

@[simp] theorem paramValue_scalar (K : Kernel) (c : Ctx) (t : Ty) (name : String)
    (h : K.aggregateParams = []) :
    paramValue K c t name 0 = some (fit t (c.params name)) := by
  simp [paramValue, h]

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
  | .por d a b => .next (s.setp d (s.p a || s.p b))
  | .xor t d a b => .next (s.set d (atWidth t.width (fun _ x y => x ^^^ y) (opVal c s a) (opVal c s b)))
  | .not t d a => .next (s.set d (fit t (~~~ (opVal c s a))))
  | .shl t d a b => .next (s.set d (shiftBy t.width (fun _ x n => x <<< n) (opVal c s a) (opVal c s b)))
  | .shr t d a b =>
    if t.signed then .next (s.set d (shiftBy t.width (fun _ x n => x.sshiftRight n) (opVal c s a) (opVal c s b)))
    else .next (s.set d (shiftBy t.width (fun _ x n => x >>> n) (opVal c s a) (opVal c s b)))
  | .mov t d a => .next (s.set d (fit t (opVal c s a)))
  | .setp op t p a b =>
    match cmpVal op t (opVal c s a) (opVal c s b) with
    | some v => .next (s.setp p v)
    | none => .fault
  | .bfi32 d a b pos len =>
    .next (s.set d (ext32 (bfi32 (lo32 (opVal c s a)) (lo32 (opVal c s b)) pos len)))
  | .selp t d a b p => .next (s.set d (fit t (if s.p p then opVal c s a else opVal c s b)))
  | .cvt dt st d a => .next (s.set d (convert dt st (opVal c s a)))
  | .cvtaGlobal d a => .next (s.set d (opVal c s a))
  | .ld .param t d (.param n 0) =>
    match K.aggregateParams with
    | [] => .next (s.set d (fit t (c.params n)))
    | _ =>
      match paramValue K c t n 0 with
      | some v => .next (s.set d v)
      | none => .fault
  | .ld .param t d (.param n off) =>
    match paramValue K c t n off with
    | some v => .next (s.set d v)
    | none => .fault
  | .ld .param .. | .st .param .. => .fault
  | .ld sp t d a =>
    match dataAddr c s sp a with
    | some (sp', x) => .load sp' x t.size (fun v => s.set d v)
    | none => .fault
  | .st sp t a v =>
    match dataAddr c s sp a with
    | some (sp', x) => .store sp' x t.size (opVal c s v) s.skip
    | none => .fault
  | .atom sp op t d a b =>
    atomic c s sp t a (fun old => atomVal op t old (opVal c s b)) (fun old => s.set d (fit t old))
  | .cas sp t d a b e =>
    atomic c s sp t a (fun old => if fit t old = fit t (opVal c s b) then opVal c s e else old)
      (fun old => s.set d (fit t old))
  | .red sp op t a b => atomic c s sp t a (fun old => atomVal op t old (opVal c s b)) (fun _ => s.skip)
  -- Warp and NC instructions require Ptx.Warp's launch-wide obligations.
  | .warpBar | .ldGlobalNCF32 .. => .fault
  -- Volatile accesses remain individual memory actions in this SC model.
  | .ldVolatileShared32 d a =>
    match dataAddr c s .shared a with
    | some (.shared, x) => .load .shared x .b4 (fun v => s.set d v)
    | _ => .fault
  | .stVolatileShared32 a v =>
    match dataAddr c s .shared a with
    | some (.shared, x) => .store .shared x .b4 (opVal c s v) s.skip
    | _ => .fault
  | .bar => .bar
  | .bra _ l => jump K s l
  | .ret | .exit => .done
  | .clz32 d a => .next (s.set d (ext32 (lo32 (opVal c s a)).clz))
  | .minS32 d a b =>
    let x := lo32 (opVal c s a)
    let y := lo32 (opVal c s b)
    .next (s.set d (ext32 (if x.slt y then x else y)))
  | .fbinDefault op ftz sat t d a b =>
    let F := t.fmt
    let x := fbits t (opVal c s a)
    let y := fbits t (opVal c s b)
    let r := match op with
      | .add => Fp.fadd F .rn ftz sat x y
      | .sub => Fp.fsub F .rn ftz sat x y
      | .mul => Fp.fmul F .rn ftz sat x y
      | .div => Fp.fdiv F .rn ftz x y
    .next (s.set d (fres c s t r))
  | .fbin op m ftz sat t d a b =>
    let F := t.fmt
    let x := fbits t (opVal c s a)
    let y := fbits t (opVal c s b)
    let r := match op with
      | .add => Fp.fadd F m ftz sat x y
      | .sub => Fp.fsub F m ftz sat x y
      | .mul => Fp.fmul F m ftz sat x y
      | .div => Fp.fdiv F m ftz x y
    .next (s.set d (fres c s t r))
  | .ffma m ftz sat t d a b e =>
    .next (s.set d (fres c s t (Fp.ffma t.fmt m ftz sat (fbits t (opVal c s a)) (fbits t (opVal c s b))
      (fbits t (opVal c s e)))))
  | .fsqrt m ftz t d a => .next (s.set d (fres c s t (Fp.fsqrt t.fmt m ftz (fbits t (opVal c s a)))))
  | .frcp m ftz t d a => .next (s.set d (fres c s t (Fp.frcp t.fmt m ftz (fbits t (opVal c s a)))))
  | .fneg ftz t d a => .next (s.set d (fres c s t (Fp.fneg t.fmt ftz (fbits t (opVal c s a)))))
  | .fabs ftz t d a => .next (s.set d (fres c s t (Fp.fabs t.fmt ftz (fbits t (opVal c s a)))))
  | .fminmax mx ftz nan t d a b =>
    .next (s.set d (fres c s t (Fp.fminmax t.fmt mx ftz nan (fbits t (opVal c s a)) (fbits t (opVal c s b)))))
  | .fsetp op ftz t p a b => .next (s.setp p (Fp.fsetp t.fmt op ftz (fbits t (opVal c s a)) (fbits t (opVal c s b))))
  | .cvtF dt st r ftz sat d a =>
    match cvtFloat c s dt st r ftz sat (opVal c s a) with
    | some v => .next (s.set d v)
    | none => .fault

def guardHolds (s : TState) : Option Guard → Bool
  | none => true
  | some g => s.p g.pred != g.neg

/-- The next action of thread state `s`. Falling off the end of the body is a
fault: a kernel must end every path with `ret` or `exit`. -/
def action (K : Kernel) (c : Ctx) (s : TState) : Action :=
  match K.body[s.pc]? with
  | none => .fault
  | some st => if guardHolds s st.guard then exec K c s st.instr else .next s.skip

inductive AccKind where
  | read | write | atomic
  deriving Repr, DecidableEq, Inhabited

/-- A memory access: space, address, size, and whether it reads, writes, or
is an atomic read-modify-write. -/
structure Acc where
  sp : Sp
  a : Addr
  sz : Size
  kind : AccKind
  deriving Repr, DecidableEq, Inhabited

/-- The memory access an action is about to make. -/
def Action.acc : Action → Option Acc
  | .load sp a sz _ => some ⟨sp, a, sz, .read⟩
  | .store sp a sz _ _ => some ⟨sp, a, sz, .write⟩
  | .atom sp a sz _ _ => some ⟨sp, a, sz, .atomic⟩
  | _ => none

/-- Outcome of one step of a thread: it moved, it waits at a barrier, it has
finished, or it faulted. -/
inductive TRes where
  | ok (s : TState) (h : Heap)
  | wait
  | halted
  | fault

/-- One step of a thread against what it sees, with the allocations of each
space. -/
def tstep (K : Kernel) (al : Sp → List Region) (c : Ctx) (s : TState) (h : Heap) : TRes :=
  match action K c s with
  | .next s' => .ok s' h
  | .load sp a sz k => if accessOk (al sp) a sz then .ok (k (rd (h.at sp) a sz)) h else .fault
  | .store sp a sz v s' =>
    if accessOk (al sp) a sz then .ok s' (h.set sp (wr (h.at sp) a sz v)) else .fault
  | .atom sp a sz f k =>
    if accessOk (al sp) a sz then
      .ok (k (rd (h.at sp) a sz)) (h.set sp (wr (h.at sp) a sz (f (rd (h.at sp) a sz))))
    else .fault
  | .bar => .wait
  | .done => .halted
  | .fault => .fault

/-- Outcome of one step of a thread that only uses global memory. -/
inductive Res where
  | ok (s : TState) (m : Mem)
  | halted
  | fault

/-- One step of a thread with global memory `m` and allocations `al`, for the
global-only fragment the M1-M3 proofs use: shared accesses, atomics and
barriers are not steps here (they are `fault`), so a run of `stepMem`
never contains one. `tstep_of_stepMem` is the bridge to `tstep`. -/
def stepMem (K : Kernel) (al : List Region) (c : Ctx) (s : TState) (m : Mem) : Res :=
  match action K c s with
  | .next s' => .ok s' m
  | .load .global a sz k => if accessOk al a sz then .ok (k (rd m a sz)) m else .fault
  | .store .global a sz v s' => if accessOk al a sz then .ok s' (wr m a sz v) else .fault
  | .done => .halted
  | _ => .fault

theorem tstep_of_stepMem {K : Kernel} {al : Sp → List Region} {c : Ctx} {s s' : TState}
    {m m' sh : Mem} (h : stepMem K (al .global) c s m = .ok s' m') :
    tstep K al c s ⟨m, sh⟩ = .ok s' ⟨m', sh⟩ := by
  unfold stepMem at h; unfold tstep
  split at h
  · next hA => rw [hA]; cases h; rfl
  · next a sz k hA =>
    rw [hA]; split at h
    · next hok => cases h; simp [hok, Heap.at]
    · cases h
  · next a sz v s'' hA =>
    rw [hA]; split at h
    · next hok => cases h; simp [hok, Heap.at, Heap.set]
    · cases h
  · cases h
  · cases h

theorem tstep_halted_of_stepMem {K : Kernel} {al : Sp → List Region} {c : Ctx} {s : TState}
    {m sh : Mem} (h : stepMem K (al .global) c s m = .halted) : tstep K al c s ⟨m, sh⟩ = .halted := by
  unfold stepMem at h; unfold tstep
  split at h <;> (try split at h) <;> simp_all

end Ptx
