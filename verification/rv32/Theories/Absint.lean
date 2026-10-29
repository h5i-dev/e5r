/-
  Abstract interpretation of firmware binaries, as a certificate checker.

  Original e5r code, Apache-2.0.

  An analyzer (untrusted; `tools/Analyze.lean`) explores the binary and emits
  a certificate: a finite set of abstract nodes (an exact pc plus abstract
  registers, memory cells and CSRs), the successor nodes of each, a global
  invariant `G` over static RAM that holds whenever an interrupt can be
  taken, and the nodes of the interrupt handler, analyzed once relative to
  the interrupted registers. `check` re-runs the same transfer function on
  every node and verifies that each successor is covered. Its soundness
  (`Theories/AbsintSound.lean`) turns `check cert = true`, evaluated by the
  Lean kernel, into a theorem about every reachable machine.

  Everything here computes on `Nat`, so kernel evaluation stays cheap.
-/
import Theories.Platform

set_option linter.constructorNameAsVariable false

namespace E5R.AI
open E5R

def M32 : Nat := 4294967296
def maxVals : Nat := 24

/-! ## Abstract values -/

/-- A set of 32-bit values.

  * `vals l`: one of the listed values (`[]` is unreachable);
  * `rng lo hi`: an unsigned value in `[lo, hi]`;
  * `sym s off`: the interrupted machine's register `s` (32 = its pc) plus
    `off`, modulo 2^32. Only handler nodes use it. -/
inductive AV where
  | top
  | vals (l : List Nat)
  | rng (lo hi : Nat)
  | sym (s off : Nat)
  deriving Repr, DecidableEq, Inhabited

def ins (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x < y then x :: y :: ys else if x = y then y :: ys else y :: ins x ys

def norm (l : List Nat) : List Nat := l.foldr (fun x acc => ins (x % M32) acc) []

def lmin : List Nat → Nat
  | [] => 0
  | x :: xs => xs.foldl min x

def lmax : List Nat → Nat
  | [] => 0
  | x :: xs => xs.foldl max x

/-- A value set, widened to a range when it grows past `maxVals`. -/
def mkVals (l : List Nat) : AV :=
  let l := norm l
  if l.length ≤ maxVals then .vals l else .rng (lmin l) (lmax l)

def AV.const (c : Nat) : AV := .vals [c % M32]

/-- A range small enough to enumerate becomes a value set. -/
def AV.small : AV → AV
  | .rng lo hi => if hi < lo + maxVals then .vals ((List.range (hi + 1 - lo)).map (lo + ·)) else .rng lo hi
  | a => a

def AV.isConst : AV → Option Nat
  | .vals [c] => some c
  | _ => none

/-- Bounds of a non-symbolic value. -/
def AV.bounds : AV → Option (Nat × Nat)
  | .vals [] => none
  | .vals l => some (lmin l, lmax l)
  | .rng lo hi => some (lo, hi)
  | .top => some (0, M32 - 1)
  | .sym _ _ => none

def AV.hasSym : AV → Bool
  | .sym _ _ => true
  | _ => false

def AV.join : AV → AV → AV
  | .top, _ => .top
  | _, .top => .top
  | .vals a, .vals b => mkVals (a ++ b)
  | .sym s o, .sym s' o' => if s = s' ∧ o = o' then .sym s o else .top
  | .sym _ _, _ => .top
  | _, .sym _ _ => .top
  | a, b => match a.bounds, b.bounds with
    | some (l1, h1), some (l2, h2) => .rng (min l1 l2) (max h1 h2)
    | none, _ => b
    | _, none => a

/-- `a` describes no more values than `b`. -/
def AV.leq : AV → AV → Bool
  | _, .top => true
  | .vals a, .vals b => a.all (· ∈ b)
  | .vals a, .rng lo hi => a.all fun x => lo ≤ x && x ≤ hi
  | .rng lo hi, .rng lo' hi' => lo' ≤ lo && hi ≤ hi'
  | .sym s o, .sym s' o' => s == s' && o == o'
  | _, _ => false

/-! ### Arithmetic

Each operation is either computed exactly on value sets, or bounded, or
`top`. The soundness proof has one lemma per case. -/

def w (n : Nat) : Word := BitVec.ofNat 32 n

/-- Exact on two value sets, through the concrete operation. -/
def lift2 (f : Word → Word → Word) (a b : List Nat) : AV :=
  if a.length * b.length ≤ 64 then
    mkVals (a.flatMap fun x => b.map fun y => (f (w x) (w y)).toNat)
  else .top

def addC (a : AV) (c : Nat) : AV :=
  let c := c % M32
  match a.small with
  | .vals l => mkVals (l.map (· + c))
  | .rng lo hi => if hi + c < M32 then .rng (lo + c) (hi + c)
                  else if M32 ≤ lo + c then .rng (lo + c - M32) (hi + c - M32) else .top
  | .sym s o => .sym s ((o + c) % M32)
  | .top => .top

def AV.add (a b : AV) : AV :=
  match a, b with
  | .vals x, .vals y => lift2 (· + ·) x y
  | a, .vals [c] => addC a c
  | .vals [c], b => addC b c
  | a, b => match a, b with
    | .sym _ _, _ => .top
    | _, .sym _ _ => .top
    | _, _ => match a.bounds, b.bounds with
      | some (l1, h1), some (l2, h2) => if h1 + h2 < M32 then .rng (l1 + l2) (h1 + h2) else .top
      | _, _ => .top

def AV.neg : AV → AV
  | .vals l => mkVals (l.map fun x => (M32 - x) % M32)
  | _ => .top

def AV.sub (a b : AV) : AV :=
  match b with
  | .vals [c] => addC a ((M32 - c % M32) % M32)
  | _ => match a, b with
    | .vals x, .vals y => lift2 (· - ·) x y
    | _, _ => .top

def AV.band (a b : AV) : AV :=
  match a, b with
  | .vals x, .vals y => lift2 (· &&& ·) x y
  | _, .vals [c] => match a.bounds with
    | some (_, h) => .rng 0 (min h c)
    | none => .rng 0 c
  | .vals [c], _ => match b.bounds with
    | some (_, h) => .rng 0 (min h c)
    | none => .rng 0 c
  | _, _ => .top

def AV.shr (a : AV) (k : Nat) : AV :=
  match a with
  | .vals l => mkVals (l.map (· >>> k))
  | _ => match a.bounds with
    | some (l, h) => .rng (l >>> k) (h >>> k)
    | none => .top

def AV.shl (a : AV) (k : Nat) : AV :=
  match a with
  | .vals l => mkVals (l.map fun x => (x <<< k) % M32)
  | .rng l h => if h <<< k < M32 then .rng (l <<< k) (h <<< k) else .top
  | _ => .top

def bool01 : AV := .vals [0, 1]

def AV.sltu (a b : AV) : AV :=
  match a, b with
  | .vals x, .vals y => lift2 (fun p q => if p.ult q then 1 else 0) x y
  | _, _ => match a.bounds, b.bounds with
    | some (l1, h1), some (l2, h2) =>
      if h1 < l2 then .const 1 else if h2 ≤ l1 then .const 0 else bool01
    | _, _ => bool01

def AV.slt (a b : AV) : AV :=
  match a, b with
  | .vals x, .vals y => lift2 (fun p q => if p.slt q then 1 else 0) x y
  | _, _ => match a.bounds, b.bounds with
    | some (l1, h1), some (l2, h2) =>
      -- Both non-negative as signed numbers: the unsigned order.
      if h1 < 2^31 ∧ h2 < 2^31 then
        (if h1 < l2 then .const 1 else if h2 ≤ l1 then .const 0 else bool01)
      else bool01
    | _, _ => bool01

def AV.alu (op : AluOp) (a b : AV) : AV :=
  match op with
  | .add => a.add b
  | .sub => a.sub b
  | .and => a.band b
  | .or => match a, b with | .vals x, .vals y => lift2 (· ||| ·) x y | _, _ => .top
  | .xor => match a, b with | .vals x, .vals y => lift2 (· ^^^ ·) x y | _, _ => .top
  | .sll => match b with | .vals [k] => a.shl (k % 32) | _ => .top
  | .srl => match b with | .vals [k] => a.shr (k % 32) | _ => .top
  | .sra => match a, b with
    | .vals x, .vals y => lift2 (fun p q => p.sshiftRight (q.toNat % 32)) x y
    | .rng l h, .vals [k] => if h < 2^31 then .rng (l >>> (k % 32)) (h >>> (k % 32)) else .top
    | _, _ => .top
  | .slt => a.slt b
  | .sltu => a.sltu b

/-! ### Branch decisions and refinement -/

/-- Can the branch be taken / not taken? -/
def canTake (c : BrCond) (a b : AV) : Bool × Bool :=
  match a, b with
  | .vals x, .vals y =>
    let outs := x.flatMap fun p => y.map fun q => taken c (w p) (w q)
    (outs.any id, outs.any (!·))
  | .sym s o, .sym s' o' =>
    if s = s' ∧ o = o' then
      match c with
      | .eq | .ge | .geu => (true, false)
      | .ne | .lt | .ltu => (false, true)
    else (true, true)
  | _, _ => match a.bounds, b.bounds with
    | some (l1, h1), some (l2, h2) =>
      match c with
      | .ltu => (decide (l1 < h2), decide (h1 ≥ l2))
      | .geu => (decide (h1 ≥ l2), decide (l1 < h2))
      | .eq => let ov := l1 ≤ h2 ∧ l2 ≤ h1
               (decide ov, !(l1 = h1 ∧ l2 = h2 ∧ l1 = l2))
      | .ne => let ov := l1 ≤ h2 ∧ l2 ≤ h1
               (!(l1 = h1 ∧ l2 = h2 ∧ l1 = l2), decide ov)
      | .lt | .ge =>
        if h1 < 2^31 ∧ h2 < 2^31 then
          if c = .lt then (decide (l1 < h2), decide (h1 ≥ l2))
          else (decide (h1 ≥ l2), decide (l1 < h2))
        else (true, true)
    | _, _ => (true, true)

/-- `top` as the full range, so range refinement applies to it. -/
def AV.topRng : AV → AV
  | .top => .rng 0 (M32 - 1)
  | a => a

/-- Narrow `a` given that `taken c a k` has the outcome `t`, for a constant
    `k`. -/
def refineLCore (c : BrCond) (t : Bool) (a : AV) (k : Nat) : AV :=
  match a with
  | .vals x => .vals (x.filter fun p => taken c (w p) (w k) == t)
  | .rng l h =>
    match c, t with
    | .ltu, true | .geu, false => if k = 0 then .vals [] else .rng l (min h (k - 1))
    | .ltu, false | .geu, true => .rng (max l k) h
    | .eq, true | .ne, false => if l ≤ k ∧ k ≤ h then .vals [k] else .vals []
    | .eq, false | .ne, true =>
      if k = l ∧ l < h then .rng (l+1) h else if k = h ∧ l < h then .rng l (h-1) else .rng l h
    | _, _ => .rng l h
  | a => a

def refineL (c : BrCond) (t : Bool) (a : AV) (k : Nat) : AV :=
  (refineLCore c t a.topRng k).small

/-- The same, for a constant on the left: `taken c k a = t`. -/
def refineRCore (c : BrCond) (t : Bool) (k : Nat) (a : AV) : AV :=
  match a with
  | .vals x => .vals (x.filter fun q => taken c (w k) (w q) == t)
  | .rng l h =>
    match c, t with
    -- k < a
    | .ltu, true | .geu, false => .rng (max l (k+1)) h
    -- k ≥ a
    | .ltu, false | .geu, true => .rng l (min h k)
    | .eq, true | .ne, false => if l ≤ k ∧ k ≤ h then .vals [k] else .vals []
    | .eq, false | .ne, true =>
      if k = l ∧ l < h then .rng (l+1) h else if k = h ∧ l < h then .rng l (h-1) else .rng l h
    | _, _ => .rng l h
  | a => a

def refineR (c : BrCond) (t : Bool) (k : Nat) (a : AV) : AV :=
  (refineRCore c t k a.topRng).small

/-! ## Abstract memory -/

inductive Base where
  | abs
  /-- Relative to the interrupted machine's stack pointer (handler nodes). -/
  | rel
  deriving Repr, DecidableEq, Inhabited

structure Cell where
  base : Base
  addr : Nat
  w : Width
  v : AV
  /-- `some (ga, gv)`: the constraint holds only while the word at absolute
      address `ga` is not `gv`. This is how `Option<Waker>` is described:
      while the vtable word is non-null, the data word is a task. -/
  guard : Option (Nat × Width × Nat)
  deriving Repr, DecidableEq

/-- The bytes `[a, a+n)` and `[b, b+m)` may overlap (on one base, mod 2^32). -/
def overlap (a n b m : Nat) : Bool :=
  -- Addresses are reduced mod 2^32; a range never wraps in a checked state.
  a < b + m && b < a + n

def Cell.hits (c : Cell) (base : Base) (a n : Nat) : Bool :=
  c.base == base && overlap c.addr c.w.bytes a n

/-- The unconditional fact about `wd` at `a`, if any. -/
def plain (mem : List Cell) (base : Base) (a : Nat) (wd : Width) : Option AV :=
  (mem.find? fun c => c.base == base && c.addr == a && c.w == wd && c.guard.isNone).map (·.v)

/-- The state knows the `g.2.1` value at `g.1` is not `g.2.2`. -/
def guardHolds (mem : List Cell) (g : Nat × Width × Nat) : Bool :=
  match plain mem .abs g.1 g.2.1 with
  | some (.vals l) => !(l.contains g.2.2)
  | some (.rng lo hi) => g.2.2 < lo || hi < g.2.2
  | _ => false

/-- A fact about `wd` at `a` that applies in this state. -/
def lookup (mem : List Cell) (base : Base) (a : Nat) (wd : Width) : Option AV :=
  (mem.find? fun c => c.base == base && c.addr == a && c.w == wd &&
    match c.guard with | none => true | some g => guardHolds mem g).map (·.v)

/-- A cell that is stale after writing `v` to `wd` at `a` on `base`: it
    overlaps the write, or its guard reads bytes the write overlaps (unless
    the write stores exactly the guard value there, which makes the guarded
    fact hold vacuously). -/
def Cell.staleAfter (c : Cell) (base : Base) (a : Nat) (wd : Width) (v : AV) : Bool :=
  c.hits base a wd.bytes ||
  (base == .abs && match c.guard with
    | some g => overlap g.1 g.2.1.bytes a wd.bytes && !(g.1 == a && g.2.1 == wd && v == .vals [g.2.2])
    | none => false)

/-- What a load of `wd` from `a` returns, before extension. -/
def loadCell (mem : List Cell) (base : Base) (a : Nat) (wd : Width) : AV :=
  match lookup mem base a wd with
  | some v => v
  | none =>
    match wd with
    | .b => .rng 0 255
    | .h => .rng 0 65535
    | .w => .top

def storeStrong (mem : List Cell) (base : Base) (a : Nat) (wd : Width) (v : AV) : List Cell :=
  ⟨base, a, wd, v, none⟩ :: mem.filter fun c => !c.staleAfter base a wd v

/-- A store to one of several addresses: each may or may not be written. -/
def storeWeak (mem : List Cell) (base : Base) (a : Nat) (wd : Width) (v : AV) : List Cell :=
  mem.filterMap fun c =>
    if c.base == base && c.addr == a && c.w == wd && c.guard.isNone then some { c with v := c.v.join v }
    else if c.staleAfter base a wd v then none else some c

/-- Record that the `wd` value at `a` is `v` (it was just loaded), keeping
    every other fact, guarded ones included. -/
def setPlain (mem : List Cell) (a : Nat) (wd : Width) (v : AV) : List Cell :=
  ⟨.abs, a, wd, v, none⟩ :: mem.filter fun c => !(c.base == .abs && c.addr == a && c.w == wd && c.guard.isNone)

/-! ## Abstract machine states -/

/-- An abstract Boolean CSR field: known false, known true, or either. -/
inductive Tri where
  | no | yes | any
  deriving Repr, DecidableEq, Inhabited

def Tri.leq : Tri → Tri → Bool
  | _, .any => true
  | a, b => a == b

def Tri.join (a b : Tri) : Tri := if a = b then a else .any

def Tri.mayBe (t : Tri) (b : Bool) : Bool :=
  match t with | .any => true | .yes => b | .no => !b

def Tri.of (b : Bool) : Tri := if b then .yes else .no

structure AState where
  pc : Nat
  /-- x1..x31 (x0 is always zero and not stored). -/
  regs : List AV
  mem : List Cell
  mie : Tri
  mpie : Tri
  /-- Possible values of mstatus.MPP. -/
  mpp : List Nat
  mieReg : AV
  mtvec : AV
  mepc : AV
  mcause : AV
  mscratch : AV
  /-- A handler node: `sym` and `rel` refer to the interrupted machine. -/
  hnd : Bool
  deriving Repr, DecidableEq

def AState.get (s : AState) (r : Reg) : AV :=
  if r.val = 0 then .const 0 else s.regs.getD (r.val - 1) .top

def AState.set (s : AState) (r : Reg) (v : AV) : AState :=
  if r.val = 0 then s else { s with regs := s.regs.set (r.val - 1) v }

/-! ## The configuration a certificate is checked against -/

/-- Allowed values for writes to one device register. -/
structure Allow where
  addr : Nat
  lo : Nat
  hi : Nat
  deriving Repr, DecidableEq

structure Config where
  board : Board
  img : List Segment
  /-- RAM below this address is static data, at or above it the stack. -/
  stackLow : Nat
  /-- RAM at or above this address belongs to frames that never return
      (`main` and what calls it); it is treated as static data. -/
  pinLow : Nat
  /-- The device-write property. Unlisted registers may take any value. -/
  allow : List Allow
  /-- The deepest a handler may push below the interrupted stack pointer. -/
  hdepth : Nat
  /-- Static RAM intervals `[lo, hi)` the interrupt handler never writes.
      `check` takes them from the certificate (any value given here is
      replaced) and refuses a handler store that touches one; facts about
      them then survive an interrupt. -/
  hkeep : List (Nat × Nat) := []

def Config.ramEnd (cfg : Config) : Nat := cfg.board.ramBase + cfg.board.ramSize

def Config.isStatic (cfg : Config) (a n : Nat) : Bool :=
  (cfg.board.ramBase ≤ a && a + n ≤ cfg.stackLow) || (cfg.pinLow ≤ a && a + n ≤ cfg.ramEnd)

def Config.isStack (cfg : Config) (a n : Nat) : Bool :=
  cfg.stackLow ≤ a && a + n ≤ cfg.pinLow

/-- Bytes `[a, a+n)` are static and inside one kept interval. -/
def Config.keeps (cfg : Config) (a n : Nat) : Bool :=
  cfg.isStatic a n && cfg.hkeep.any fun p => p.1 ≤ a && a + n ≤ p.2

/-- Some byte of `[a, a+n)` is in a kept interval. -/
def Config.touchesKeep (cfg : Config) (a n : Nat) : Bool :=
  cfg.hkeep.any fun p => a < p.2 && p.1 < a + n

/-- Is a write of a value in `v` to device register `a` allowed? -/
def Config.writeOk (cfg : Config) (a : Nat) (v : AV) : Bool :=
  match cfg.allow.find? (·.addr == a) with
  | none => true
  | some al => match v.bounds with
    | some (l, h) => al.lo ≤ l && h ≤ al.hi
    | none => false

/-! ## Memory accesses -/

/-- Where an absolute access goes. -/
inductive Target where
  | ram
  | rom (v : Nat)
  | dev (d : DevReg)
  deriving Repr, DecidableEq

def classify (cfg : Config) (a : Nat) (wd : Width) : Option Target :=
  if a % wd.bytes ≠ 0 then none
  else if cfg.board.inRam (w a) wd.bytes then some .ram
  else match romRead? cfg.img a wd.bytes false with
    | some v => some (.rom v.toNat)
    | none => match cfg.board.device? (w a) with
      | some d => if wd = .w then some (.dev d) else none
      | none => none

/-- What a load from one absolute candidate address can return, or `none`
    if it could fault there. -/
def loadAt (cfg : Config) (s : AState) (a : Nat) (wd : Width) (atomic : Bool) : Option AV :=
  match classify cfg a wd with
  | some .ram => some (loadCell s.mem .abs a wd)
  | some (.rom v) => if atomic then none else some (.const v)
  | some (.dev d) => if atomic || !d.read then none else some .top
  | none => none

/-- The values of a load, or `none` if some possible address could fault. -/
def absLoad (cfg : Config) (s : AState) (addr : AV) (wd : Width) (atomic : Bool) : Option AV :=
  match addr with
  | .vals as => as.foldlM (init := .vals []) fun acc a => (loadAt cfg s a wd atomic).map acc.join
  | .sym 2 off =>
    -- A handler's own stack frame, below the interrupted sp and within its
    -- budget (so the bytes are RAM).
    if s.hnd && off % wd.bytes = 0 && M32 - cfg.hdepth ≤ off && off + wd.bytes ≤ M32 then
      some (loadCell s.mem .rel off wd)
    else none
  | _ => none

/-- Values below this are non-negative as signed `wd` values. -/
def signedLimit : Width → Nat
  | .b => 128
  | .h => 32768
  | .w => 2147483648

/-- Extension of a loaded value. -/
def AV.extend (wd : Width) (signed : Bool) (v : AV) : AV :=
  match wd, signed with
  | .w, _ => v
  | _, false => v
  | _, true => match v with
    | .vals l => mkVals (l.map fun x => (E5R.extend wd true (w x)).toNat)
    | .rng l h => if h < signedLimit wd then .rng l h else .top
    | _ => .top

/-- A store to one absolute candidate address: `strong` when it is the only
    candidate. `none` if it could fault or write a disallowed device value. -/
def storeAt (cfg : Config) (s : AState) (mem : List Cell) (a : Nat) (wd : Width) (v : AV)
    (atomic strong : Bool) : Option (List Cell) :=
  match classify cfg a wd with
  | some .ram =>
    -- Handler nodes may write static RAM outside the kept intervals, but
    -- never the interrupted stack.
    if s.hnd && (!cfg.isStatic a wd.bytes || cfg.touchesKeep a wd.bytes) then none
    else some (if strong then storeStrong mem .abs a wd v else storeWeak mem .abs a wd v)
  | some (.dev d) => if atomic || !d.write || !cfg.writeOk a v then none else some mem
  | _ => none

/-- The value memory keeps from a store of `wd`: its low bits. -/
def AV.stored (wd : Width) (v : AV) : AV :=
  match wd with
  | .b => v.band (.const 0xff)
  | .h => v.band (.const 0xffff)
  | .w => v

/-- The memory after a store, or `none` if some possible address could
    fault or write a disallowed device value. -/
def absStore (cfg : Config) (s : AState) (addr : AV) (wd : Width) (v : AV) (atomic : Bool) :
    Option (List Cell) :=
  let v := v.stored wd
  match addr with
  | .vals [a] => storeAt cfg s s.mem a wd v atomic true
  | .vals as => as.foldlM (init := s.mem) fun mem a => storeAt cfg s mem a wd v atomic false
  | .sym 2 off =>
    -- Below the interrupted sp, within the handler's stack budget.
    if s.hnd && off % wd.bytes = 0 && M32 - cfg.hdepth ≤ off && off + wd.bytes ≤ M32 then
      some (storeStrong s.mem .rel off wd v)
    else none
  | _ => none

/-! ## CSRs -/

def mstatusVals (s : AState) : List Nat :=
  let mies := [false, true].filter s.mie.mayBe
  let mpies := [false, true].filter s.mpie.mayBe
  mies.flatMap fun a => mpies.flatMap fun b => s.mpp.map fun p =>
    (if a then 8 else 0) + (if b then 0x80 else 0) + p * 2048

def csrReadAbs (s : AState) (addr : Nat) : Option AV :=
  if addr = csrMstatus then some (mkVals (mstatusVals s))
  else if addr = csrMie then some s.mieReg
  else if addr = csrMtvec then some s.mtvec
  else if addr = csrMscratch then some s.mscratch
  else if addr = csrMepc then some s.mepc
  else if addr = csrMcause then some s.mcause
  else if addr = csrMip then some (.rng 0 0x888)
  else if addr = csrMhartid then some (.const 0)
  else none

/-- The abstract states after writing `v` to a CSR; `none` if some value in
    `v` would be unsupported. -/
def csrWriteAbs (s : AState) (addr : Nat) (v : AV) : Option AState :=
  if addr = csrMstatus then
    match v with
    | .vals l =>
      if l.all (fun x => x &&& (M32 - 1 - 0x1888) = 0 && (x / 2048 % 4 = 0 || x / 2048 % 4 = 3)) then
        let mies := l.map fun x => x / 8 % 2 == 1
        let mpies := l.map fun x => x / 128 % 2 == 1
        some { s with
          mie := if mies.all id then .yes else if mies.all (!·) then .no else .any,
          mpie := if mpies.all id then .yes else if mpies.all (!·) then .no else .any,
          mpp := norm (l.map fun x => x / 2048 % 4) }
      else none
    | _ => none
  -- A handler leaves mie, mtvec and mscratch alone: the return summary
  -- assumes the interrupted values survive.
  else if addr = csrMie then if s.hnd then none else some { s with mieReg := v.band (.const 0x888) }
  else if addr = csrMtvec then
    if s.hnd then none else
    match v with
    | .vals l => if l.all (fun x => x % 4 = 0 || x % 128 = 1) then some { s with mtvec := v } else none
    | _ => none
  else if addr = csrMscratch then if s.hnd then none else some { s with mscratch := v }
  else if addr = csrMepc then some { s with mepc := v.band (.const (M32 - 2)) }
  else if addr = csrMip then some s
  else none

/-! ## Transfer -/

/-- A jump: one successor per possible target, none may be odd. -/
def jumpAbs (s : AState) (t : AV) : Option (List AState) :=
  match t with
  | .vals l => if l.all (· % 2 = 0) then some (l.map fun p => { s with pc := p }) else none
  | _ => none

/-- Narrow one branch operand by the branch outcome `t`, when the other is a
    constant. -/
def refineState (c : BrCond) (t : Bool) (rs1 rs2 : Reg) (s' : AState) (a b : AV) : AState :=
  match b.isConst, a.isConst with
  | some k, _ => s'.set rs1 (refineL c t a k)
  | none, some k => s'.set rs2 (refineR c t k b)
  | none, none => s'

/-- Successor states of one instruction, or `none` if it might fault. -/
def absExec (cfg : Config) (s : AState) (len : Nat) (i : Instr) : Option (List AState) :=
  let next := (s.pc + len) % M32
  let adv (s' : AState) : Option (List AState) := some [{ s' with pc := next }]
  let g := s.get
  match i with
  | .lui rd imm => adv (s.set rd (.const imm.toNat))
  | .auipc rd imm => adv (s.set rd (.const (s.pc + imm.toNat)))
  | .jal rd off => jumpAbs (s.set rd (.const next)) (.const (s.pc + off.toNat))
  | .jalr rd rs1 off =>
    let t := match g rs1 with
      | .vals l => mkVals (l.map fun x => ((w x + off) &&& ~~~1).toNat)
      | _ => .top
    jumpAbs (s.set rd (.const next)) t
  | .branch c rs1 rs2 off =>
    let a := g rs1
    let b := g rs2
    let (yes, no) := canTake c a b
    let refine (t : Bool) (s' : AState) : AState := refineState c t rs1 rs2 s' a b
    let taken? : Option (List AState) :=
      if yes then jumpAbs (refine true s) (.const (s.pc + off.toNat)) else some []
    let fall := if no then [{ refine false s with pc := next }] else []
    taken?.map (· ++ fall)
  | .load wd signed rd rs1 off =>
    (absLoad cfg s (addC (g rs1) off.toNat) wd false).bind fun v =>
      adv (s.set rd (v.extend wd signed))
  | .store wd rs1 rs2 off =>
    (absStore cfg s (addC (g rs1) off.toNat) wd (g rs2) false).bind fun mem =>
      adv { s with mem := mem }
  | .opimm op rd rs1 imm => adv (s.set rd (AV.alu op (g rs1) (.const imm.toNat)))
  | .op op rd rs1 rs2 => adv (s.set rd (AV.alu op (g rs1) (g rs2)))
  | .muldiv op rd rs1 rs2 =>
    match g rs1, g rs2 with
    | .vals x, .vals y => adv (s.set rd (lift2 (E5R.muldiv op) x y))
    | _, _ => adv (s.set rd .top)
  | .lr rd rs1 =>
    (absLoad cfg s (g rs1) .w true).bind fun v => adv (s.set rd v)
  | .sc rd rs1 rs2 =>
    -- The address is probed first, as `exec` does; then success (store,
    -- rd = 0) or failure (rd = 1). The reservation is not tracked.
    (absLoad cfg s (g rs1) .w true).bind fun _ =>
    (absStore cfg s (g rs1) .w (g rs2) true).bind fun mem =>
      some [{ (s.set rd (.const 1)) with pc := next },
            { ({ s with mem := mem }).set rd (.const 0) with pc := next }]
  | .amo op rd rs1 rs2 =>
    (absLoad cfg s (g rs1) .w true).bind fun old =>
      let new := match old, g rs2 with
        | .vals x, .vals y => lift2 (amoOp op) x y
        | _, _ => .top
      (absStore cfg s (g rs1) .w new true).bind fun mem =>
        adv ({ s with mem := mem }.set rd old)
  | .fence | .fencei | .wfi => adv s
  | .csr op rd src addr =>
    let operand := match src with | .reg r => g r | .imm v => .const v.toNat
    let srcZero : Bool := match src with | .reg r => r.val == 0 | .imm v => v == 0
    let writes : Bool := op == .rw || !srcZero
    if writes && addr / 1024 == 3 then none else
    (csrReadAbs s addr).bind fun old =>
      let s' := s.set rd old
      if !writes then adv s' else
      let new := match op with
        | .rw => operand
        | .rs => match old, operand with
          | .vals x, .vals y => lift2 (· ||| ·) x y | _, _ => .top
        | .rc => match old, operand with
          | .vals x, .vals y => lift2 (fun p q => p &&& ~~~q) x y | _, _ => .top
      (csrWriteAbs s' addr new).bind adv
  | .ecall | .ebreak => none
  | .mret => none

/-! ## Interrupts -/

/-- Codes that may be taken from `s`. -/
def irqCodesAbs (s : AState) : List Nat :=
  if !s.mie.mayBe true then [] else
  irqCodes.filter fun code =>
    match s.mieReg with
    | .vals l => l.any fun x => (w x).getLsbD code
    | _ => true

/-- The handler entry for `code`: the interrupted registers, symbolically;
    static RAM described by `G`. `none` if the vector is unknown. Symbols
    1..31 are the interrupted registers, 32 its pc, 33..35 its mie, mtvec and
    mscratch, which the handler must hand back unchanged. -/
def handlerEntry (G : List Cell) (s : AState) (code : Nat) : Option AState :=
  match s.mtvec with
  | .vals [v] =>
    let base := v / 4 * 4
    let pc := if v % 4 = 1 then (base + 4 * code) % M32 else base
    if pc % 2 ≠ 0 then none else
    some { pc := pc, regs := (List.range 31).map fun i => .sym (i+1) 0, mem := G,
           mie := .no, mpie := .yes, mpp := [3], mieReg := .sym 33 0, mtvec := .sym 34 0,
           mepc := .sym 32 0, mcause := .const (2^31 + code), mscratch := .sym 35 0, hnd := true }
  | _ => none

/-! ## Certificates -/

/-- The facts in `mem` imply the fact `c`. -/
def Cell.leqIn (mem : List Cell) (c : Cell) : Bool :=
  match c.guard with
  | none => match plain mem c.base c.addr c.w with
    | some v => v.leq c.v
    | none => false
  | some g =>
    -- The same or an unconditional fact, or the guard known to be false.
    mem.any (fun d => d.base == c.base && d.addr == c.addr && d.w == c.w &&
      (d.guard.isNone || d.guard == some g) && d.v.leq c.v) ||
    (match plain mem .abs g.1 g.2.1 with
     | some x => x.leq (.vals [g.2.2])
     | none => false)

def AState.leq (a b : AState) : Bool :=
  a.pc == b.pc && a.hnd == b.hnd && a.regs.length == 31 && b.regs.length == 31 &&
  (List.zip a.regs b.regs).all (fun p => p.1.leq p.2) &&
  b.mem.all (Cell.leqIn a.mem) &&
  a.mie.leq b.mie && a.mpie.leq b.mpie && a.mpp.all (· ∈ b.mpp) &&
  a.mieReg.leq b.mieReg && a.mtvec.leq b.mtvec && a.mepc.leq b.mepc &&
  a.mcause.leq b.mcause && a.mscratch.leq b.mscratch

/-- How one successor is covered: by one node, or split on the value of a
    register over several nodes. -/
structure Edge where
  nodes : List Nat
  split : Option Nat
  /-- The split register was just loaded from this word: pin that too. -/
  pin : Bool
  deriving Repr, DecidableEq

structure Node where
  s : AState
  /-- One edge per successor, in `absExec` order. -/
  succ : List Edge
  deriving Repr

structure Cert where
  nodes : List Node
  /-- The static-RAM invariant at interruptible nodes and handler returns. -/
  G : List Cell
  /-- Every stack pointer an interrupt can arrive at. -/
  sigma : List Nat
  /-- For each interrupt code, the handler entry node. -/
  handlers : List (Nat × Nat)
  /-- Static RAM the handler never writes (`Config.hkeep`). -/
  hkeep : List (Nat × Nat) := []
  deriving Repr

def staticOf (cfg : Config) (mem : List Cell) : List Cell :=
  mem.filter fun c => c.base == .abs && cfg.isStatic c.addr c.w.bytes

/-- A static fact the handler cannot change: its bytes, and its guard's,
    are kept. -/
def Cell.kept (cfg : Config) (c : Cell) : Bool :=
  c.base == .abs && cfg.keeps c.addr c.w.bytes &&
  match c.guard with
  | some g => cfg.keeps g.1 g.2.1.bytes
  | none => true

def noSym (s : AState) : Bool :=
  !s.hnd && s.regs.all (!·.hasSym) && s.mem.all (fun c => c.base == .abs && !c.v.hasSym) &&
  !s.mieReg.hasSym && !s.mtvec.hasSym && !s.mepc.hasSym && !s.mcause.hasSym &&
  !s.mscratch.hasSym

/-- A main-thread node at which an interrupt may arrive is well-formed for
    the handler summary: static RAM is `G` followed by facts the handler
    cannot change, every tracked stack cell
    is at or above sp (the handler only writes below it), the CSRs the
    handler changes are unconstrained, and sp is one of `sigma`. -/
def interruptibleOk (cfg : Config) (cert : Cert) (s : AState) : Bool :=
  (staticOf cfg s.mem).take cert.G.length == cert.G &&
  ((staticOf cfg s.mem).drop cert.G.length).all (Cell.kept cfg) &&
  (match s.get 2 with
   | .vals [sp] =>
     sp ∈ cert.sigma &&
     -- A stack fact must not hang on a static guard word the handler may change.
     s.mem.all fun c => cfg.isStatic c.addr c.w.bytes ||
       (sp ≤ c.addr && cfg.isStack c.addr c.w.bytes && c.guard.isNone)
   | _ => false) &&
  -- After the handler's mret: MIE and MPIE set, MPP = U (0), mepc and mcause
  -- whatever the handler left.
  s.mpie.mayBe true && 0 ∈ s.mpp && s.mepc == .top && s.mcause == .top

/-- Every fact is about bytes inside RAM: absolute cells and guards lie in
    RAM, relative cells within the handler's budget below the interrupted
    sp. The soundness proof relies on this (no access wraps around the
    address space). -/
def Cell.wf (cfg : Config) (c : Cell) : Bool :=
  (match c.base with
   | .abs => c.addr < M32 && cfg.board.inRam (E5R.AI.w c.addr) c.w.bytes
   | .rel => M32 - cfg.hdepth ≤ c.addr && c.addr + c.w.bytes ≤ M32) &&
  (match c.guard with
   | some g => g.1 < M32 && cfg.board.inRam (E5R.AI.w g.1) g.2.1.bytes
   | none => true)

def AState.wf (cfg : Config) (s : AState) : Bool :=
  s.regs.length == 31 && s.mem.all (Cell.wf cfg) && (s.hnd || s.mem.all (·.base == .abs)) &&
  -- A handler's absolute facts and every guard are about static memory,
  -- apart from its frame (a frame store does not invalidate guards).
  (!s.hnd || s.mem.all fun c => (c.base == .rel || cfg.isStatic c.addr c.w.bytes) &&
    match c.guard with | some g => cfg.isStatic g.1 g.2.1.bytes | none => true)

/-- A handler `mret` returns exactly to the interrupted machine. -/
def mretOk (cfg : Config) (cert : Cert) (s : AState) : Bool :=
  s.hnd && s.regs == (List.range 31).map (fun i => .sym (i+1) 0) &&
  s.mepc == .sym 32 0 && s.mpie == .yes && s.mpp == [3] &&
  s.mieReg == .sym 33 0 && s.mtvec == .sym 34 0 && s.mscratch == .sym 35 0 &&
  (staticOf cfg s.mem).all (fun _ => true) && cert.G.all (Cell.leqIn s.mem) &&
  s.mem.all fun c => c.base == .rel || cfg.isStatic c.addr c.w.bytes

/-- The successors of a node, as the checker computes them. -/
def successors (cfg : Config) (s : AState) : Option (List AState) :=
  match fetchDecode' cfg.img s.pc with
  | some (i, len) => absExec cfg s len i
  | none => none
where
  fetchDecode' (img : List Segment) (pc : Nat) : Option (Instr × Nat) :=
    if pc % 2 ≠ 0 then none else
    match fetch img (w pc) with
    | some (bits, len) => (decode bits len).map (·, len.toNat)
    | none => none

/-- `t` is described by node `j`. -/
def covered (cert : Cert) (t : AState) (j : Nat) : Bool :=
  match cert.nodes[j]? with
  | some m => t.leq m.s
  | none => false

/-- The word a pinning split refers to: a word load at an exact RAM address,
    as (destination register, address, width). -/
def pinAddr (cfg : Config) (s : AState) : Option (Nat × Nat × Width) :=
  match successors.fetchDecode' cfg.img s.pc with
  | some (.load wd signed rd rs1 off, _) =>
    if signed && wd != .w then none else
    match addC (s.get rs1) off.toNat with
    | .vals [a] => if classify cfg a wd == some .ram then some (rd.val, a, wd) else none
    | _ => none
  | _ => none

/-- The successor after splitting register `r` on value `v`, with the loaded
    word pinned to `v` too when the edge asks for it. -/
def pinned (pin : Option (Nat × Nat × Width)) (e : Edge) (r v : Nat) (t' : AState) : Option AState :=
  if !e.pin then some t' else
  match pin with
  | some (rd, a, wd) => if rd = r then some { t' with mem := setPlain t'.mem a wd (.vals [v]) } else none
  | none => none

/-- How one successor is covered: by one node, or split on the value of a
    register over several nodes. -/
def coveredE (cert : Cert) (pin : Option (Nat × Nat × Width)) (t : AState) (e : Edge) : Bool :=
  match e.split with
  | none => !e.pin && match e.nodes with | [j] => covered cert t j | _ => false
  | some r =>
    if h : 0 < r ∧ r < 32 then
      match t.get ⟨r, h.2⟩ with
      | .vals l => l.all fun v =>
        match pinned pin e r v (t.set ⟨r, h.2⟩ (.vals [v])) with
        | some t' => e.nodes.any fun j => covered cert t' j
        | none => false
      | _ => false
    else false

/-- The instruction at the node: an `mret` summary, or every successor covered. -/
def instrOk (cfg : Config) (cert : Cert) (n : Node) : Bool :=
  match successors.fetchDecode' cfg.img n.s.pc with
  | some (.mret, _) => mretOk cfg cert n.s && n.succ.isEmpty
  | some (i, len) => match absExec cfg n.s len i with
    | some ts => ts.length == n.succ.length &&
        (List.zip ts n.succ).all fun (t, e) => coveredE cert (pinAddr cfg n.s) t e
    | none => false
  | none => false

/-- Every interrupt that may arrive at the node enters a covered handler. -/
def irqOk (cfg : Config) (cert : Cert) (s : AState) : Bool :=
  let codes := irqCodesAbs s
  codes.isEmpty || (!s.hnd && interruptibleOk cfg cert s && codes.all fun code =>
    match handlerEntry cert.G s code, cert.handlers.lookup code with
    | some e, some j => covered cert e j
    | _, _ => false)

def nodeOk (cfg : Config) (cert : Cert) (n : Node) : Bool :=
  n.s.wf cfg && (n.s.hnd || noSym n.s) && instrOk cfg cert n && irqOk cfg cert n.s

def checkAt (cfg : Config) (boot : AState) (cert : Cert) : Bool :=
  -- Execution starts in the main thread, at node 0.
  !boot.hnd &&
  (match cert.nodes[0]? with | some n => boot.leq n.s | none => false) &&
  -- RAM lies inside the 32-bit address space, and the image holds bytes.
  cfg.board.ramBase + cfg.board.ramSize ≤ M32 &&
  cfg.img.all (fun seg => seg.bytes.all (· < 256)) &&
  cert.nodes.all (nodeOk cfg cert) &&
  -- The handler's stack frame never reaches static RAM, from any sp.
  cert.sigma.all (fun sp => cfg.stackLow + cfg.hdepth ≤ sp && sp ≤ cfg.pinLow && sp % 4 = 0) &&
  cfg.board.ramBase ≤ cfg.stackLow &&
  cfg.hdepth < 2^31 && cfg.stackLow ≤ cfg.pinLow && cfg.pinLow ≤ cfg.ramEnd &&
  cert.G.all (fun c => c.base == .abs && c.wf cfg && cfg.isStatic c.addr c.w.bytes && !c.v.hasSym &&
    match c.guard with | some g => cfg.isStatic g.1 g.2.1.bytes | none => true)

/-- The checker, with the kept intervals the certificate names. -/
def check (cfg : Config) (boot : AState) (cert : Cert) : Bool :=
  checkAt { cfg with hkeep := cert.hkeep } boot cert

end E5R.AI
