import NoCompiler.Struct
import NoCompiler.Image
import NoCompiler.Trace
import NoCompiler.Fast.State
import NoCompiler.VC.Straight
import NoCompiler.VC.Mem
import NoCompiler.VC.Ob

/-
Proof automation for structured code: `nocompiler_auto`.

A function in the profile has a block/loop tree (rule R3, `Struct.Func`):
every branch goes forward to the end of an enclosing block or back to the
head of an enclosing loop. So every cycle of its control-flow graph passes
through a loop head, and the paths from the entry or from one loop head to
the next loop head or to the return are finite and loop-free. Given an
invariant and a measure at each loop head, a proof is

* one symbolic run along each such path, which is mechanical;
* at its end, the invariant (or the postcondition) of the state reached,
  which is a fact about the values the run computed: the verification
  conditions.

`nocompiler_auto` does the first part and leaves the second, in a normal form in
which each machine word is `BitVec.ofNat 64 e` or `base + BitVec.ofNat 64 e`
for a natural-number expression `e`, comparisons are comparisons of those
expressions, and the bytes of a buffer are a list. Conditions that are
linear arithmetic it closes with `omega`; what is left is about the
function's specification, in its own terms.

It also discharges, on every step, the conditions a step needs: the
instruction at the pc (by the image), the pc inside the code, the access
permitted by the specification's regions, the access aligned, and, at every
loop head and at the return, that the registers the function never writes
hold their entry values (`Same`, hence `Preserved`).

What is left is named after the path: `entry_to_0x…`, `0x…_to_0x…`,
`0x…_ret_0x…` (with `_b`, `_c`, ... when several runs end at the same place,
and `_0`, `_1`, ... for the conjuncts of one invariant or postcondition),
`…_measure`, and `perm_0x…` / `align_0x…` for side conditions it could not
discharge. In each, the invariant's ghosts have the names they are bound by,
its facts are `h1`, `h2`, ... in the order of its conjuncts, and the branch
taken at address `a` is the hypothesis `hb_a`.

Nothing here is trusted: the result is a proof term the kernel checks, built
from `Reach.cutpoints`, `Reach.exec_step` and the lemmas below.

Two rules keep that proof cheap for the kernel, and both were found the hard
way (a 160-instruction run whose proof elaborates in 20 s took the kernel
over 9 GB): no `decide` on an open proposition (`Nat.ble` on a variable and
a 2^64 literal unfolds along the literal), and no definitional step between
two different machine states (`rfl` lemmas and `assumption` up to unfolding
make the kernel compare the states, memory writes included). Hence
`nocompiler_decide_closed`, `nocompiler_omega`, the proof-carrying `State.*'` lemmas, and
the `exit` goals proved by rewriting.

Scope (v1, docs/isa/v1.md): functions with calls, syscalls and a frame.
`calls [thm, ...]` names the `VerifiedImg` theorems of the callees: at a call
the run continues through `VerifiedImg.call` from every way the callee's
specification lets it end, never looking at the callee's code; after it, the
callee-saved registers, the pc and memory outside the callee's permission are
known again, one equation per register normalised on the spot. At an ECALL
every outcome the environment model allows is a path (other syscall numbers
are refuted from a7). A prologue's saves become conjuncts of every
invariant, so a proof states no frame and no register preservation; arrays,
buffers and segments that a specification keeps apart from the stack
(`∀ x, A.mem x → ¬ R.mem x`) stay as they were under the frame's stores.
Cut points are given by label (`loop_inv $l1 …`, the labels `nocompiler
export` writes as `<f>_labels`, named as `disasm` names them) or by address.
What is left is named after the path, without addresses, so a proof's text
does not change when its function is linked elsewhere: labels where there
are any, otherwise offsets from the function's entry (`entry_to_l1`,
`l1_ret_x28`, `entry_exit_x30`, `entry_call_write_all_verified_pre`); an existential whose witnesses the tactic
cannot determine is left whole, for the proof to give them by name
(lean/Examples/Hello.lean, Sum2.lean).
-/
namespace NoCompiler

/-! ## Cut points -/

/-- Floyd's method on `Reach.loop`: an invariant at every cut point (`inv pc`)
    and a measure (`μ pc`) that every path from one cut point to the next
    decreases. With the loop heads as cut points, every path from the start or
    from a cut point reaches the end (`Q`) or a cut point without passing
    another. The postconditions are given as equations so that a proof can
    keep them abstract while it runs. -/
theorem Reach.cutpoints {c : Code} {P : Perm} {D : Dom} {Q : State → Prop}
    (inv : Word → State → Prop) (μ : Word → State → Nat) {s : State}
    (start : ∀ R : State → Prop, R = (fun s' => Q s' ∨ inv s'.pc s') → Reach c P D R s)
    (body : ∀ u, inv u.pc u → ∀ R : State → Prop,
      R = (fun s' => Q s' ∨ (inv s'.pc s' ∧ μ s'.pc s' < μ u.pc u)) → Reach c P D R u) :
    Reach c P D Q s :=
  Reach.trans (start _ rfl) fun s' h => h.elim .done fun hi =>
    Reach.loop (fun u => inv u.pc u) (fun u => μ u.pc u) (fun u hu => body u hu _ rfl) s' hi

/-- An aligned access goes ahead. -/
theorem Reach.opt_aligned {c : Code} {P : Perm} {D : Dom} {Q : State → Prop} {a : Word} {w : Nat}
    {s : State} (h : aligned a w) :
    Reach.opt c P D Q (if aligned a w then some s else none) = Reach c P D Q s := by
  simp [h]

/-! Proof-carrying forms of the state projections. The originals
(NoCompiler/Lemmas.lean) are `rfl` lemmas, which `simp` applies as definitional
steps without a proof; the kernel then rechecks each such step by comparing
two different state terms, and on a long run that comparison unfolds the
pending memory writes. These are proved by cases, so `simp` writes the
rewrite into the proof instead. -/
namespace State
@[nocompiler_state high] theorem setPc_pc' (s : State) (p) : (s.setPc p).pc = p := by cases s; rfl
@[nocompiler_state high] theorem setPc_mem' (s : State) (p) : (s.setPc p).mem = s.mem := by cases s; rfl
@[nocompiler_state high] theorem setPc_trace' (s : State) (p) : (s.setPc p).trace = s.trace := by cases s; rfl
@[nocompiler_state high] theorem setPc_exit' (s : State) (p) : (s.setPc p).exit = s.exit := by cases s; rfl
@[nocompiler_state high] theorem setPc_reg' (s : State) (p r) : (s.setPc p).reg r = s.reg r := by cases s; rfl
@[nocompiler_state high] theorem setMem_pc' (s : State) (m) : (s.setMem m).pc = s.pc := by cases s; rfl
@[nocompiler_state high] theorem setMem_mem' (s : State) (m) : (s.setMem m).mem = m := by cases s; rfl
@[nocompiler_state high] theorem setMem_trace' (s : State) (m) : (s.setMem m).trace = s.trace := by cases s; rfl
@[nocompiler_state high] theorem setMem_exit' (s : State) (m) : (s.setMem m).exit = s.exit := by cases s; rfl
@[nocompiler_state high] theorem setMem_reg' (s : State) (m r) : (s.setMem m).reg r = s.reg r := by cases s; rfl
@[nocompiler_state high] theorem emit_pc' (s : State) (e) : (s.emit e).pc = s.pc := by cases s; rfl
@[nocompiler_state high] theorem emit_mem' (s : State) (e) : (s.emit e).mem = s.mem := by cases s; rfl
@[nocompiler_state high] theorem emit_exit' (s : State) (e) : (s.emit e).exit = s.exit := by cases s; rfl
@[nocompiler_state high] theorem emit_reg' (s : State) (e r) : (s.emit e).reg r = s.reg r := by cases s; rfl
@[nocompiler_state high] theorem setPc_setPc' (s : State) (p q : Word) : (s.setPc p).setPc q = s.setPc q := by
  cases s; rfl
@[nocompiler_state high] theorem setMem_setMem' (s : State) (m m' : Word → Byte) :
    (s.setMem m).setMem m' = s.setMem m' := by cases s; rfl
@[nocompiler_state high] theorem setPc_setMem' (s : State) (p : Word) (m : Word → Byte) :
    (s.setPc p).setMem m = (s.setMem m).setPc p := by cases s; rfl
end State

/-! Moving `emit`, `halt` and `sysRet` out of the way of the pc, for the
states a syscall leaves. -/
namespace State
@[nocompiler_state high] theorem emit_setPc' (s : State) (p : Word) (e : Event) :
    (s.setPc p).emit e = (s.emit e).setPc p := by cases s; rfl
@[nocompiler_state high] theorem emit_setMem' (s : State) (m : Word → Byte) (e : Event) :
    (s.setMem m).emit e = (s.emit e).setMem m := by cases s; rfl
@[nocompiler_state high] theorem emit_setReg' (s : State) (r : Reg) (v : Word) (e : Event) :
    (s.setReg r v).emit e = (s.emit e).setReg r v := by
  unfold setReg; split <;> cases s <;> rfl
@[nocompiler_state high] theorem sysRet_eq' (s : State) (r : Word) :
    s.sysRet r = (s.setReg Reg.a0 r).setPc (s.pc + 4) := rfl
@[nocompiler_state high] theorem emit_exit_halt (s : State) (c : Word) (e : Event) :
    ((s.halt c).emit e).exit = some c := by cases s; rfl
end State

/-- Two regions share no byte. -/
def Region.Disjoint (r r' : Region) : Prop :=
  r.size ≤ (r'.base - r.base).toNat ∧ r'.size ≤ (r.base - r'.base).toNat

theorem Region.Disjoint.symm {r r' : Region} (h : r.Disjoint r') : r'.Disjoint r := ⟨h.2, h.1⟩

namespace Auto

/-! ## Calls, frames, syscalls -/

-- The sign of a syscall's result, for the branch a caller takes on it, in the
-- form the branch conditions have (`0#64`).
@[nocompiler_nat] theorem ofNat_not_slt_zero' {r : Nat} (h : r ≤ maxRW) :
    (BitVec.ofNat 64 r).slt (BitVec.ofNat 64 0) = false := ofNat_not_slt_zero h
@[nocompiler_nat] theorem neg_ofNat_slt_zero' {e : Nat} (h1 : 1 ≤ e) (h2 : e ≤ 4095) :
    (-(BitVec.ofNat 64 e)).slt (BitVec.ofNat 64 0) = true := neg_ofNat_slt_zero h1 h2

/-- After a call: registers the caller keeps unchanged stay so if the callee
    preserves every register outside `rs`. -/
theorem Same.after_call {s0 s1 s' : State} {rs : List Nat} (h : Same s0 s1 rs) (hp : Preserved s1 s')
    (hrs : ∀ r : Reg, r.val ∉ rs → r = 0 ∨ r ∈ preservedRegs) : Same s0 s' rs := by
  intro r hr
  rcases hrs r hr with rfl | hm
  · simp
  · rw [hp r hm]; exact h r hr

/-- `Preserved` from `Same`, with the registers in `rs` (saved and restored by
    the function) shown one by one. -/
theorem Same.preserved_of {s0 s' : State} {rs : List Nat} (h : Same s0 s' rs)
    (hr : ∀ r ∈ preservedRegs, r.val ∈ rs → s'.reg r = s0.reg r) : Preserved s0 s' := by
  intro r hm
  by_cases hin : r.val ∈ rs
  · exact hr r hm hin
  · exact h r hin

theorem Same.reg_eq {s0 s : State} {rs : List Nat} (h : Same s0 s rs) (r : Reg) (hr : r.val ∉ rs) :
    s.reg r = s0.reg r := h r hr

/-- `Preserved`, one register at a time. -/
theorem preserved_of_regs {s0 s : State}
    (h2 : s.reg 2 = s0.reg 2) (h3 : s.reg 3 = s0.reg 3) (h4 : s.reg 4 = s0.reg 4)
    (h8 : s.reg 8 = s0.reg 8) (h9 : s.reg 9 = s0.reg 9) (h18 : s.reg 18 = s0.reg 18)
    (h19 : s.reg 19 = s0.reg 19) (h20 : s.reg 20 = s0.reg 20) (h21 : s.reg 21 = s0.reg 21)
    (h22 : s.reg 22 = s0.reg 22) (h23 : s.reg 23 = s0.reg 23) (h24 : s.reg 24 = s0.reg 24)
    (h25 : s.reg 25 = s0.reg 25) (h26 : s.reg 26 = s0.reg 26) (h27 : s.reg 27 = s0.reg 27) :
    Preserved s0 s := by
  intro r hr
  simp only [preservedRegs, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    assumption

theorem Dom.not_mem_of_sub {D E : Dom} {x : Word} (h : D.sub E) (hx : ¬ E.mem x) : ¬ D.mem x :=
  fun hd => hx (h x hd)

/-- The registers a callee preserves (`preservedRegs`), as numbers. -/
def preservedNats : List Nat := [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-- The registers a callee may change: everything but sp, gp, tp, s0 to s11. -/
def nonPreserved : List Nat := [1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]

theorem nonPreserved_spec (rs : List Nat) (h : nonPreserved.all (fun r => rs.contains r) = true) :
    ∀ r : Reg, r.val ∉ rs → r = 0 ∨ r ∈ preservedRegs := by
  have key : ∀ r : Reg, r.val ∉ nonPreserved → r = 0 ∨ r ∈ preservedRegs := by decide
  intro r hr
  exact key r fun hm => hr (by have := List.all_eq_true.1 h r.val hm; simpa using this)

/-- The addresses of `f` holding an ECALL. -/
def ecalls (c : Code) (f : Struct.Func) : List Nat :=
  (List.range f.len).filterMap fun i =>
    let pc := f.entry + BitVec.ofNat 64 (4 * i)
    if c.instr pc == some .ecall then some pc.toNat else none

/-- The prologue of `f`: `addi sp, sp, -N` and the `sd r, k(sp)` after it, as
    `[N, k₁, r₁, k₂, r₂, ...]`; `[]` without a frame. -/
def frameOf (c : Code) (f : Struct.Func) : List Nat :=
  match c.instr f.entry with
  | some (.iop .addi 2 2 imm) =>
    if 2048 ≤ imm.toNat then
      let rec go : Nat → Word → List Nat
        | 0, _ => []
        | fuel + 1, pc =>
          match c.instr pc with
          | some (.store .sd 2 r off) => off.toNat :: r.val :: go fuel (pc + 4)
          | _ => []
      (4096 - imm.toNat) :: go 32 (f.entry + 4)
    else []
  | _ => []

/-! ## The registers a function writes -/

def rd? : Instr → Option Nat
  | .lui rd _ | .auipc rd _ | .jal rd _ | .jalr rd _ _ | .load _ rd _ _ | .iop _ rd _ _
  | .addiw rd _ _ | .shift _ rd _ _ | .shiftw _ rd _ _ | .rop _ rd _ _ | .rwop _ rd _ _
  | .uop _ rd _ => some rd.val
  | .ecall => some 10
  | _ => none

/-- Every register an instruction of `f` writes (computed, then used as a
    literal: `Same` along the run is proved, not assumed). -/
def writes (c : Code) (f : Struct.Func) : List Nat :=
  ((List.range f.len).filterMap fun i =>
    (c.instr (f.entry + BitVec.ofNat 64 (4 * i))).bind rd?).eraseDups.filter (· ≠ 0)

def loopHeads (f : Struct.Func) : List Nat :=
  f.nodes.filterMap fun n => if n.kind = .loop then some n.start.toNat else none

/-! ## The word normal form

`W` is 2^64, written out: `omega` and the kernel take the literal as it is. -/

local notation "W" => 18446744073709551616

@[nocompiler_nat] theorem zero_word : (0 : Word) = BitVec.ofNat 64 0 := rfl
@[nocompiler_nat] theorem one_word : (1 : Word) = BitVec.ofNat 64 1 := rfl

@[nocompiler_nat high] theorem ofNat_add_ofNat (x y : Nat) :
    BitVec.ofNat 64 x + BitVec.ofNat 64 y = BitVec.ofNat 64 (x + y) := BitVec.ofNat_add_ofNat x y

@[nocompiler_nat high] theorem add_ofNat_add_ofNat (a : Word) (x y : Nat) :
    a + BitVec.ofNat 64 x + BitVec.ofNat 64 y = a + BitVec.ofNat 64 (x + y) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

@[nocompiler_nat] theorem add_ofNat_zero (a : Word) : a + BitVec.ofNat 64 0 = a := BitVec.add_zero a
@[nocompiler_nat] theorem ofNat_zero_add (a : Word) : BitVec.ofNat 64 0 + a = a := BitVec.zero_add a

/-- Offsets to the right. -/
@[nocompiler_nat low] theorem ofNat_add_comm (x : Nat) (a : Word) :
    BitVec.ofNat 64 x + a = a + BitVec.ofNat 64 x := BitVec.add_comm _ _
@[nocompiler_nat low] theorem add_ofNat_add_comm (a b : Word) (x : Nat) :
    a + BitVec.ofNat 64 x + b = a + b + BitVec.ofNat 64 x := by
  rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 x), ← BitVec.add_assoc]
@[nocompiler_nat] theorem add_add_ofNat (a b : Word) (y : Nat) :
    a + (b + BitVec.ofNat 64 y) = a + b + BitVec.ofNat 64 y := (BitVec.add_assoc _ _ _).symm

/-- Adding a large literal is subtracting its complement, when that does not
    go below zero (`addi rd, rs, -k`). -/
@[nocompiler_nat] theorem ofNat_add_wrap (x k : Nat) (h1 : 9223372036854775808 ≤ k) (h2 : k < W)
    (h3 : W - k ≤ x) : BitVec.ofNat 64 (x + k) = BitVec.ofNat 64 (x - (W - k)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.reducePow]
  omega

@[nocompiler_nat] theorem ofNat_sub_ofNat (x y : Nat) (h : y ≤ x) (hx : x < W) :
    BitVec.ofNat 64 x - BitVec.ofNat 64 y = BitVec.ofNat 64 (x - y) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow]
  omega

@[nocompiler_nat high] theorem toNat_ofNat_lt (x : Nat) (h : x < W) : (BitVec.ofNat 64 x).toNat = x := by
  simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega
@[nocompiler_nat low] theorem toNat_ofNat_mod (x : Nat) : (BitVec.ofNat 64 x).toNat = x % W := by
  simp only [BitVec.toNat_ofNat, Nat.reducePow]
@[nocompiler_nat] theorem ofNat_mod (x : Nat) : BitVec.ofNat 64 (x % W) = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, Nat.reducePow]; omega

/-! Comparisons, as branches and `slt`/`sltu` compute them. -/

@[nocompiler_nat high] theorem ult_ofNat (x y : Nat) (hx : x < W) (hy : y < W) :
    (BitVec.ofNat 64 x).ult (BitVec.ofNat 64 y) = decide (x < y) := by
  rw [BitVec.ult_eq_decide]; simp only [toNat_ofNat_lt x hx, toNat_ofNat_lt y hy]
@[nocompiler_nat low] theorem ult_ofNat_mod (x y : Nat) :
    (BitVec.ofNat 64 x).ult (BitVec.ofNat 64 y) = decide (x % W < y % W) := by
  rw [BitVec.ult_eq_decide]; simp only [toNat_ofNat_mod]

theorem ofNat_eq_iff_mod (x y : Nat) : BitVec.ofNat 64 x = BitVec.ofNat 64 y ↔ x % W = y % W := by
  constructor
  · intro h; have := congrArg BitVec.toNat h; simpa only [toNat_ofNat_mod] using this
  · intro h; apply BitVec.eq_of_toNat_eq; simpa only [toNat_ofNat_mod] using h

@[nocompiler_nat high] theorem beq_ofNat (x y : Nat) (hx : x < W) (hy : y < W) :
    (BitVec.ofNat 64 x == BitVec.ofNat 64 y) = decide (x = y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ofNat_eq_iff_mod]; omega
@[nocompiler_nat low] theorem beq_ofNat_mod (x y : Nat) :
    (BitVec.ofNat 64 x == BitVec.ofNat 64 y) = decide (x % W = y % W) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ofNat_eq_iff_mod]
@[nocompiler_nat high] theorem bne_ofNat (x y : Nat) (hx : x < W) (hy : y < W) :
    (BitVec.ofNat 64 x != BitVec.ofNat 64 y) = !decide (x = y) := by
  rw [bne, beq_ofNat x y hx hy]
@[nocompiler_nat low] theorem bne_ofNat_mod (x y : Nat) :
    (BitVec.ofNat 64 x != BitVec.ofNat 64 y) = !decide (x % W = y % W) := by
  rw [bne, beq_ofNat_mod]

@[nocompiler_nat] theorem slt_ofNat (x y : Nat) (hx : x < 9223372036854775808) (hy : y < 9223372036854775808) :
    (BitVec.ofNat 64 x).slt (BitVec.ofNat 64 y) = decide (x < y) := by
  have ex : (BitVec.ofNat 64 x).toNat = x := by simp; omega
  have ey : (BitVec.ofNat 64 y).toNat = y := by simp; omega
  rw [BitVec.slt_eq_ult, BitVec.msb_eq_decide, BitVec.msb_eq_decide, ex, ey, BitVec.ult_eq_decide, ex, ey]
  simp only [Nat.reducePow, Nat.reduceSub]
  rw [decide_eq_false (by omega), decide_eq_false (by omega)]
  cases decide (x < y) <;> rfl

@[nocompiler_nat] theorem bool64_and (b b' : Bool) : bool64 b &&& bool64 b' = bool64 (b && b') := by
  cases b <;> cases b' <;> rfl
@[nocompiler_nat] theorem bool64_or (b b' : Bool) : bool64 b ||| bool64 b' = bool64 (b || b') := by
  cases b <;> cases b' <;> rfl
@[nocompiler_nat] theorem bool64_beq_zero (b : Bool) : (bool64 b == BitVec.ofNat 64 0) = !b := by
  cases b <;> rfl
@[nocompiler_nat] theorem bool64_bne_zero (b : Bool) : (bool64 b != BitVec.ofNat 64 0) = b := by
  cases b <;> rfl

/-- Natural numbers in the normal form are at most `x`'s value modulo 2^64:
    equalities of words, for the verification conditions (not used while
    the run goes, where they would hide the witnesses). -/
theorem ofNat_inj (x y : Nat) (hx : x < W) (hy : y < W) :
    BitVec.ofNat 64 x = BitVec.ofNat 64 y ↔ x = y := by
  rw [ofNat_eq_iff_mod]; omega
theorem add_ofNat_inj (a : Word) (x y : Nat) :
    a + BitVec.ofNat 64 x = a + BitVec.ofNat 64 y ↔ x % W = y % W := by
  rw [← ofNat_eq_iff_mod]; exact BitVec.add_right_inj a
theorem eq_add_ofNat_iff (a : Word) (y : Nat) : a = a + BitVec.ofNat 64 y ↔ y % W = 0 := by
  have := add_ofNat_inj a 0 y
  rw [add_ofNat_zero] at this; rw [this]; omega
theorem add_ofNat_eq_iff (a : Word) (y : Nat) : a + BitVec.ofNat 64 y = a ↔ y % W = 0 := by
  rw [eq_comm, eq_add_ofNat_iff]

/-! ### More operations on the normal form: 32-bit words, products, shifts, signed arguments -/

@[nocompiler_nat] theorem ofNat_mul_ofNat (x y : Nat) :
    BitVec.ofNat 64 x * BitVec.ofNat 64 y = BitVec.ofNat 64 (x * y) := BitVec.ofNat_mul_ofNat x y

/-- `sext32` (addiw, sext.w) of a value that fits in 31 bits. -/
@[nocompiler_nat] theorem sext32_ofNat (x : Nat) (h : x < 2147483648) :
    sext32 (BitVec.ofNat 64 x) = BitVec.ofNat 64 x := by
  unfold sext32
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend, BitVec.msb_eq_decide]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceSub]
  rw [ite_eq_right (by simp; omega)]; omega

@[nocompiler_nat] theorem zext32_ofNat (x : Nat) : zext32 (BitVec.ofNat 64 x) = BitVec.ofNat 64 (x % 4294967296) := by
  unfold zext32
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow]; omega

@[nocompiler_nat] theorem ofNat_shiftRight (x k : Nat) (h : x < W) :
    BitVec.ofNat 64 x >>> k = BitVec.ofNat 64 (x / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, toNat_ofNat_lt x h, Nat.shiftRight_eq_div_pow]
  rw [toNat_ofNat_lt]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h

@[nocompiler_nat] theorem ofNat_shiftLeft (x k : Nat) :
    BitVec.ofNat 64 x <<< k = BitVec.ofNat 64 (x * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reducePow]
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  all_goals omega

@[nocompiler_nat] theorem mulhUU_ofNat (x y : Nat) (hx : x < W) (hy : y < W) :
    mulhUU (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) = BitVec.ofNat 64 (x * y / W) := by
  unfold mulhUU
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt (by omega : x < 340282366920938463463374607431768211456),
    Nat.mod_eq_of_lt (by omega : y < 340282366920938463463374607431768211456)]
  have hxy : x * y < 340282366920938463463374607431768211456 := by
    have := Nat.mul_lt_mul_of_lt_of_lt hx hy; omega
  rw [Nat.mod_eq_of_lt hxy]

@[nocompiler_nat low] theorem mulhUU_ofNat_mod (x y : Nat) :
    mulhUU (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) = BitVec.ofNat 64 (x % W * (y % W) / W) := by
  rw [← ofNat_mod x, ← ofNat_mod y, mulhUU_ofNat _ _ (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))]


@[nocompiler_nat low] theorem ofNat_shiftRight_mod (x k : Nat) :
    BitVec.ofNat 64 x >>> k = BitVec.ofNat 64 (x % W / 2 ^ k) := by
  rw [← ofNat_mod x, ofNat_shiftRight _ _ (Nat.mod_lt _ (by decide))]

/-- `maxu` (and the `max` of two words in the normal form). -/
@[nocompiler_nat] theorem maxu_ofNat (x y : Nat) :
    (if decide (x < y) = true then BitVec.ofNat 64 y else BitVec.ofNat 64 x) = BitVec.ofNat 64 (max x y) := by
  rw [Nat.max_def]
  by_cases h : x < y
  · simp only [h, decide_true, ite_true]; rw [ite_eq_left (by omega)]
  · simp only [h, decide_false, Bool.false_eq_true, ite_false]; split <;> first | rfl | (congr 1; omega)

/-- A 32-bit signed argument that is not negative. -/
@[nocompiler_nat] theorem ofInt_of_nonneg (x : Int) (h : 0 ≤ x) : BitVec.ofInt 64 x = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat, Nat.reducePow]
  omega

/-- The sign test of a signed argument in range. -/
@[nocompiler_nat] theorem zero_slt_ofInt (x : Int) (h1 : -9223372036854775808 ≤ x) (h2 : x < 9223372036854775808) :
    (BitVec.ofNat 64 0).slt (BitVec.ofInt 64 x) = decide (0 < x) := by
  rw [BitVec.slt_eq_decide, BitVec.toInt_ofInt, show (BitVec.ofNat 64 0).toInt = 0 from rfl]
  simp only [Nat.reducePow]
  rw [Int.bmod_eq_of_le h1 h2]

@[nocompiler_nat] theorem ofNat64_toNat (x : Word) : BitVec.ofNat 64 x.toNat = x := by simp

@[nocompiler_nat] theorem intToNat_natCast (n : Nat) : (n : Int).toNat = n := rfl

/-! ## Pointer differences, for region and disjointness checks -/

@[nocompiler_nat] theorem toNat_add_ofNat_sub (a b : Word) (i : Nat) :
    ((a + BitVec.ofNat 64 i) - b).toNat = ((a - b).toNat + i) % W := by
  have : a + BitVec.ofNat 64 i - b = (a - b) + BitVec.ofNat 64 i := by bv_omega
  rw [this, BitVec.toNat_add, toNat_ofNat_mod]; simp only [Nat.reducePow]; omega
@[nocompiler_nat] theorem toNat_sub_add_ofNat (a b : Word) (j : Nat) :
    (a - (b + BitVec.ofNat 64 j)).toNat = ((a - b).toNat + (W - j % W)) % W := by
  have : a - (b + BitVec.ofNat 64 j) = (a - b) - BitVec.ofNat 64 j := by bv_omega
  rw [this, BitVec.toNat_sub, toNat_ofNat_mod]; simp only [Nat.reducePow]; omega
@[nocompiler_nat] theorem toNat_sub_self (a : Word) : (a - a).toNat = 0 := by simp

@[nocompiler_nat] theorem sub_ofNat_zero (a : Word) : a - BitVec.ofNat 64 0 = a := by simp

/-- A stack base below sp, in the normal form. -/
@[nocompiler_nat] theorem sub_ofNat_eq_add (a : Word) (k : Nat) (h : 0 < k) (h' : k < W) :
    a - BitVec.ofNat 64 k = a + BitVec.ofNat 64 (W - k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_add, toNat_ofNat_lt _ h', toNat_ofNat_lt _ (by omega)]
  simp only [Nat.reducePow]; omega

@[nocompiler_nat] theorem toNat_add_ofNat (a : Word) (i : Nat) :
    (a + BitVec.ofNat 64 i).toNat = (a.toNat + i) % W := by
  rw [BitVec.toNat_add, toNat_ofNat_mod]; simp only [Nat.reducePow]; omega

/-- `aligned` of an address in the normal form, as arithmetic (a literal jump
    target then reduces to `True` or `False`). -/
@[nocompiler_state, nocompiler_nat] theorem aligned_ofNat (n k : Nat) :
    aligned (BitVec.ofNat 64 n) k = (n % W % k = 0) := by
  simp only [aligned, toNat_ofNat_mod]

attribute [nocompiler_state] Nat.reduceMod Nat.reduceEqDiff

@[nocompiler_nat] theorem aligned_one (a : Word) : aligned a 1 = True := by
  simp [aligned, Nat.mod_one]

theorem aligned_two_of_four {x : Word} (h : aligned x 4) : aligned x 2 := by
  unfold aligned at *; omega

/-! ## Memory -/

theorem readLE_one (m : Word → Byte) (a : Word) : readLE m a 1 = (m a).toNat := by
  simp [readLE]

@[nocompiler_nat] theorem read8_eq (m : Word → Byte) (a : Word) : read8 m a = BitVec.ofNat 64 (m a).toNat := by
  simp [read8, readLE]
@[nocompiler_nat] theorem ofNat8_readLE_one (m : Word → Byte) (a : Word) : BitVec.ofNat 8 (readLE m a 1) = m a := by
  simp [readLE]
@[nocompiler_nat] theorem ofNat8_toNat (b : Byte) : BitVec.ofNat 8 b.toNat = b := by simp
@[nocompiler_nat] theorem ofNat8_mod (x : Nat) : BitVec.ofNat 8 (x % W) = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
@[nocompiler_nat] theorem ofNat8_signExtend (b : Byte) : BitVec.ofNat 8 (b.signExtend 64).toNat = b := by
  rw [BitVec.ofNat_toNat]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_signExtend, hi]
  omega

@[nocompiler_nat] theorem readBytes_length (m : Word → Byte) (a : Word) (n : Nat) :
    (readBytes m a n).length = n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [readBytes, ih]

theorem getElem_readBytes (m : Word → Byte) (a : Word) (n j : Nat) (h : j < (readBytes m a n).length) :
    (readBytes m a n)[j] = m (a + BitVec.ofNat 64 j) := by
  induction n generalizing a j with
  | zero => simp [readBytes] at h
  | succ n ih =>
    cases j with
    | zero => simp [readBytes]
    | succ j =>
      simp only [readBytes, List.getElem_cons_succ]
      rw [ih]
      · congr 1; apply BitVec.eq_of_toNat_eq; simp; omega

/-- A byte of a buffer whose contents are known. -/
theorem mem_of_readBytes {m : Word → Byte} {a : Word} {n : Nat} {L : List Byte}
    (h : readBytes m a n = L) : ∀ i, i < n → m (a + BitVec.ofNat 64 i) = L.getD i 0 := by
  intro i hi
  subst h
  rw [← getElem_readBytes m a n i (by simp [readBytes_length, hi])]
  simp [List.getD_eq_getElem?_getD, readBytes_length, hi]

theorem mem_of_readBytes_base {m : Word → Byte} {a : Word} {n : Nat} {L : List Byte}
    (h : readBytes m a n = L) (hn : 0 < n) : m a = L.getD 0 0 := by
  have := mem_of_readBytes h 0 hn
  rwa [add_ofNat_zero] at this

theorem writeLE_one (m : Word → Byte) (p : Word) (v : Nat) :
    writeLE m p v 1 = fun x => if x = p then BitVec.ofNat 8 v else m x := by
  funext x; simp [writeLE]

/-- A byte stored into a buffer whose contents are known. -/
@[nocompiler_nat] theorem readBytes_writeLE_one (m : Word → Byte) (a : Word) (v n i : Nat) (hi : i < n)
    (hn : n ≤ W) :
    readBytes (writeLE m (a + BitVec.ofNat 64 i) v 1) a n = (readBytes m a n).set i (BitVec.ofNat 8 v) := by
  apply List.ext_getElem
  · simp [readBytes_length]
  · intro j h1 h2
    rw [getElem_readBytes, List.getElem_set]
    rw [writeLE_one]
    simp only [readBytes_length] at h1
    by_cases hij : i = j
    · subst hij; simp
    · have : a + BitVec.ofNat 64 j ≠ a + BitVec.ofNat 64 i := by
        rw [Ne, add_ofNat_inj]; omega
      simp only [this, ite_false, hij]
      rw [getElem_readBytes]
@[nocompiler_nat] theorem readBytes_writeLE_one_base (m : Word → Byte) (a : Word) (v n : Nat) (hn0 : 0 < n)
    (hn : n ≤ W) : readBytes (writeLE m a v 1) a n = (readBytes m a n).set 0 (BitVec.ofNat 8 v) := by
  have := readBytes_writeLE_one m a v n 0 hn0 hn
  rwa [add_ofNat_zero] at this

theorem not_mem_of_disjoint {R : Region} {a : Word} {n k : Nat} (hd : R.Disjoint ⟨a, n⟩)
    (hk : k < n) : ¬ R.mem (a + BitVec.ofNat 64 k) := by
  unfold Region.Disjoint at hd; unfold Region.mem
  simp only at hd
  have hk' : k < W := by
    have := BitVec.isLt (R.base - a); simp only [Nat.reducePow] at this; omega
  rw [toNat_add_ofNat_sub]
  have e : (a - R.base).toNat + (R.base - a).toNat = 0 ∨
      (a - R.base).toNat + (R.base - a).toNat = W := by
    by_cases h : a = R.base
    · subst h; simp
    · right
      have h1 : a - R.base ≠ 0 := fun e => h (by bv_omega)
      rw [BitVec.toNat_sub, BitVec.toNat_sub]
      have := BitVec.isLt a; have := BitVec.isLt R.base
      have : a.toNat ≠ R.base.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
      simp only [Nat.reducePow] at *
      omega
  omega

/-- A store into one region leaves a buffer disjoint from it alone. -/
theorem readBytes_writeLE_of_disjoint {R : Region} {a : Word} {n : Nat} (hd : R.Disjoint ⟨a, n⟩)
    (m : Word → Byte) (p : Word) (v w : Nat) (hc : R.covers p w) :
    readBytes (writeLE m p v w) a n = readBytes m a n := by
  apply readBytes_congr
  intro k hk
  exact writeLE_of_not_mem hc (not_mem_of_disjoint hd hk)

theorem read64_writeLE_of_disjoint {R : Region} {a : Word} (hd : R.Disjoint ⟨a, 8⟩)
    (m : Word → Byte) (p : Word) (v w : Nat) (hc : R.covers p w) :
    read64 (writeLE m p v w) a = read64 m a := by
  unfold read64; congr 1
  apply readLE_congr
  intro k hk
  exact writeLE_of_not_mem hc (not_mem_of_disjoint hd hk)

/-- A byte of a buffer, under a store into a region disjoint from it. -/
theorem writeLE_apply_of_disjoint {R : Region} {a : Word} {n : Nat} (hd : R.Disjoint ⟨a, n⟩)
    (m : Word → Byte) (p : Word) (v w : Nat) (hc : R.covers p w) (k : Nat) (hk : k < n) :
    writeLE m p v w (a + BitVec.ofNat 64 k) = m (a + BitVec.ofNat 64 k) :=
  writeLE_of_not_mem hc (not_mem_of_disjoint hd hk)

theorem writeLE_apply_base_of_disjoint {R : Region} {a : Word} {n : Nat} (hd : R.Disjoint ⟨a, n⟩)
    (m : Word → Byte) (p : Word) (v w : Nat) (hc : R.covers p w) (hn : 0 < n) :
    writeLE m p v w a = m a := by
  have := writeLE_apply_of_disjoint hd m p v w hc 0 hn
  rwa [add_ofNat_zero] at this

/-- A loaded segment stays loaded under a store into a region disjoint from it. -/
theorem loaded_writeLE_iff {g : Segment} {R : Region} (hd : R.Disjoint g.region)
    (m : Word → Byte) (p : Word) (v w : Nat) (hc : R.covers p w) :
    g.Loaded (writeLE m p v w) ↔ g.Loaded m := by
  have hd' : R.Disjoint ⟨g.base, g.bytes.size⟩ := hd
  unfold Segment.Loaded
  constructor <;> intro h i hi
  · rw [← writeLE_of_not_mem (m := m) (v := v) hc (not_mem_of_disjoint hd' hi)]; exact h i hi
  · rw [writeLE_of_not_mem (m := m) (v := v) hc (not_mem_of_disjoint hd' hi)]; exact h i hi

/-- An array stays in memory under a store into a region that has none of its
    bytes (the form a specification states it in: `∀ x, in the array → not in R`). -/
theorem arr64_writeLE_of_outside {R : Region} {a : Word} {xs : List Word}
    (hd : ∀ x, (arrRegion a xs).mem x → ¬ R.mem x)
    (m : Word → Byte) (p : Word) (v w : Nat) (hc : R.covers p w) :
    arr64 (writeLE m p v w) a xs ↔ arr64 m a xs := by
  have key : ∀ i, i < xs.length →
      read64 (writeLE m p v w) (a + BitVec.ofNat 64 (8 * i)) = read64 m (a + BitVec.ofNat 64 (8 * i)) := by
    intro i hi
    unfold read64; congr 1
    apply readLE_congr
    intro k hk
    apply writeLE_of_not_mem hc
    apply hd
    show (_ - a).toNat < 8 * xs.length
    have e : a + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 k - a = BitVec.ofNat 64 (8 * i + k) := by
      bv_omega
    rw [e, BitVec.toNat_ofNat]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
  unfold arr64
  constructor <;> intro h i hi
  · rw [← key i hi]; exact h i hi
  · rw [key i hi]; exact h i hi

/-- A buffer inside a region with no byte in `R` reads the same after a store
    into `R`. -/
theorem readBytes_writeLE_of_outside {A R : Region} (hd : ∀ x, A.mem x → ¬ R.mem x)
    (m : Word → Byte) (p : Word) (v w : Nat) (hc : R.covers p w) {a : Word} {n : Nat}
    (hin : A.covers a n) : readBytes (writeLE m p v w) a n = readBytes m a n :=
  readBytes_congr fun k hk => writeLE_of_not_mem hc (hd _ (Region.covers_mem hin (by
    rw [show a + BitVec.ofNat 64 k - a = BitVec.ofNat 64 k by bv_omega, BitVec.toNat_ofNat]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hk)))

/-- The same, from `Region.Disjoint`. -/
theorem arr64_writeLE_iff {R : Region} {a : Word} {xs : List Word} (hd : R.Disjoint (arrRegion a xs))
    (m : Word → Byte) (p : Word) (v w : Nat) (hc : R.covers p w) :
    arr64 (writeLE m p v w) a xs ↔ arr64 m a xs := by
  refine arr64_writeLE_of_outside (fun x hx hR => ?_) m p v w hc
  have hd' : R.Disjoint ⟨a, 8 * xs.length⟩ := hd
  have hx' : (x - a).toNat < 8 * xs.length := hx
  have e : x = a + BitVec.ofNat 64 (x - a).toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
  rw [e] at hR
  exact not_mem_of_disjoint hd' hx' hR

/-- Reading back an 8-byte store. -/
@[nocompiler_nat] theorem read64_writeLE_same' (m : Word → Byte) (a : Word) (v : Nat) :
    read64 (writeLE m a v 8) a = BitVec.ofNat 64 v := by
  unfold read64
  rw [readLE_writeLE_same m a v (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.reducePow]
  omega

/-- An 8-byte load next to a store: the two do not overlap. -/
@[nocompiler_nat] theorem read64_writeLE_other' (m : Word → Byte) (p q : Word) (v w : Nat)
    (h1 : w ≤ (q - p).toNat) (h2 : 8 ≤ (p - q).toNat) :
    read64 (writeLE m p v w) q = read64 m q := by
  have hd : Region.Disjoint ⟨p, w⟩ ⟨q, 8⟩ := ⟨h1, h2⟩
  exact read64_writeLE_of_disjoint hd m p v w (by simp [Region.covers])

/-- The little-endian value of `n` bytes of a segment from offset `o`. -/
def _root_.NoCompiler.Segment.leAt (g : Segment) (o : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (g.bytes.getD o 0).toNat + 256 * g.leAt (o + 1) n

/-- Reading a constant out of a loaded segment (a table, a magic number). -/
theorem _root_.NoCompiler.Segment.readLE_of_loaded {g : Segment} {m : Word → Byte} (h : g.Loaded m) :
    ∀ (n o : Nat), o + n ≤ g.bytes.size → readLE m (g.base + BitVec.ofNat 64 o) n = g.leAt o n
  | 0, _, _ => rfl
  | n + 1, o, hon => by
    simp only [readLE, Segment.leAt]
    have e : g.base + BitVec.ofNat 64 o + 1 = g.base + BitVec.ofNat 64 (o + 1) := by
      apply BitVec.eq_of_toNat_eq; simp; omega
    rw [h o (by omega), e, Segment.readLE_of_loaded h n (o + 1) (by omega)]
    simp [Array.getD, show o < g.bytes.size by omega]

/-- An array of words, as `simp` uses it. -/
theorem arr64.read {m : Word → Byte} {a : Word} {xs : List Word} (h : arr64 m a xs) :
    ∀ i (hi : i < xs.length), read64 m (a + BitVec.ofNat 64 (8 * i)) = xs[i] := h

end Auto
end NoCompiler

/-! ## Tactics -/

namespace NoCompiler.Auto
open Lean Elab Tactic Meta


/-- `decide`, on a goal without variables only. On `x < 2^64` with `x`
    symbolic, `decide` would unfold `Nat.ble` along the literal: the blow-up
    NoCompiler/Arith.lean is about. -/
elab "nocompiler_decide_closed" : tactic => do
  let t ← instantiateMVars (← getMainTarget)
  if t.hasFVar || t.hasMVar then throwError "nocompiler_decide_closed: not closed"
  evalTactic (← `(tactic| decide))

/-- Whether `e` mentions `% 2^64`. -/
def hasWordMod (e : Expr) : Bool :=
  (e.find? fun x => x.isAppOfArity ``HMod.hMod 6 &&
    (x.getArg! 5).nat? == some 18446744073709551616 ||
    (x.isAppOfArity ``HMod.hMod 6 && match (x.getArg! 5).rawNatLit? with
      | some n => n == 18446744073709551616 | none => false)).isSome

/-- `omega` on the hypotheses that bear on the goal: those sharing a variable
    with it (two rounds), and none with `% 2^64` unless the goal has it.
    `omega` reads every arithmetic hypothesis in context, and the proofs it
    writes grow with them; along a run there are many, and thousands of side
    conditions. -/
elab "nocompiler_omega" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let t ← instantiateMVars (← g.getType)
    let goalMod := hasWordMod t
    let mut vars := (collectFVars {} t).fvarSet
    let hyps ← (← getLCtx).getFVarIds.filterM fun f => do
      let d ← f.getDecl
      if d.isImplementationDetail then return false
      return (← isProp d.type)
    for _ in [0:2] do
      for f in hyps do
        let ty ← instantiateMVars (← f.getType)
        let fv := (collectFVars {} ty).fvarSet
        if fv.toList.any (vars.contains ·) && (goalMod || !hasWordMod ty) then
          vars := fv.toList.foldl (fun acc x => acc.insert x) vars
    let mut g := g
    for f in hyps.reverse do
      let ty ← instantiateMVars (← f.getType)
      let fv := (collectFVars {} ty).fvarSet
      let keep := fv.toList.any (vars.contains ·) && (goalMod || !hasWordMod ty)
      unless keep do
        try g ← g.clear f catch _ => pure ()
    let gs ← evalTacticAt (← `(tactic| omega)) g
    unless gs.isEmpty do throwError "nocompiler_omega: goals left"

/-- Side conditions of the normal form's rewrites: bounds, by evaluation or
    linear arithmetic over the hypotheses in context. -/
macro "nocompiler_disch" : tactic => `(tactic| first
  | nocompiler_decide_closed
  | nocompiler_omega
  | (simp (disch := nocompiler_decide_closed) only [Region.covers, Region.mem, Spec.stackRegion, Reg.sp,
      nocompiler_nat, Nat.reducePow, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod]; nocompiler_omega))

/-- The step normaliser of NoCompiler/Tactic.lean (`nocompiler_norm`), followed by the word
    normal form. Every pass may make no progress. -/
syntax "nocompiler_anorm" (" [" Lean.Parser.Tactic.simpArg,* "]")? (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| nocompiler_anorm) => `(tactic| nocompiler_anorm [])
  | `(tactic| nocompiler_anorm $loc:location) => `(tactic| nocompiler_anorm [] $loc:location)
  | `(tactic| nocompiler_anorm [$ts,*]) => `(tactic| (
      (try simp only [nocompiler_sem])
      (try simp (config := { decide := true }) only [nocompiler_state, nocompiler_image, $ts,*])
      (try simp only [nocompiler_lit])
      (try simp (disch := nocompiler_disch) only [nocompiler_nat, nocompiler_lit,
        Nat.add_zero, Nat.zero_add, Nat.sub_self, Nat.sub_zero, Nat.mul_zero, Nat.zero_mod, $ts,*])
      (try simp (config := { decide := true }) only [nocompiler_state, nocompiler_image, $ts,*])))
  | `(tactic| nocompiler_anorm [$ts,*] $loc:location) => `(tactic| (
      (try simp only [nocompiler_sem] $loc:location)
      (try simp (config := { decide := true }) only [nocompiler_state, nocompiler_image, $ts,*] $loc:location)
      (try simp only [nocompiler_lit] $loc:location)
      (try simp (disch := nocompiler_disch) only [nocompiler_nat, nocompiler_lit,
        Nat.add_zero, Nat.zero_add, Nat.sub_self, Nat.sub_zero, Nat.mul_zero, Nat.zero_mod, $ts,*]
        $loc:location)
      (try simp (config := { decide := true }) only [nocompiler_state, nocompiler_image, $ts,*] $loc:location)))

/-- `nocompiler_anorm` without evaluation by `decide`: for verification conditions,
    where `decide` would try to evaluate the specification's functions. -/
syntax "nocompiler_vnorm" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic
macro_rules
  | `(tactic| nocompiler_vnorm [$ts,*]) => `(tactic| (
      (try simp only [nocompiler_sem])
      (try simp (disch := nocompiler_decide_closed) only [nocompiler_state, nocompiler_image, $ts,*])
      (try simp only [nocompiler_lit])
      (try simp (disch := nocompiler_disch) only [nocompiler_nat, nocompiler_lit,
        Nat.add_zero, Nat.zero_add, Nat.sub_self, Nat.sub_zero, Nat.mul_zero, Nat.zero_mod, $ts,*])
      (try simp (disch := nocompiler_decide_closed) only [nocompiler_state, nocompiler_image, nocompiler_lit, $ts,*])))

/-- A branch condition as a fact about the normal form. -/
syntax "nocompiler_cond" (" [" Lean.Parser.Tactic.simpArg,* "]")? Lean.Parser.Tactic.location : tactic
macro_rules
  | `(tactic| nocompiler_cond [$ts,*] $loc:location) => `(tactic| (
      nocompiler_anorm [$ts,*] $loc:location
      (try simp only [decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true',
        Bool.not_eq_false', Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        Bool.not_false, decide_not, Bool.not_not, not_and, not_or, Classical.not_not, ne_eq,
        Bool.and_eq_false_iff, Bool.or_eq_false_iff, decide_eq_false_iff_not,
        Bool.false_eq_true, false_and, and_false, not_false_eq_true, true_and, and_true] $loc:location)))

/-- A load or store's permission, from the specification's regions. -/
syntax "nocompiler_perm" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic
macro_rules
  | `(tactic| nocompiler_perm [$ts,*]) => `(tactic| (
      simp (disch := nocompiler_disch) only [Perm.canRead, Perm.canWrite, Spec.perm, Spec.stackRegion,
        arrRegion, Segment.region, List.size_toArray, List.length_cons, List.length_nil, List.cons_append, List.nil_append, List.append_nil, List.exists_mem_cons, List.mem_cons, exists_eq_or_imp, exists_eq_left, List.mem_nil_iff,
        List.not_mem_nil, exists_false, false_and, or_false, false_or, Region.covers, nocompiler_nat,
        Nat.reducePow, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.add_zero, Nat.zero_add, $ts,*]
      omega))

/-- A load or store's alignment, from the alignment of its base. -/
macro "nocompiler_align" : tactic => `(tactic| (
  simp (disch := nocompiler_disch) only [aligned, nocompiler_nat, Nat.reducePow, Nat.reduceMod, Nat.add_zero]
  omega))

/-! ### The run -/

inductive Mode | start | body

/-- The step relation a run is about: `Reach` over a `Code`, or another one
    with the same shape (NoCompiler/Ext/Rvc.lean, compressed code). -/
structure Flavor where
  reach : Name := ``Reach
  opt : Name := ``Reach.opt
  instr : Name := ``Code.instr
  exec : Name := ``Exec
  execStep : Name := ``Reach.exec_step
  done : Name := ``Reach.done
  optSome : Name := ``Reach.opt_some
  optAligned : Name := ``Reach.opt_aligned
  cutpoints : Name := ``Reach.cutpoints
  /-- A callee's theorem, its call rule, the syscall step, the entry
      conditions, and the facts about the return address. -/
  verified : Name := ``VerifiedImg
  callRule : Name := ``VerifiedImg.call
  sysStep : Name := ``Reach.sys_step
  entry : Name := ``Entry
  retMask : Name := ``ret_mask
  retTwo : Name := ``aligned_two_of_four

structure Ctx where
  fl : Flavor := {}
  /-- Debugging (`nocompiler.auto.debugKernel`): the goals of the run, in order. -/
  log : Option (IO.Ref (Array (MVarId × String))) := none
  /-- How many runs have ended at each (origin, end), for distinct goal names. -/
  ends : Option (IO.Ref (Std.HashMap String Nat)) := none
  /-- The functions it calls: entry, `VerifiedImg` theorem, specification. -/
  callees : Array (Nat × Term × Name) := #[]
  /-- The addresses of its ECALLs. -/
  ecalls : List Nat := []
  /-- Its frame: the conjuncts `nocompiler_auto` adds to every invariant (empty if none). -/
  frameN : Nat := 0
  /-- The loop heads: where a run stops and the invariant is due. -/
  cuts : List Nat
  /-- Rewrites for every normalisation: the caller's facts, the pc and the
      cut point's facts. -/
  facts : Array Term
  /-- The registers the function writes. -/
  rs : Term
  /-- The entry state and its `Entry` hypothesis. -/
  s0 : Term
  he : Term
  spec : Ident
  hR : Ident
  mode : Mode
  /-- Where the run started, for naming what it leaves. -/
  origin : String
  /-- The function's labels: cut points are named by them. -/
  labels : List (String × Nat) := []
  /-- The function's entry: other points are named by their offset from it. -/
  entryN : Nat := 0

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

abbrev SimpArgs := Syntax.TSepArray
  [``Lean.Parser.Tactic.simpStar, ``Lean.Parser.Tactic.simpErase, ``Lean.Parser.Tactic.simpLemma] ","

def simpArgs (ts : Array Term) : TacticM SimpArgs := do
  let arr ← ts.mapM fun t => do
    let l ← `(Lean.Parser.Tactic.simpLemma| $t:term)
    return (⟨l.raw⟩ : TSyntax [``Lean.Parser.Tactic.simpStar, ``Lean.Parser.Tactic.simpErase,
      ``Lean.Parser.Tactic.simpLemma])
  return Syntax.TSepArray.ofElems arr

register_option nocompiler.auto.trace : Bool := { defValue := false, descr := "trace nocompiler_auto" }
register_option nocompiler.auto.debugKernel : Bool :=
  { defValue := false, descr := "debugging only: after the run, close what is left with sorry and \
      kernel-check the proof of every step bottom-up, tracing the time (adds declarations)" }
register_option nocompiler.auto.traceFile : String :=
  { defValue := "", descr := "append nocompiler_auto's trace to this file as it runs" }

def traceLine (msg : String) : CoreM Unit := do
  let f := nocompiler.auto.traceFile.get (← getOptions)
  if f.isEmpty then return
  let h ← IO.FS.Handle.mk f .append
  h.putStrLn msg
  h.flush



/-- Debugging: the proof a step assigned to `g`, with what is still open
    replaced by `sorry`, checked by the kernel as a theorem of its own. -/
partial def zapMVars (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if !e.hasMVar then return e
  Meta.transform e (pre := fun x => do
    if x.getAppFn.isMVar then
      return .done (← mkSorry (← zapMVars (← inferType x)) false)
    else return .continue)

def kernelCheckStep (g : MVarId) : TermElabM Nat := g.withContext do
  let e ← zapMVars (mkMVar g)
  let ty ← zapMVars (← g.getType)
  let fvs := (← getLCtx).getFVars
  let val ← zapMVars (← mkLambdaFVars fvs e)
  let typ ← zapMVars (← mkForallFVars fvs ty)
  let val ← instantiateMVars val
  let typ ← instantiateMVars typ
  if val.hasMVar || typ.hasMVar then traceLine s!"[kernel] still mvars: level {val.hasLevelMVar || typ.hasLevelMVar}"
  let base := (← Term.getDeclName?).getD `nocompiler
  let n := base ++ (← mkFreshUserName `nocompiler_debug_step).eraseMacroScopes ++ Name.mkSimple s!"s{← IO.monoNanosNow}"
  let t0 ← IO.monoMsNow
  try addDecl (.thmDecl { name := n, levelParams := [], type := typ, value := val })
  catch ex => traceLine s!"[kernel] error {(← ex.toMessageData.toString).take 300}"
  return (← IO.monoMsNow) - t0

def run (g : MVarId) (tac : TSyntax `tactic) : TacticM (List MVarId) := do
  if nocompiler.auto.trace.get (← getOptions) then
    let t ← IO.monoMsNow
    if !(nocompiler.auto.traceFile.get (← getOptions)).isEmpty then
      let gt := toString (← g.withContext (Meta.ppExpr (← instantiateMVars (← g.getType))))
      traceLine s!"[goal] {(gt.replace "\n" " ").take 40000}"
    let gs ← withEnableInfoTree false (evalTacticAt tac g)
    let kt := 0
    traceLine s!"[nocompiler_auto {(← IO.monoMsNow) - t} ms, kernel {kt} ms] {tac.raw.prettyPrint.pretty 100 |>.take 160}"
    return ← gs.filterM fun g => return !(← g.isAssigned)
  -- No info tree: it would keep every intermediate goal of every step.
  let gs ← withEnableInfoTree false (evalTacticAt tac g)
  gs.filterM fun g => return !(← g.isAssigned)

/-- `Reach c P D R s` or `Reach.opt c P D R os`. -/
def goalHead (fl : Flavor) (g : MVarId) : MetaM (Option (Name × Expr)) := do
  let t ← instantiateMVars (← g.getType)
  let t := t.consumeMData
  if t.isAppOfArity fl.reach 5 then return some (fl.reach, t.appArg!)
  if t.isAppOfArity fl.opt 5 then return some (fl.opt, t.appArg!)
  return none

/-- The pc of a state in the step tactics' normal form, if it is a literal:
    `(..).setPc p`, or a variable with a hypothesis `s.pc = p`. -/
def pcOf (s : Expr) : MetaM (Option Nat) := do
  let s ← instantiateMVars s
  if s.isAppOfArity ``State.setPc 2 then
    return (← getBitVecValue? s.appArg!).map (·.2.toNat)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if let some (_, l, r) := ty.eq? then
      if l.isAppOfArity ``State.pc 1 && l.appArg! == s then
        if let some ⟨_, v⟩ ← getBitVecValue? r then return some v.toNat
  return none

/-- `tag`, or `tag_b`, `tag_c`, ... when several runs end at the same place. -/
def endTag (cx : Ctx) (tag : String) : IO String := do
  let some r := cx.ends | return tag
  let n := (← r.get).getD tag 0
  r.modify (·.insert tag (n + 1))
  return if n = 0 then tag else s!"{tag}_{Char.ofNat (97 + n)}"

/-- A point's name in goal names: its label, else its offset from the
    function's entry (`x74`), so that names do not change when the function
    is linked elsewhere. -/
def Ctx.name (cx : Ctx) (pc : Nat) : String :=
  match cx.labels.find? (·.2 == pc) with
  | some (l, _) => l
  | none => "x" ++ ((Nat.toDigits 16 ((pc + 2 ^ 64 - cx.entryN) % 2 ^ 64)).asString)

def tagged (gs : List MVarId) (tag : String) : MetaM (List MVarId) := do
  let mut i := 0
  for g in gs do
    let n := if gs.length = 1 then tag else s!"{tag}_{i}"
    g.setTag (Name.mkSimple n)
    i := i + 1
  return gs

/-- Split a goal into its conjuncts and introduce its existential witnesses as
    unification variables; solve every equation conjunct that unification can
    (which is how witnesses are found: a register equal to `BitVec.ofNat 64 ?k`).
    Returns the conjuncts left. -/
partial def splitGoal (g : MVarId) : MetaM (List MVarId) := g.withContext do
  let t ← whnfR (← instantiateMVars (← g.getType))
  match t with
  | .app (.app (.const ``Exists [u]) α) p =>
    let n := match p with | .lam n .. => n | _ => `w
    let w ← mkFreshExprMVar α (kind := .natural) (userName := n)
    let h ← mkFreshExprSyntheticOpaqueMVar (p.beta #[w]) (← g.getTag)
    g.assign (mkApp4 (.const ``Exists.intro [u]) α p w h)
    splitGoal h.mvarId!
  | .app (.app (.const ``And []) a) b =>
    let ga ← mkFreshExprSyntheticOpaqueMVar a (← g.getTag)
    let gb ← mkFreshExprSyntheticOpaqueMVar b (← g.getTag)
    g.assign (mkApp4 (.const ``And.intro []) a b ga gb)
    return (← splitGoal ga.mvarId!) ++ (← splitGoal gb.mvarId!)
  | .const ``True [] => g.assign (.const ``True.intro []); return []
  | _ =>
    if let some (_, l, r) := t.eq? then
      if (← withReducible (isDefEq l r)) then
        g.assign (← mkEqRefl (← instantiateMVars l))
        return []
    return [g]

/-- After the witnesses are known: normalise each conjunct again and close
    what arithmetic closes. -/
def finish (cx : Ctx) (gs : List MVarId) : TacticM (List MVarId) := do
  let fs ← simpArgs cx.facts
  let mut out := []
  for g in gs do
    if ← g.isAssigned then continue
    if let some r := cx.log then r.modify (·.push (g, s!"finish conjunct"))
    -- Each attempt bounded: a verification condition is about the
    -- specification's own functions, which nothing here should unfold.
    let r ← run g (← `(tactic| first
        | (set_option maxHeartbeats 200000 in with_reducible rfl)
        | (set_option maxHeartbeats 200000 in with_reducible assumption)
        | (set_option maxHeartbeats 200000 in omega)
        | skip))
    let r ← r.foldlM (fun acc g => do return acc ++ (← run g (← `(tactic|
        first | (set_option maxHeartbeats 2000000 in nocompiler_vnorm [$fs,*]) | skip)))) []
    let r ← r.foldlM (fun acc g => do return acc ++ (← run g (← `(tactic| first
        | (set_option maxHeartbeats 1000000 in
            simp (disch := nocompiler_disch) only [ofNat_inj, add_ofNat_inj, eq_add_ofNat_iff,
              add_ofNat_eq_iff, List.length_set, readBytes_length])
        | skip)))) []
    let r ← r.foldlM (fun acc g => do return acc ++ (← run g (← `(tactic| first
        | (set_option maxHeartbeats 200000 in with_reducible rfl)
        | (set_option maxHeartbeats 200000 in omega)
        | skip)))) []
    out := out ++ r
  return out

/-- Split goals into conjuncts and close what `finish` closes; if that leaves a
    witness of an `∃` undetermined, undo it and return the goals unsplit, so
    the user writes the witnesses by name. -/
def splitOrKeep (cx : Ctx) (r : List MVarId) : TacticM (List MVarId) := do
  let st ← saveState
  let r' ← r.foldlM (fun acc g => return acc ++ (← splitGoal g)) []
  let r' ← finish cx r'
  if ← r'.anyM (fun g => do return (← instantiateMVars (← g.getType)).hasExprMVar) then
    st.restore
    return r
  return r'

/-- The names of the syscall numbers, for the simp sets of a syscall step. -/
def sysNames : TacticM (Array Term) := return #[← `(sysExit), ← `(sysExitGroup), ← `(sysRead), ← `(sysWrite)]

def exitTac : TacticM (TSyntax `tactic) :=
  `(tactic| simp only [State.setReg_exit, State.setPc_exit', State.setMem_exit', State.emit_exit',
      sysRet_exit, $(mkIdent `nocompiler_hx):ident])

/-- The run has reached a cut point: the invariant (and the measure) of the
    state reached. -/
def closeCut (cx : Ctx) (g : MVarId) (pc : Nat) : TacticM (List MVarId) := do
  if let some r := cx.log then r.modify (·.push (g, s!"cut {cx.origin} -> {hex pc}"))
  let fs ← simpArgs cx.facts
  let hR := cx.hR
  let tag ← endTag cx s!"{cx.origin}_to_{cx.name pc}"
  let gs ← run g (← `(tactic| (subst $hR:ident; refine $(mkIdent cx.fl.done) ?_; (try dsimp only); right)))
  let some g := gs.head? | return []
  let vc (g : MVarId) : TacticM (List MVarId) := do
    let r ← run g (← `(tactic| nocompiler_vnorm [$fs,*]))
    splitOrKeep cx r
  match cx.mode with
  | .start =>
    let [gx, gsame, gf, gi] ← run g (← `(tactic| refine ⟨?_, ?_, ?_, ?_⟩)) | throwError "nocompiler_auto: cut"
    let r1 ← run gx (← exitTac)
    let r2 ← run gsame (← `(tactic| nocompiler_same))
    let rf ← vc gf
    let r3 ← vc gi
    return (← tagged (r1 ++ r2 ++ r3) tag) ++ (← tagged rf (tag ++ "_frame"))
  | .body =>
    let [gx, gsame, gf, gi, gm] ← run g (← `(tactic| refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩))
      | throwError "nocompiler_auto: cut"
    let r1 ← run gx (← exitTac)
    let r2 ← run gsame (← `(tactic| nocompiler_same))
    let rf ← vc gf
    let r3 ← vc gi
    let r4 ← run gm (← `(tactic| (nocompiler_vnorm [$fs,*]; (try omega))))
    let r4 ← tagged r4 (tag ++ "_measure")
    return (← tagged (r1 ++ r2 ++ r3) tag) ++ (← tagged rf (tag ++ "_frame")) ++ r4

/-- The run has returned (`jalr zero, 0(ra)`): the postcondition. -/
def closeRet (cx : Ctx) (g : MVarId) (from_ : Nat) : TacticM (List MVarId) := do
  if let some r := cx.log then r.modify (·.push (g, s!"ret {cx.origin} at {hex from_}"))
  let fs ← simpArgs cx.facts
  let hR := cx.hR
  let he := cx.he
  let rs := cx.rs
  let sp := cx.spec
  let tag ← endTag cx s!"{cx.origin}_ret_{cx.name from_}"
  let gs ← run g (← `(tactic| (subst $hR:ident; refine $(mkIdent cx.fl.done) ?_; (try dsimp only); left)))
  let some g := gs.head? | return []
  let [gf, gx, gp, gpres, gpost] ← run g (← `(tactic| refine ⟨.inl ?_, .inl ⟨?_, ?_, ?_, ?_⟩⟩))
    | throwError "nocompiler_auto: ret"
  if let some r := cx.log then
    for (x, nm) in [(gf, "final"), (gx, "exit"), (gp, "pc"), (gpres, "preserved"), (gpost, "post")] do
      r.modify (·.push (x, s!"ret {nm}"))
  let r1 ← run gf (← `(tactic| (nocompiler_anorm [$fs,*]; exact ($he).ret)))
  let r2 ← run gx (← exitTac)
  let r3 ← run gp (← `(tactic| (nocompiler_anorm [$fs,*]; (try rfl))))
  let r4 ← run gpres (← `(tactic| first
    | exact Same.preserved (rs := $rs) (by nocompiler_same) (by decide)
    | (refine preserved_of_regs ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
       first
        | (refine Same.reg_eq (rs := $rs) ?_ _ (by decide); nocompiler_same)
        | (nocompiler_vnorm [$fs,*]; done)
        | skip)))
  let r4 ← tagged r4 s!"{tag}_preserved"
  let r5 ← run gpost (← `(tactic| (simp only [$sp:ident]; nocompiler_vnorm [$fs,*])))
  let r5 ← splitOrKeep cx r5
  tagged (r1 ++ r2 ++ r3 ++ r4 ++ r5) tag

/-- One instruction: its side conditions discharged (or left, named), and
    the goal for the state after it. -/
def step (cx : Ctx) (g : MVarId) (pc : Nat) : TacticM (MVarId × List MVarId) := do
  if let some r := cx.log then r.modify (·.push (g, s!"step at {hex pc}"))
  let fs ← simpArgs cx.facts
  let sp := cx.spec
  let gs ← run g (← `(tactic| refine' $(mkIdent cx.fl.execStep) ?_ ?_ ?_ ?_ ?_))
  let find (n : Name) : MetaM (Option MVarId) := gs.findM? fun g => do
    let t ← instantiateMVars (← g.getType)
    let h := if t.isAppOf ``Eq then
        (if (t.getArg! 1).isAppOf cx.fl.instr then `hi else `hx)
      else if t.isAppOf ``Dom.mem then `hd
      else if t.isAppOf ``InstrOk then `hok
      else if t.isAppOf cx.fl.opt then `h
      else `i
    return h == n
  let some ghi ← find `hi | throwError "nocompiler_auto: step at {hex pc}"
  if let some r := cx.log then
    for (n, nm) in [(`hi, "hi"), (`hd, "hd"), (`hx, "hx"), (`hok, "hok")] do
      if let some x ← find n then r.modify (·.push (x, s!"{nm} at {hex pc}"))
  let _ ← run ghi (← `(tactic| ((try nocompiler_anorm [$fs,*]) <;> rfl)))
  let mut left := []
  if let some ghd ← find `hd then
    left := left ++ (← run ghd (← `(tactic| ((try nocompiler_anorm [$fs,*]) <;> decide))))
  if let some ghx ← find `hx then
    -- By the projection lemmas, not by `assumption` up to unfolding: the kernel
    -- would replay that unfolding through every update of the state.
    left := left ++ (← run ghx (← `(tactic| (simp only [State.setReg_exit, State.setPc_exit',
      State.setMem_exit', State.emit_exit', sysRet_exit, $(mkIdent `nocompiler_hx):ident]))))
  if let some ghok ← find `hok then
    unless ← ghok.isAssigned do
      let r ← run ghok (← `(tactic| (nocompiler_anorm [$fs,*]; (try trivial))))
      let r ← r.foldlM (fun acc g => do
        return acc ++ (← run g (← `(tactic| first | (nocompiler_perm [$sp:ident, $fs,*]) | skip)))) []
      left := left ++ (← tagged r s!"perm_{hex pc}")
  let some gh ← find `h | throwError "nocompiler_auto: step at {hex pc}"
  let passes : List (TSyntax `tactic) := [
    ← `(tactic| (try simp only [nocompiler_sem])),
    ← `(tactic| (try simp (config := { decide := true }) only [nocompiler_state, nocompiler_image, $fs,*])),
    ← `(tactic| (try simp only [nocompiler_lit])),
    ← `(tactic| (try simp (disch := nocompiler_disch) only [nocompiler_nat, nocompiler_lit,
        Nat.add_zero, Nat.zero_add, Nat.sub_self, Nat.sub_zero, Nat.mul_zero, Nat.zero_mod, $fs,*])),
    ← `(tactic| (try simp (config := { decide := true }) only [nocompiler_state, nocompiler_image, $fs,*]))]
  let mut gh := gh
  let mut k := 0
  for t in passes do
    if let some r := cx.log then r.modify (·.push (gh, s!"pass {k} at {hex pc}"))
    let [g'] ← run gh t | throwError "nocompiler_auto: the step at {hex pc} closed or split its goal"
    gh := g'
    k := k + 1
  return (gh, left)

set_option hygiene false in
/-- The run has ended the process: the specification's `onExit`. -/
def closeExit (cx : Ctx) (g : MVarId) (at_ : Nat) : TacticM (List MVarId) := do
  let fs ← simpArgs cx.facts
  let hR := cx.hR
  let sp := cx.spec
  let tag ← endTag cx s!"{cx.origin}_exit_{cx.name at_}"
  let gs ← run g (← `(tactic| (subst $hR:ident; refine $(mkIdent cx.fl.done) ?_; (try dsimp only); left)))
  let some g := gs.head? | return []
  let [g1, g2, g3] ← run g (← `(tactic| refine ⟨.inr ?_, .inr ⟨?_, ?_⟩⟩)) | throwError "nocompiler_auto: exit"
  let ne ← `(tactic| (simp only [State.emit_exit_halt, State.setPc_exit', State.setMem_exit',
      State.setReg_exit, State.emit_exit']; exact Option.some_ne_none _))
  let r1 ← run g1 ne
  let r2 ← run g2 ne
  let r3 ← run g3 (← `(tactic| (simp only [$sp:ident]; nocompiler_vnorm [State.emit_exit_halt, $fs,*])))
  let r3 ← splitOrKeep cx r3
  tagged (r1 ++ r2 ++ r3) tag

set_option hygiene false in
/-- An ECALL: every outcome the environment model allows. Returns the goals to
    run on (one per outcome that is possible here) and the goals left. -/
def stepSys (cx : Ctx) (g : MVarId) (pc : Nat) : TacticM (List MVarId × List MVarId) := do
  let fs ← simpArgs (cx.facts ++ (← sysNames))
  let sp := cx.spec
  let gs ← run g (← `(tactic| refine $(mkIdent cx.fl.sysStep) ?_ ?_ ?_ ?_ ?_ ?_))
  let kind (g : MVarId) : MetaM String := do
    let t ← whnfR (← instantiateMVars (← g.getType))
    if t.isAppOf ``Dom.mem then return "hd"
    if t.isAppOf ``SysOk then return "hok"
    if t.isAppOf ``Exists then return "hex"
    if t.isForall then return "k"
    if t.isAppOf ``Eq then
      return if (t.getArg! 1).isAppOf cx.fl.instr then "hi" else "hx"
    return "?"
  let mut left := []
  let mut cont := []
  for g in gs do
    if ← g.isAssigned then continue
    match ← kind g with
    | "hd" => left := left ++ (← run g (← `(tactic| ((try nocompiler_anorm [$fs,*]) <;> decide))))
    | "hx" => left := left ++ (← run g (← exitTac))
    | "hi" => left := left ++ (← run g (← `(tactic| ((try nocompiler_anorm [$fs,*]) <;> rfl))))
    | "hok" =>
      let r ← run g (← `(tactic| (simp only [SysOk]; nocompiler_anorm [$fs,*])))
      let r ← r.foldlM (fun acc g => do
        return acc ++ (← run g (← `(tactic| (try simp only [false_implies, true_implies, and_true, true_and, and_self]))))) []
      let r ← r.foldlM (fun acc g => do
        return acc ++ (← run g (← `(tactic| first | trivial | (nocompiler_perm [$sp:ident, $fs,*]) | skip)))) []
      left := left ++ (← tagged r s!"perm_{hex pc}")
    | "hex" =>
      -- As tactics, not `exact` with `by` inside: a `by` block that fails in
      -- a term is logged and replaced by `sorry`, and `first` would not move
      -- on to the next outcome.
      left := left ++ (← run g (← `(tactic| first
        | (refine ⟨_, Sys.exit (Or.inr ?_)⟩; nocompiler_anorm [$fs,*]; done)
        | (refine ⟨_, Sys.exit (Or.inl ?_)⟩; nocompiler_anorm [$fs,*]; done)
        | (refine ⟨_, Sys.readErr 1 ?_ (by decide) (by decide)⟩; nocompiler_anorm [$fs,*]; done)
        | (refine ⟨_, Sys.writeErr 1 ?_ (by decide) (by decide)⟩; nocompiler_anorm [$fs,*]; done))))
    | _ =>
      let ds := mkIdent `ds
      let r ← run g (← `(tactic| intro nocompiler_s' nocompiler_hs))
      let r ← r.foldlM (fun acc g => do return acc ++ (← run g (← `(tactic|
        rcases nocompiler_hs with ⟨sys_n, nocompiler_h7, nocompiler_hle, nocompiler_hmax, nocompiler_hpos⟩ | ⟨sys_err, nocompiler_h7, nocompiler_he1, nocompiler_he2⟩ |
          ⟨$ds:ident, nocompiler_h7, nocompiler_hlen, nocompiler_hmax⟩ | ⟨sys_err, nocompiler_h7, nocompiler_he1, nocompiler_he2⟩ | ⟨nocompiler_h7⟩)))) []
      for g' in r do
        -- An outcome for another syscall number: its hypothesis is false.
        let r' ← run g' (← `(tactic| nocompiler_cond [$fs,*] at nocompiler_h7))
        for g'' in r' do
          let mut gg := [g'']
          for t in [← `(tactic| (try nocompiler_cond [$fs,*] at nocompiler_hlen)), ← `(tactic| (try nocompiler_cond [$fs,*] at nocompiler_hle)),
              ← `(tactic| (try nocompiler_cond [$fs,*] at nocompiler_he1)), ← `(tactic| (try nocompiler_cond [$fs,*] at nocompiler_he2)),
              ← `(tactic| (try nocompiler_anorm [$fs,*] at nocompiler_hpos)),
              ← `(tactic| (try nocompiler_anorm [$fs,*]))] do
            gg ← gg.foldlM (fun acc g => return acc ++ (← run g t)) []
          cont := cont ++ gg
  return (cont, left)

/-- Destructure a hypothesis that is a conjunction into `name_1`, `name_2`, ... -/
partial def destructAnd (g : MVarId) (h : Ident) (name : String) (k : Nat := 1) : TacticM (MVarId × Array Term) := do
  let t ← g.withContext do
    let some d := (← getLCtx).findFromUserName? h.getId | return Expr.const ``True []
    whnfR (← instantiateMVars d.type)
  if t.isAppOfArity ``And 2 then
    let hk := mkIdent (Name.mkSimple s!"{name}_{k}")
    let [g'] ← run g (← `(tactic| obtain ⟨$hk:ident, $h:ident⟩ := $h:ident)) | return (g, #[])
    let (g'', fs) ← destructAnd g' h name (k + 1)
    return (g'', #[(← `($hk))] ++ fs)
  else if t.isAppOfArity ``Exists 2 then
    -- A witness, named as the specification names it.
    let w := match t.appArg! with
      | .lam n .. => mkIdent n
      | _ => mkIdent (Name.mkSimple s!"{name}_w{k}")
    let [g'] ← run g (← `(tactic| obtain ⟨$w:ident, $h:ident⟩ := $h:ident)) | return (g, #[])
    destructAnd g' h name k
  else
    return (g, #[← `($h)])

def natLit (n : Nat) : Term := Syntax.mkNumLit (toString n)


set_option hygiene false in
/-- A call (or tail call) to a function with a `VerifiedImg` theorem: the
    callee's specification in place of its code. Returns the goals to run on
    after the call, with their contexts, and the goals left. -/
def closeCall (cx : Ctx) (g : MVarId) (pc : Nat) (thm : Term) (calleeSpec : Name) (s1 : Expr) :
    TacticM (List (MVarId × Ctx) × List MVarId) := do
  let fs ← simpArgs cx.facts
  let sp := cx.spec
  let he := cx.he
  let rs := cx.rs
  let csp := mkIdent calleeSpec
  let cname := match thm.raw.getId with
    | .str _ n => n
    | _ => hex pc
  let tag ← endTag cx s!"{cx.origin}_call_{cname}"
  let cdoneI := mkIdent (Name.mkSimple s!"nocompiler_cdone_{tag}")
  let cframeI := mkIdent (Name.mkSimple s!"nocompiler_cframe_{tag}")
  let cxI := mkIdent (Name.mkSimple s!"nocompiler_cx_{tag}")
  let cpcI := mkIdent (Name.mkSimple s!"nocompiler_cpc_{tag}")
  let cpresI := mkIdent (Name.mkSimple s!"nocompiler_cpres_{tag}")
  let cpostI := mkIdent (Name.mkSimple s!"nocompiler_cpost_{tag}")
  let cexI := mkIdent (Name.mkSimple s!"nocompiler_cex_{tag}")
  let conI := mkIdent (Name.mkSimple s!"nocompiler_con_{tag}")
  let cpI := mkIdent (Name.mkSimple s!"nocompiler_cp_{tag}")
  let cmemI := mkIdent (Name.mkSimple s!"nocompiler_cmem_{tag}")
  let cS := mkIdent (Name.mkSimple s!"nocompiler_sc_{tag}")
  let gs ← run g (← `(tactic| refine' $(mkIdent cx.fl.callRule) $thm _ ?_ ?_ ?_ ?_ ?_))
  let kind (g : MVarId) : MetaM String := do
    let t0 ← instantiateMVars (← g.getType)
    if t0.isAppOf ``Spec.pre then return "pre"
    let t ← whnfR t0
    if t.isAppOf cx.fl.entry then return "he"
    if t.isAppOf ``Dom.sub then return "hD"
    if t.isAppOf ``Perm.le then return "hP"
    if t.isForall then return "k"
    return "arg"
  let mut byKind : Std.HashMap String MVarId := {}
  for g in gs do
    let k ← kind g
    byKind := byKind.insert k g
  -- The callee's arguments: a structure of unknowns, found by unification below.
  if let some ga := byKind["arg"]? then
    ga.withContext do
      let ty ← whnf (← instantiateMVars (← ga.getType))
      -- A structure, or any inductive with one constructor (PUnit is not a structure).
      if let .const n lvls := ty.getAppFn then
        if let some (.inductInfo iv) := (← getEnv).find? n then
          if let [ctorName] := iv.ctors then
            let c := mkConst ctorName lvls
            let (ms, _, _) ← forallMetaTelescope (← instantiateForall (← inferType c) ty.getAppArgs)
            ga.assign (mkAppN (mkAppN c ty.getAppArgs) ms)
  let mut left := []
  if let some gp := byKind["pre"]? then
    let r ← run gp (← `(tactic| (simp only [$csp:ident]; nocompiler_vnorm [$fs,*])))
    let r ← splitOrKeep cx r
    left := left ++ (← tagged r s!"{tag}_pre")
  if let some gh := byKind["he"]? then
    let [g1, g2, g3, g4, g5] ← run gh (← `(tactic| refine ⟨?_, ?_, ?_, ?_, ?_⟩)) | throwError "nocompiler_auto: Entry"
    left := left ++ (← run g1 (← `(tactic| ((try nocompiler_anorm [$fs,*]) <;> rfl))))
    left := left ++ (← run g2 (← exitTac))
    left := left ++ (← run g3 (← `(tactic| ((try nocompiler_anorm [$fs,*]) <;> first
      | decide | exact NoCompiler.Auto.Dom.not_mem_of_sub (Dom.sub_of_ranges (by decide)) ($he).ret))))
    left := left ++ (← run g4 (← `(tactic| ((try nocompiler_anorm [$fs,*]) <;> first
      | decide | exact ($he).retAligned | trivial))))
    left := left ++ (← run g5 (← `(tactic| ((try nocompiler_anorm [$fs,*]) <;> nocompiler_align))))
  if let some gd := byKind["hD"]? then
    left := left ++ (← run gd (← `(tactic| exact Dom.sub_of_ranges (by decide))))
  if let some gP := byKind["hP"]? then
    let r ← run gP (← `(tactic| (refine Perm.le_of ?_ ?_ <;>
      simp (disch := nocompiler_disch) only [Spec.perm, Spec.stackRegion, $csp:ident, $sp:ident, Segment.region,
        List.size_toArray, List.length_cons, List.length_nil, List.cons_append, List.nil_append,
        List.append_nil, List.mem_cons, List.mem_append, List.mem_nil_iff, or_false, false_or,
        forall_eq_or_imp, forall_eq, exists_eq_or_imp, exists_eq_left, List.not_mem_nil, false_and,
        exists_false, imp_false, not_false_eq_true, true_and, and_true, false_implies, implies_true,
        forall_const, Region.within, nocompiler_state, nocompiler_nat, Nat.reducePow, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, $fs,*] <;>
      (try omega))))
    left := left ++ (← tagged r s!"{tag}_perm")
  let mut cont := []
  if let some gk := byKind["k"]? then
    let s1T ← gk.withContext do Term.exprToSyntax s1
    let r ← run gk (← `(tactic| intro $cS:ident $cdoneI:ident $cframeI:ident))
    let r ← r.foldlM (fun acc g => do return acc ++ (← run g (← `(tactic|
      rcases $cdoneI:ident with ⟨$cxI:ident, $cpcI:ident, $cpresI:ident, $cpostI:ident⟩ | ⟨$cexI:ident, $conI:ident⟩)))) []
    for g' in r do
      let isRet ← g'.withContext do return ((← getLCtx).findFromUserName? cpostI.getId).isSome
      if isRet then
        let r1 ← run g' (← `(tactic| ((try simp only [$csp:ident] at $cpostI:ident); (try exact ($cpostI).elim))))
        for g1 in r1 do
          -- What the callee leaves: the pc, the registers it preserves, its postcondition, memory.
          let steps : List (TSyntax `tactic) := [
            ← `(tactic| have $(mkIdent `nocompiler_hx):ident := $cxI),
            ← `(tactic| have $cpI:ident : ∀ r, r ∈ preservedRegs → ($cS).reg r = State.reg $s1T r := $cpresI),
            ← `(tactic| (try have $cmemI:ident : ($cS).mem = State.mem $s1T := funext fun x => $cframeI x (by
                simp [Perm.writable, Spec.perm, Spec.stackRegion, $csp:ident, Region.mem]))),
            ← `(tactic| (try have $(mkIdent `nocompiler_hS):ident : Same $(cx.s0) $cS:ident $rs :=
                Same.after_call (by nocompiler_same) $cpresI (nonPreserved_spec _ (by decide)))),
            ← `(tactic| nocompiler_anorm [$fs,*] at $cpcI:ident),
            ← `(tactic| (try nocompiler_anorm [$fs,*] at $cmemI:ident))]
          -- One equation per callee-saved register, normalised now with what is
          -- known at the call: a later normalisation then never has to go back
          -- through this call (or an earlier one) to find a register.
          let mut regSteps : Array (TSyntax `tactic) := #[]
          for r in preservedNats do
            let ci := mkIdent (Name.mkSimple s!"nocompiler_cp{r}_{tag}")
            regSteps := regSteps.push (← `(tactic|
              have $ci:ident : ($cS).reg $(natLit r) = State.reg $s1T $(natLit r) := $cpI _ (by decide)))
            regSteps := regSteps.push (← `(tactic| (try nocompiler_anorm [$fs,*] at $ci:ident)))
          let steps := steps ++ regSteps.toList
          let mut r2 := [g1]
          for t in steps do
            r2 ← r2.foldlM (fun acc g => return acc ++ (← run g t)) []
          for g2 in r2 do
            let (g3, postFacts) ← destructAnd g2 cpostI s!"hc_{cname}"
            -- The callee's postcondition, in the normal form of what is known here.
            let mut g3 := g3
            for pf in postFacts do
              if let [g'] ← run g3 (← `(tactic| (try nocompiler_anorm [$fs,*] at $(⟨pf.raw⟩):ident))) then
                g3 := g'
              else break
            let (newFacts) ← g3.withContext do
              let mut out : Array Term := #[← `($cpcI), ← `(nocompiler_hx)]
              for r in preservedNats do
                out := out.push (← `($(mkIdent (Name.mkSimple s!"nocompiler_cp{r}_{tag}")):ident))
              if ((← getLCtx).findFromUserName? cmemI.getId).isSome then out := out.push (← `($cmemI))
              return out ++ postFacts
            cont := cont ++ [(g3, { cx with facts := cx.facts ++ newFacts })]
      else
        -- The callee ended the process: this function's `onExit`.
        let r1 ← run g' (← `(tactic| (subst $(cx.hR):ident; refine $(mkIdent cx.fl.done) ?_; (try dsimp only); left)))
        let r1 ← r1.foldlM (fun acc g => do
          return acc ++ (← run g (← `(tactic| refine ⟨.inr $cexI, .inr ⟨$cexI, ?_⟩⟩)))) []
        let r2 ← r1.foldlM (fun acc g => do
          return acc ++ (← run g (← `(tactic| ((try simp only [$csp:ident] at $conI:ident) <;> (try simp only [$sp:ident])))))) []
        let r2 ← r2.foldlM (fun acc g => do
          return acc ++ (← run g (← `(tactic| (try nocompiler_vnorm [$conI:ident, $fs,*]))))) []
        let r2 ← splitOrKeep cx r2
        left := left ++ (← tagged r2 s!"{tag}_exit")
  return (cont, left)

/-- Run from the goal's state to the next cut points or returns. -/
partial def drive (cx : Ctx) (first : Bool) (fuel : Nat) (g : MVarId) (last : Nat) :
    TacticM (List MVarId) := do
  traceLine s!"[drive] after {hex last}, fuel {fuel}"
  if fuel = 0 then
    throwError "nocompiler_auto: no cut point within 400 steps of {cx.origin}: is every loop given an invariant?"
  let some (h, a) ← goalHead cx.fl g
    | throwError "nocompiler_auto: expected a `Reach` goal, got{indentExpr (← g.getType)}"
  if h == cx.fl.opt then
    -- An `if` left by a branch or by an alignment check.
    let a ← whnfR (← instantiateMVars a)
    unless a.isAppOf ``ite do
      throwError "nocompiler_auto: cannot continue at {hex last}:{indentExpr (← g.getType)}"
    let cond := a.getArg! 1
    if cond.isAppOf ``aligned then
      let gs ← run g (← `(tactic| rw [$(mkIdent cx.fl.optAligned):ident (by nocompiler_align)]))
      match gs with
      | [g'] => return ← drive cx false (fuel - 1) g' last
      | _ =>
        let gs ← tagged gs s!"align_{hex last}"
        return gs
    else
      let fs ← simpArgs cx.facts
      let gs ← run g (← `(tactic| split))
      let mut out := []
      for g' in gs do
        -- Named after the branch: unique along a run, which visits no address twice.
        let hb := mkIdent (Name.mkSimple s!"hb_{(hex last).drop 2}")
        let r ← run g' (← `(tactic| (rename_i $hb:ident)))
        let showHb (g : MVarId) (what : String) : TacticM Unit := g.withContext do
          if let some d := (← getLCtx).findFromUserName? hb.getId then
            traceLine s!"[cond {what} at {hex last}] {← Meta.ppExpr (← instantiateMVars d.type)}"
        for g in r do showHb g "before"
        let r ← r.foldlM (fun acc g => do
          return acc ++ (← run g (← `(tactic| nocompiler_cond [$fs,*] at $hb:ident)))) []
        for g in r do showHb g "after"
        let r ← r.foldlM (fun acc g => do
          return acc ++ (← run g (← `(tactic| (try (exfalso; omega)))))) []
        let r ← r.foldlM (fun acc g => do
          return acc ++ (← run g (← `(tactic| (try simp only [$(mkIdent cx.fl.optSome):ident]))))) []
        for g'' in r do
          out := out ++ (← drive cx false (fuel - 1) g'' last)
      return out
  traceLine "[drive] head"
  if (a.find? (·.isAppOf ``State.halt)).isSome then
    return ← closeExit cx g last
  let some pc ← pcOf a
    | closeRet cx g last
  traceLine s!"[drive] at {hex pc}"
  if !first && cx.cuts.contains pc then
    return ← closeCut cx g pc
  if let some (_, thm, csp) := cx.callees.find? (·.1 == pc) then
    let (cont, left) ← closeCall cx g pc thm csp a
    let mut out := left
    for (g', cx') in cont do
      out := out ++ (← g'.withContext do drive cx' false (fuel - 1) g' pc)
    return out
  if cx.ecalls.contains pc then
    let (cont, left) ← stepSys cx g pc
    let mut out := left
    for g' in cont do
      out := out ++ (← g'.withContext do drive cx false (fuel - 1) g' pc)
    return out
  let (g', left) ← step cx g pc
  return left ++ (← drive cx false (fuel - 1) g' pc)

/-! ### The front end -/

/-- A label of the structured form, `$next`: where the cut point is, without its address. -/
syntax nocompilerLabel := "$" noWs ident
syntax nocompilerCut := "loop_inv " (nocompilerLabel <|> term:max) ppSpace term:max " measure " term:max

/-- `nocompiler_auto f s he [facts] (loop_inv pc inv measure μ)*` proves the goal
    `Exec c (spec.perm a s) D (spec.Done a s) s` that `VerifiedImg c D entry spec`
    leaves after `intro a s he hpre`, for the function whose block/loop tree is
    `f`, given an invariant and a measure at each of its loop heads. What it
    cannot close is left as goals named after the path: `entry_to_0x…`,
    `0x…_to_0x…`, `…_ret_0x…`, `…_measure`. -/
syntax (name := nocompilerAuto) "nocompiler_auto " term:max ident ident (" [" Lean.Parser.Tactic.simpArg,* "]")?
  (" calls " "[" term,* "]")? (ppLine nocompilerCut)* : tactic

unsafe def evalLabelsImpl (e : Expr) : MetaM (List (String × Nat)) :=
  evalExpr (List (String × Nat)) (mkApp (mkConst ``List [Level.zero])
    (mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``String) (mkConst ``Nat))) e
@[implemented_by evalLabelsImpl] opaque evalLabels (e : Expr) : MetaM (List (String × Nat))

/-- The labels `nocompiler export` writes for the function `f` (`<f>_func`
    has `<f>_labels`), as names and addresses; none if there are none. -/
def labelsOf (f : Syntax) : TacticM (List (String × Nat)) := do
  let some n := (if f.isIdent then some f.getId else none) | return []
  let .str p s := n | return []
  unless s.endsWith "_func" do return []
  let ln := mkIdent (.str p ((String.ofList (s.toList.take (s.length - 5))) ++ "_labels"))
  try
    let e ← Term.elabTerm (← `(List.map (fun p : String × Word => (p.1, p.2.toNat)) $ln)) none
    evalLabels (← instantiateMVars e)
  catch _ => return []

unsafe def evalNatListImpl (e : Expr) : MetaM (List Nat) :=
  evalExpr (List Nat) (mkApp (mkConst ``List [Level.zero]) (mkConst ``Nat)) e
@[implemented_by evalNatListImpl] opaque evalNatList (e : Expr) : MetaM (List Nat)
unsafe def evalNatImpl (e : Expr) : MetaM Nat := evalExpr Nat (mkConst ``Nat) e
@[implemented_by evalNatImpl] opaque evalNat (e : Expr) : MetaM Nat

/-- `simp only [t]` accepts `t` (it elaborates and is a rewrite rule). -/
def simpAccepts (t : Term) : TermElabM Bool := do
  let st ← saveState
  let n0 := (← getThe Core.State).messages.toList.length
  try
    let g ← mkFreshExprMVar (mkConst ``True)
    let l ← `(Lean.Parser.Tactic.simpLemma| $t:term)
    let args : Syntax.TSepArray [``Lean.Parser.Tactic.simpStar, ``Lean.Parser.Tactic.simpErase,
      ``Lean.Parser.Tactic.simpLemma] "," := Syntax.TSepArray.ofElems #[⟨l.raw⟩]
    let tac ← `(tactic| simp only [$args,*])
    let _ ← Term.withoutErrToSorry <| Tactic.run g.mvarId! (Tactic.evalTactic tac)
    let bad := (← getThe Core.State).messages.toList.length != n0
    st.restore
    return !bad
  catch _ =>
    st.restore
    return false

/-- Facts every normalisation uses, from the hypotheses of the context. -/
def contextFacts (us : List Expr) : TermElabM (Array Term) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let x := mkFVar d.fvarId
    if let some (_, l, _) := ty.eq? then
      if us.any (fun u => l.containsFVar u.fvarId!) then
        out := out.push (← Term.exprToSyntax x)
        if l.isAppOfArity ``readBytes 3 then
          out := out.push (← `(mem_of_readBytes $(← Term.exprToSyntax x)))
          out := out.push (← `(mem_of_readBytes_base $(← Term.exprToSyntax x)))
    if ty.isAppOfArity ``Region.Disjoint 2 then
      let t ← Term.exprToSyntax x
      out := out.push (← `(readBytes_writeLE_of_disjoint $t))
      out := out.push (← `(readBytes_writeLE_of_disjoint (Region.Disjoint.symm $t)))
      out := out.push (← `(writeLE_apply_of_disjoint $t))
      out := out.push (← `(writeLE_apply_base_of_disjoint $t))
      out := out.push (← `(loaded_writeLE_iff $t))
      out := out.push (← `(arr64_writeLE_iff $t))
    if ty.isAppOfArity ``arr64 3 then
      out := out.push (← `(arr64.read $(← Term.exprToSyntax x)))
    -- `∀ x, (arrRegion a xs).mem x → ¬ R.mem x`: the array survives stores into R.
    if ty.isForall then
      if let .forallE _ _ b _ := ty then
        if b.isForall && !b.bindingBody!.hasLooseBVar 0 && b.bindingDomain!.isAppOfArity ``Region.mem 2 &&
            (b.bindingDomain!.getArg! 0).isAppOfArity ``arrRegion 2 then
          out := out.push (← `(arr64_writeLE_of_outside $(← Term.exprToSyntax x)))
  -- Keep what `simp` accepts: one bad simp argument would void a whole pass.
  out.filterM fun t => simpAccepts t

/-- Alignment hypotheses as the arithmetic `omega` reads. -/
def alignFacts : TacticM Unit := withMainContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``aligned 2 then
      let t ← Term.exprToSyntax (mkFVar d.fvarId)
      evalTactic (← `(tactic| have := (show _ % _ = 0 from $t)))


/-- What both front ends share: the syntax of the call, the goal, and the
    cut points as given. -/
structure Call where
  s0 : Ident
  he : Ident
  userFacts : Array Term
  code : Expr
  specName : Name
  cuts : Array (Nat × Term × Term × Term)
  /-- The function's labels (name, address). -/
  labels : List (String × Nat) := []

def parseCall (fl : Flavor) (s0 he : Syntax) (factsStx : Syntax) (cutStx : Array Syntax)
    (labels : List (String × Nat) := []) : TacticM Call := do
  let userFacts : Array Term := if factsStx.isNone then #[] else
    factsStx[1].getSepArgs.map fun a => ⟨a[2]!⟩
  let g ← getMainGoal
  let gt := (← instantiateMVars (← g.getType)).consumeMData
  unless gt.isAppOfArity fl.exec 5 do
    throwError "nocompiler_auto: expected `{fl.exec} c P D Q s` (after `intro a s he hpre` on a `VerifiedImg` goal)"
  let code := gt.getArg! 0
  let doneE := (gt.getArg! 3).consumeMData
  let specName ← match doneE.getAppFn with
    | .const ``Spec.Done _ => match (doneE.getArg! 1).getAppFn with
      | .const n _ => pure n
      | _ => throwError "nocompiler_auto: the specification must be a named constant"
    | _ => throwError "nocompiler_auto: expected `spec.Done` as the postcondition"
  let mut cuts : Array (Nat × Term × Term × Term) := #[]
  for c in cutStx do
    -- `$l`: a label. In term position it also parses as an antiquotation, so
    -- the syntax may be a choice node; what is written starts with `$`.
    let written : String := String.ofList ((c[1].reprint.getD "").toList.dropWhile Char.isWhitespace)
    if c[1].getKind == ``nocompilerLabel || written.toList.head? == some '$' then
      let some idStx := c[1].find? (·.isIdent) | throwError "nocompiler_auto: a label is `$name`"
      let l := idStx.getId.toString
      let some (_, v) := labels.find? (·.1 == l)
        | throwError "nocompiler_auto: no label ${l} (the function's labels: {labels.map (·.1)})"
      cuts := cuts.push (v, ← `((BitVec.ofNat 64 $(natLit v) : Word)), ⟨c[2]⟩, ⟨c[4]⟩)
      continue
    let pcT : Term := ⟨c[1]⟩
    let pcE ← Term.elabTerm pcT (some (mkConst ``Word))
    let some ⟨_, v⟩ ← getBitVecValue? (← instantiateMVars pcE)
      | throwError "nocompiler_auto: cut point {pcT} is not a literal"
    cuts := cuts.push (v.toNat, pcT, ⟨c[2]⟩, ⟨c[4]⟩)
  return { s0 := ⟨s0⟩, he := ⟨he⟩, userFacts, code, specName, cuts, labels }

/-- The run, from the cut points on. -/
def autoCore (fl : Flavor) (call : Call) (heads rsList : List Nat) (entryN : Nat)
    (callees : Array (Nat × Term × Name) := #[]) (ecallList : List Nat := []) (frameList : List Nat := []) :
    TacticM Unit := do
  let s0 := call.s0
  let he := call.he
  let userFacts := call.userFacts
  let specName := call.specName
  let cuts := call.cuts
  let gTop ← getMainGoal
  let logRef ← IO.mkRef (#[] : Array (MVarId × String))
  let logOpt := if nocompiler.auto.debugKernel.get (← getOptions) then some logRef else none
  let endsRef ← IO.mkRef ({} : Std.HashMap String Nat)
  traceLine "[nocompiler_auto] let rs ← `([$(rsList.toArray.map natLit)"
  let rs ← `([$(rsList.toArray.map natLit),*])
  let pcIdent := mkIdent `pc
  let uIdent := mkIdent `u
  let mut invChain ← `(False)
  let mut muChain ← `((0 : Nat))
  for (pcN, _, iT, mT) in cuts.reverse do
    let pcL := natLit pcN
    invChain ← `(if $pcIdent = BitVec.ofNat 64 $pcL then $iT $uIdent else $invChain)
    muChain ← `(if $pcIdent = BitVec.ofNat 64 $pcL then $mT $uIdent else $muChain)
  -- The frame: sp, and every register the prologue saved, still in its slot.
  let mut frameT ← `(True)
  if let n :: slots := frameList then
    let W := 18446744073709551616
    let pairs := (List.range (slots.length / 2)).map fun i => (slots[2 * i]!, slots[2 * i + 1]!)
    for (k, r) in pairs.reverse do
      frameT ← `(read64 (State.mem $uIdent) (State.reg $s0 2 + BitVec.ofNat 64 $(natLit (W - n + k))) =
        State.reg $s0 $(natLit r) ∧ $frameT)
    frameT ← `(State.reg $uIdent 2 = State.reg $s0 2 + BitVec.ofNat 64 $(natLit (W - n)) ∧ $frameT)
  let invT ← `(fun ($pcIdent : Word) ($uIdent : State) =>
    State.exit $uIdent = none ∧ Same $s0 $uIdent $rs ∧ $frameT ∧ $invChain)
  let muT ← `(fun ($pcIdent : Word) ($uIdent : State) => $muChain)
  traceLine "[nocompiler_auto] alignFacts"
  evalTactic (← `(tactic| have := (show (State.reg $s0 2).toNat % 16 = 0 from ($he).sp)))
  alignFacts
  let hR := mkIdent `nocompiler_hR
  let R := mkIdent `nocompiler_R
  let hpc := mkIdent `nocompiler_hpc
  let hx := mkIdent `nocompiler_hx
  let hS := mkIdent `nocompiler_hS
  let hI := mkIdent `nocompiler_hI
  let hra := mkIdent `nocompiler_hra
  let entryLit := natLit entryN
  traceLine "[nocompiler_auto] evalTactic (← `(tactic| unfold Exec))"
  evalTactic (← `(tactic| unfold $(mkIdent fl.exec):ident))
  let [gStart, gBody] ← run (← getMainGoal) (← `(tactic|
      refine $(mkIdent fl.cutpoints) (Q := fun s => Final _ s ∧ _) $invT $muT ?_ ?_))
    | throwError "nocompiler_auto: cutpoints"
  let retFacts : Array Term := #[← `($(mkIdent fl.retMask) ($he).retAligned), ← `(eq_true ($he).retAligned),
    ← `(eq_true ($(mkIdent fl.retTwo) ($he).retAligned))]
  -- From the entry.
  let [gStart] ← run gStart (← `(tactic| intro $R:ident $hR:ident)) | throwError "nocompiler_auto: start"
  let [gStart] ← run gStart (← `(tactic|
      have $hpc:ident : ($s0).pc = BitVec.ofNat 64 $entryLit := ($he).pc)) | throwError "nocompiler_auto: start"
  let [gStart] ← run gStart (← `(tactic| have $hx:ident : ($s0).exit = none := ($he).live))
    | throwError "nocompiler_auto: start"
  let [gStart] ← run gStart (← `(tactic| have $hS:ident : Same $s0 $s0 $rs := Same.refl _ _))
    | throwError "nocompiler_auto: start"
  let startGoals ← do
    gStart.withContext do
      let own : Array Term := #[hpc, hx]
      let s0E ← Term.elabTerm s0 none
      let fs ← contextFacts [s0E]
      let cx : Ctx := {
        fl := fl
        log := logOpt
        ends := some endsRef
        callees := callees
        ecalls := ecallList
        cuts := heads
        facts := userFacts ++ retFacts ++ fs ++ own
        rs := rs
        s0 := s0
        he := he
        spec := mkIdent specName
        hR := hR
        mode := .start
        origin := "entry"
        labels := call.labels
        entryN := entryN }
      drive cx false 400 gStart entryN
  -- From each loop head.
  let gBody0 := gBody
  let [gBody] ← run gBody (← `(tactic| intro $uIdent:ident $hI:ident $R:ident $hR:ident))
    | throwError "nocompiler_auto: body"
  let hF := mkIdent `nocompiler_hF
  let [gBody] ← run gBody (← `(tactic| obtain ⟨$hx:ident, $hS:ident, $hF:ident, $hI:ident⟩ := $hI:ident))
    | throwError "nocompiler_auto: body"
  let (gBody, frameFacts) ← destructAnd gBody hF "nocompiler_fr"
  let gBody ← if rsList.contains 1 then pure gBody else do
    let [g'] ← run gBody (← `(tactic|
        have $hra:ident : ($uIdent).reg 1 = ($s0).reg 1 := $hS:ident 1 (by decide)))
      | throwError "nocompiler_auto: body"
    pure g'
  let mut bodyGoals := []
  let mut pending := [gBody]
  let mut done := []
  -- Take the `if` chain apart: one goal per loop head.
  while !pending.isEmpty do
    let g :: rest := pending | break
    pending := rest
    let t ← g.withContext do
      let some d := (← getLCtx).findFromUserName? `nocompiler_hI | throwError "nocompiler_auto: hI"
      whnfR (← instantiateMVars d.type)
    if t.isAppOf ``ite then
      let gs ← run g (← `(tactic| split at $hI:ident))
      for g' in gs do
        let gs' ← run g' (← `(tactic| (try rename_i $hpc:ident)))
        pending := pending ++ gs'
    else if t.isConstOf ``False then
      let _ ← run g (← `(tactic| exact ($hI).elim))
    else
      done := done ++ [g]
  for g in done do
    let gs ← run g (← `(tactic| (try dsimp only at $hI:ident)))
    let some g := gs.head? | continue
    -- Take the invariant apart: ghosts by their names, facts as hypotheses.
    let mut g := g
    let mut k := 1
    repeat
      let t ← g.withContext do
        let some d := (← getLCtx).findFromUserName? `nocompiler_hI | throwError "nocompiler_auto: hI"
        whnfR (← instantiateMVars d.type)
      match t with
      | .app (.app (.const ``Exists _) _) (.lam n ..) =>
        let [g'] ← run g (← `(tactic| obtain ⟨$(mkIdent n):ident, $hI:ident⟩ := $hI:ident))
          | throwError "nocompiler_auto: invariant"
        g := g'
      | .app (.app (.const ``And _) _) _ =>
        -- The invariant's facts, by position: h1, h2, ...
        let [g'] ← run g (← `(tactic| obtain ⟨$(mkIdent (Name.mkSimple s!"h{k}")):ident, $hI:ident⟩ := $hI:ident))
          | throwError "nocompiler_auto: invariant"
        k := k + 1
        g := g'
      | _ => break
    let [g'] ← run g (← `(tactic| have $(mkIdent (Name.mkSimple s!"h{k}")):ident := $hI:ident))
      | throwError "nocompiler_auto: invariant"
    g := g'
    let (pc, cx) ← g.withContext do
      let some ud := (← getLCtx).findFromUserName? `u | throwError "nocompiler_auto: u"
      let some pc ← pcOf (mkFVar ud.fvarId) | throwError "nocompiler_auto: pc of a loop head"
      let fs ← contextFacts [mkFVar ud.fvarId, ← Term.elabTerm s0 none]
      let own : Array Term := (if rsList.contains 1 then #[hpc, hx] else #[hpc, hx, hra]) ++ frameFacts
      let cx : Ctx := {
        fl := fl
        log := logOpt
        ends := some endsRef
        callees := callees
        ecalls := ecallList
        cuts := heads
        facts := userFacts ++ retFacts ++ fs ++ own
        rs := rs
        s0 := s0
        he := he
        spec := mkIdent specName
        hR := hR
        mode := .body
        origin := hex 0
        labels := call.labels
        entryN := entryN }
      return (pc, cx)
    let gs ← g.withContext do drive { cx with origin := cx.name pc } true 400 g pc
    if !(nocompiler.auto.traceFile.get (← getOptions)).isEmpty then
      let e ← instantiateMVars (mkMVar g)
      traceLine s!"[size] body {hex pc}: {← e.numObjs} objects"
      if nocompiler.auto.debugKernel.get (← getOptions) then
        traceLine s!"[kernel] body {hex pc}: {← kernelCheckStep g} ms"
    bodyGoals := bodyGoals ++ gs
  traceLine s!"[auto] done, {startGoals.length + bodyGoals.length} goals left"
  if nocompiler.auto.debugKernel.get (← getOptions) then
    -- Debugging only. What is left is closed with `sorry` (so the audit rejects
    -- the declaration as depending on `sorryAx`), and an error is logged, so a
    -- file with the option on does not build at all.
    logError "nocompiler_auto: nocompiler.auto.debugKernel is on: the goals left are closed with sorry; \
      this is not a proof (turn the option off)"
    for g in startGoals ++ bodyGoals do
      unless ← g.isAssigned do g.withContext do g.assign (← mkSorry (← g.getType) false)
    let log ← logRef.get
    for i in [0:log.size] do
      let (g, t) := log[log.size - 1 - i]!
      traceLine s!"[kstep] checking step {log.size - 1 - i}: {t}"
      traceLine s!"[kstep] {← kernelCheckStep g} ms"
    traceLine s!"[kernel] whole body goal: {← kernelCheckStep gBody0} ms"
    traceLine s!"[kernel] whole goal: {← kernelCheckStep gTop} ms"
  replaceMainGoal (startGoals ++ bodyGoals)

/-- The callees of `calls [thm, ...]`: entry, theorem, specification. -/
def parseCallees (fl : Flavor) (stx : Syntax) : TacticM (Array (Nat × Term × Name)) := do
  let calleeTerms : Array Term := if stx.isNone then #[] else stx[2].getSepArgs.map (⟨·⟩)
  let mut callees : Array (Nat × Term × Name) := #[]
  for t in calleeTerms do
    let ty ← instantiateMVars (← inferType (← Term.elabTerm t none))
    unless ty.isAppOfArity fl.verified 5 do throwError "nocompiler_auto: {t} is not a `{fl.verified}` theorem"
    let entry := ty.getArg! 3
    let some spN := (ty.getArg! 4).getAppFn.constName? | throwError "nocompiler_auto: the spec of {t} must be a constant"
    callees := callees.push (← evalNat (← mkAppM ``BitVec.toNat #[entry]), t, spN)
  return callees

@[tactic nocompilerAuto] def evalNoCompilerAuto : Tactic := fun stx => do
  traceLine "[nocompiler_auto] start"
  let f : Term := ⟨stx[1]⟩
  let call ← parseCall {} stx[2] stx[3] stx[4] stx[6].getArgs (← labelsOf stx[1])
  let callees ← parseCallees {} stx[5]
  -- The function's tree: its loop heads are the cut points.
  let fE ← Term.elabTerm f (some (mkConst ``Struct.Func))
  let heads ← evalNatList (mkApp (mkConst ``loopHeads) fE)
  let rsList ← evalNatList (mkApp2 (mkConst ``writes) call.code fE)
  -- A function that calls may lose every caller-saved register to its callee.
  let rsList := if callees.isEmpty then rsList else
    (rsList ++ nonPreserved.filter (fun r => r != 1 || rsList.contains 1)).eraseDups
  let ecallList ← evalNatList (mkApp2 (mkConst ``ecalls) call.code fE)
  let frameList ← evalNatList (mkApp2 (mkConst ``frameOf) call.code fE)
  let entryN ← evalNat (← mkAppM ``BitVec.toNat #[mkApp (mkConst ``Struct.Func.entry) fE])
  let given := call.cuts.toList.map (·.1)
  for h in heads do
    unless given.contains h do throwError "nocompiler_auto: no invariant for the loop at {hex h}"
  for h in given do
    unless heads.contains h do throwError "nocompiler_auto: {hex h} is not a loop head of {f}"
  autoCore {} call heads rsList entryN callees ecallList frameList


end NoCompiler.Auto

namespace NoCompiler.Auto
/-- Word literals in the normal form (bytes keep their literals, as written). -/
@[nocompiler_nat] theorem ofNat_word (n : Nat) :
    (OfNat.ofNat n : Word) = BitVec.ofNat 64 n := rfl
end NoCompiler.Auto
