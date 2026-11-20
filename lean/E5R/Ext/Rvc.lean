import E5R.Auto

/-
EXTENSION, NOT PART OF THE e5r PROFILE: compressed (RVC) code.

The profile has fixed 32-bit instructions (docs/isa/profile.md). Ordinary
RV64GC code, which clang emits for `-march=rv64gc`, mixes 16-bit and 32-bit
instructions on 2-byte boundaries. This file extends the semantics as far as
proving such code in the same logic needs, and no further:

* `decodeC` expands a 16-bit RV64C instruction into the existing `Instr`
  (the expansion the RISC-V specification defines; the floating-point ones,
  C.EBREAK and the reserved encodings decode to nothing);
* `CCode` is a code image of halfwords: an instruction is fetched at a 2-byte
  aligned pc, and is 32-bit when its low two bits are 11, 16-bit otherwise;
* `execC n` is `exec` with the next pc and the link address at `pc + n`, and
  jump targets 2-byte aligned (instruction-address-misaligned with C enabled);
* `StepC`, `ReachC`, `ExecC` and `VerifiedC` are `Step`, `Reach`, `Exec` and
  `Verified` over `CCode`, with the same `Spec`, `Entry`, `Perm` and `Done`.
  The rules a proof uses (`trans`, `loop`, `cutpoints`, `exec_step`) are
  proved again here, the same way.

What this adds to the trusted base, for results about compressed code only:
`decodeC`, `CCode.instr` and `execC` (and the four definitions above). The
results about e5r binaries do not import this file. Checked against llvm-mc
(every 16-bit word, demo/test/rvc_decode.py) and against qemu-riscv64 (the
compressed `cobs_decode` run in Lean and in qemu on the same inputs,
demo/test/rvc_exec.py). Not done here: the adequacy theorems of
E5R/Adequacy.lean for `StepC`.
-/
namespace E5R

/-! ## Decoding -/

/-- Bits `lo .. lo+len-1` of a halfword. -/
@[inline] def cbits (h : BitVec 16) (lo len : Nat) : Nat := (h.toNat >>> lo) % 2 ^ len

/-- A register x8..x15, from a 3-bit field. -/
@[inline] def cregAt (h : BitVec 16) (lo : Nat) : Reg := ⟨8 + cbits h lo 3, by unfold cbits; omega⟩
@[inline] def cregFull (h : BitVec 16) (lo : Nat) : Reg := ⟨cbits h lo 5, Nat.mod_lt _ (by decide)⟩

/-- A sign-extended immediate of `n` bits as a 12-bit field. -/
def sx12 (v n : Nat) : BitVec 12 := (BitVec.ofNat n v).signExtend 12

/-- The 16-bit instructions of RV64C, as the 32-bit instructions they expand to. -/
def decodeC (h : BitVec 16) : Option Instr :=
  let op := cbits h 0 2
  let f3 := cbits h 13 3
  let rd := cregFull h 7
  let rs2 := cregFull h 2
  let rdp := cregAt h 7     -- rd'/rs1' in bits 9:7
  let rs2p := cregAt h 2    -- rd'/rs2' in bits 4:2
  -- the 6-bit immediate imm[5] = h[12], imm[4:0] = h[6:2]
  let imm6 := cbits h 12 1 * 32 + cbits h 2 5
  match op, f3 with
  -- Quadrant 0
  | 0, 0 =>
    let nz := cbits h 6 1 * 4 + cbits h 5 1 * 8 + cbits h 11 2 * 16 + cbits h 7 4 * 64
    if nz = 0 then none else some (.iop .addi rs2p 2 (BitVec.ofNat 12 nz))
  | 0, 2 => some (.load .lw rs2p rdp (BitVec.ofNat 12 (cbits h 6 1 * 4 + cbits h 10 3 * 8 + cbits h 5 1 * 64)))
  | 0, 3 => some (.load .ld rs2p rdp (BitVec.ofNat 12 (cbits h 10 3 * 8 + cbits h 5 2 * 64)))
  | 0, 6 => some (.store .sw rdp rs2p (BitVec.ofNat 12 (cbits h 6 1 * 4 + cbits h 10 3 * 8 + cbits h 5 1 * 64)))
  | 0, 7 => some (.store .sd rdp rs2p (BitVec.ofNat 12 (cbits h 10 3 * 8 + cbits h 5 2 * 64)))
  -- Quadrant 1
  | 1, 0 => some (.iop .addi rd rd (sx12 imm6 6))
  | 1, 1 => if rd.val = 0 then none else some (.addiw rd rd (sx12 imm6 6))
  | 1, 2 => some (.iop .addi rd 0 (sx12 imm6 6))
  | 1, 3 =>
    if rd.val = 2 then
      let nz := cbits h 6 1 * 16 + cbits h 2 1 * 32 + cbits h 5 1 * 64 + cbits h 3 2 * 128 +
        cbits h 12 1 * 512
      if nz = 0 then none else some (.iop .addi 2 2 (sx12 nz 10))
    else
      if imm6 = 0 then none else some (.lui rd ((BitVec.ofNat 6 imm6).signExtend 20))
  | 1, 4 =>
    match cbits h 10 2 with
    | 0 => some (.shift .srli rdp rdp (BitVec.ofNat 6 imm6))
    | 1 => some (.shift .srai rdp rdp (BitVec.ofNat 6 imm6))
    | 2 => some (.iop .andi rdp rdp (sx12 imm6 6))
    | _ =>
      match cbits h 12 1, cbits h 5 2 with
      | 0, 0 => some (.rop .sub rdp rdp rs2p)
      | 0, 1 => some (.rop .xor rdp rdp rs2p)
      | 0, 2 => some (.rop .or rdp rdp rs2p)
      | 0, 3 => some (.rop .and rdp rdp rs2p)
      | 1, 0 => some (.rwop .subw rdp rdp rs2p)
      | 1, 1 => some (.rwop .addw rdp rdp rs2p)
      | _, _ => none
  | 1, 5 =>
    let off := cbits h 3 3 * 2 + cbits h 11 1 * 16 + cbits h 2 1 * 32 + cbits h 7 1 * 64 +
      cbits h 6 1 * 128 + cbits h 9 2 * 256 + cbits h 8 1 * 1024 + cbits h 12 1 * 2048
    some (.jal 0 ((BitVec.ofNat 12 off).signExtend 21))
  | 1, 6 | 1, 7 =>
    let off := cbits h 3 2 * 2 + cbits h 10 2 * 8 + cbits h 2 1 * 32 + cbits h 5 2 * 64 +
      cbits h 12 1 * 256
    some (.branch (if f3 = 6 then .beq else .bne) rdp 0 ((BitVec.ofNat 9 off).signExtend 13))
  -- Quadrant 2
  | 2, 0 => some (.shift .slli rd rd (BitVec.ofNat 6 imm6))
  | 2, 2 =>
    if rd.val = 0 then none
    else some (.load .lw rd 2 (BitVec.ofNat 12 (cbits h 4 3 * 4 + cbits h 12 1 * 32 + cbits h 2 2 * 64)))
  | 2, 3 =>
    if rd.val = 0 then none
    else some (.load .ld rd 2 (BitVec.ofNat 12 (cbits h 5 2 * 8 + cbits h 12 1 * 32 + cbits h 2 3 * 64)))
  | 2, 4 =>
    match cbits h 12 1, rd.val, rs2.val with
    | 0, 0, 0 => none
    | 0, _, 0 => some (.jalr 0 rd 0)
    | 0, _, _ => some (.rop .add rd 0 rs2)
    | _, 0, 0 => none
    | _, _, 0 => some (.jalr 1 rd 0)
    | _, _, _ => some (.rop .add rd rd rs2)
  | 2, 6 => some (.store .sw 2 rs2 (BitVec.ofNat 12 (cbits h 9 4 * 4 + cbits h 7 2 * 64)))
  | 2, 7 => some (.store .sd 2 rs2 (BitVec.ofNat 12 (cbits h 10 3 * 8 + cbits h 7 3 * 64)))
  | _, _ => none

/-! ## Code images of halfwords -/

structure CCode where
  base : Word
  halves : Array (BitVec 16)

namespace CCode
def half (c : CCode) (pc : Word) : Option (BitVec 16) :=
  let off := (pc - c.base).toNat
  if off % 2 = 0 then c.halves[off / 2]? else none

/-- The instruction at `pc` and its length in bytes. -/
def instr (c : CCode) (pc : Word) : Option (Instr × Nat) :=
  match c.half pc with
  | none => none
  | some lo =>
    if lo.toNat % 4 = 3 then
      match c.half (pc + 2) with
      | none => none
      | some hi => (decode (hi ++ lo)).map (·, 4)
    else (decodeC lo).map (·, 2)
end CCode

/-! ## Semantics -/

/-- Continue at `t`, which must be 2-byte aligned. -/
def jumpToC (s : State) (t : Word) : Option State :=
  if aligned t 2 then some (s.setPc t) else none

/-- One step of an instruction `n` bytes long: control transfers as in
    `exec` with `pc + n` for the next instruction and 2-byte alignment;
    every other instruction is `exec`, followed by the pc `pc + n`. -/
def execC (n : Nat) (i : Instr) (s : State) : Option State :=
  let next := s.pc + BitVec.ofNat 64 n
  match i with
  | .jal rd off => jumpToC (s.setReg rd next) (s.pc + off.signExtend 64)
  | .jalr rd rs1 off =>
    let t := (s.reg rs1 + off.signExtend 64) &&& ~~~1
    jumpToC (s.setReg rd next) t
  | .branch op rs1 rs2 off =>
    if evalBr op (s.reg rs1) (s.reg rs2) then jumpToC s (s.pc + off.signExtend 64)
    else some (s.setPc next)
  | i => (exec i s).map (·.setPc next)

theorem Option.map_ite' {α β : Type} (f : α → β) (c : Prop) [Decidable c] (a b : Option α) :
    Option.map f (if c then a else b) = if c then Option.map f a else Option.map f b := by
  split <;> rfl

attribute [e5r_state] Option.map_ite' Option.map_some Option.map_none
attribute [irreducible] execC
attribute [e5r_sem] execC jumpToC Option.map_some Option.map_none

inductive StepC (c : CCode) (P : Perm) : State → State → Prop
  | exec {s s' : State} {i : Instr} {n : Nat} :
      s.exit = none → c.instr s.pc = some (i, n) → InstrOk P i s → execC n i s = some s' →
      StepC c P s s'
  | sys {s s' : State} :
      s.exit = none → c.instr s.pc = some (.ecall, 4) → SysOk P s → Sys s s' → StepC c P s s'

inductive ReachC (c : CCode) (P : Perm) (D : Dom) (Q : State → Prop) : State → Prop
  | done {s : State} : Q s → ReachC c P D Q s
  | step {s : State} :
      D.mem s.pc → (∃ s', StepC c P s s') → (∀ s', StepC c P s s' → ReachC c P D Q s') →
      ReachC c P D Q s

def ExecC (c : CCode) (P : Perm) (D : Dom) (Q : State → Prop) (s : State) : Prop :=
  ReachC c P D (fun s => Final D s ∧ Q s) s

/-- `Verified` for compressed code: the same specification, entry
    conditions and conclusion. -/
def VerifiedC {α : Type} (c : CCode) (D : Dom) (entry : Word) (sp : Spec α) : Prop :=
  ∀ a s, Entry D entry s → sp.pre a s → ExecC c (sp.perm a s) D (sp.Done a s) s

/-! ## The rules, again -/

namespace ReachC
variable {c : CCode} {P : Perm} {D : Dom}

theorem trans {Q₁ Q₂ : State → Prop} {s} (h : ReachC c P D Q₁ s)
    (k : ∀ s', Q₁ s' → ReachC c P D Q₂ s') : ReachC c P D Q₂ s := by
  induction h with
  | done hq => exact k _ hq
  | step hd hex _ ih => exact .step hd hex ih

theorem loop {Q : State → Prop} (I : State → Prop) (μ : State → Nat)
    (body : ∀ s, I s → ReachC c P D (fun s' => Q s' ∨ (I s' ∧ μ s' < μ s)) s) :
    ∀ s, I s → ReachC c P D Q s := by
  intro s hs
  induction hm : μ s using Nat.strongRecOn generalizing s with
  | _ n ih =>
    refine trans (body s hs) ?_
    rintro s' (hq | ⟨hi, hlt⟩)
    · exact .done hq
    · exact ih _ (hm ▸ hlt) s' hi rfl

theorem cutpoints {Q : State → Prop} (inv : Word → State → Prop) (μ : Word → State → Nat)
    {s : State}
    (start : ∀ R : State → Prop, R = (fun s' => Q s' ∨ inv s'.pc s') → ReachC c P D R s)
    (body : ∀ u, inv u.pc u → ∀ R : State → Prop,
      R = (fun s' => Q s' ∨ (inv s'.pc s' ∧ μ s'.pc s' < μ u.pc u)) → ReachC c P D R u) :
    ReachC c P D Q s :=
  trans (start _ rfl) fun s' h => h.elim .done fun hi =>
    loop (fun u => inv u.pc u) (fun u => μ u.pc u) (fun u hu => body u hu _ rfl) s' hi

def opt (c : CCode) (P : Perm) (D : Dom) (Q : State → Prop) : Option State → Prop
  | none => False
  | some s => ReachC c P D Q s

@[simp, e5r_state] theorem opt_some {Q s} : opt c P D Q (some s) = ReachC c P D Q s := rfl
@[simp, e5r_state] theorem opt_none {Q} : opt c P D Q none = False := rfl
attribute [irreducible] opt

theorem opt_aligned {Q : State → Prop} {a : Word} {w : Nat} {s : State} (h : aligned a w) :
    opt c P D Q (if aligned a w then some s else none) = ReachC c P D Q s := by
  simp [h]

theorem exec_ecallC (n : Nat) (s : State) : execC n .ecall s = none := by
  unfold execC; simp [exec_ecall]

theorem exec_step {Q : State → Prop} {s : State} {i : Instr} {n : Nat}
    (hd : D.mem s.pc) (hx : s.exit = none) (hi : c.instr s.pc = some (i, n)) (hok : InstrOk P i s)
    (h : opt c P D Q (execC n i s)) : ReachC c P D Q s := by
  cases hxs : execC n i s with
  | none => rw [hxs, opt_none] at h; exact h.elim
  | some s₁ =>
    rw [hxs, opt_some] at h
    refine .step hd ⟨s₁, .exec hx hi hok hxs⟩ (fun s' h' => ?_)
    cases h' with
    | exec _ hi' _ hx' => rw [hi] at hi'; cases hi'; rw [hxs] at hx'; cases hx'; exact h
    | sys _ hi' _ _ =>
      rw [hi] at hi'; cases hi'; exact absurd hxs (by simp [exec_ecallC])

end ReachC

/-! ## The registers a function writes, and its instruction addresses -/

namespace Auto
/-- The registers the instructions in `[entry, entry + bytes)` write, walking
    instruction by instruction. -/
def writesC (c : CCode) (entry : Word) (bytes : Nat) : List Nat :=
  let rec go : Nat → Nat → List Nat
    | 0, _ => []
    | fuel + 1, off =>
      if off ≥ bytes then [] else
      match c.instr (entry + BitVec.ofNat 64 off) with
      | some (i, n) => (rd? i).toList ++ go fuel (off + n)
      | none => go fuel (off + 2)
  ((go bytes 0).eraseDups).filter (· ≠ 0)
end Auto

end E5R

/-! ## `e5r_auto_c`: the symbolic run on compressed code

The same driver as `e5r_auto` (E5R/Auto.lean) over `ReachC`. There is no
block/loop tree here, so the cut points are the caller's: an invariant at a
set of addresses that every cycle of the function's control flow passes
through. Nothing checks that the set is enough before the run; if it is not,
a run goes around a loop until its step bound and fails. -/
namespace E5R.Auto
open Lean Elab Tactic Meta

def cFlavor : Flavor :=
  { reach := ``ReachC, opt := ``ReachC.opt, instr := ``CCode.instr, exec := ``ExecC,
    execStep := ``ReachC.exec_step, done := ``ReachC.done, optSome := ``ReachC.opt_some,
    optAligned := ``ReachC.opt_aligned, cutpoints := ``ReachC.cutpoints }

/-- `e5r_auto_c entry size s he [facts] (loop_inv pc inv measure μ)*`: as
    `e5r_auto`, for the function of `size` bytes at `entry` of a `CCode`. -/
syntax (name := e5rAutoC) "e5r_auto_c " term:max term:max ident ident
  (" [" Lean.Parser.Tactic.simpArg,* "]")? (ppLine e5rCut)* : tactic

@[tactic e5rAutoC] def evalE5rAutoC : Tactic := fun stx => do
  let call ← parseCall cFlavor stx[3] stx[4] stx[5] stx[6].getArgs
  let entryE ← Term.elabTerm stx[1] (some (mkConst ``Word))
  let sizeE ← Term.elabTerm stx[2] (some (mkConst ``Nat))
  let entryN ← evalNat (← mkAppM ``BitVec.toNat #[entryE])
  let rsList ← evalNatList (mkApp3 (mkConst ``writesC) call.code entryE sizeE)
  autoCore cFlavor call (call.cuts.toList.map (·.1)) rsList entryN

end E5R.Auto
