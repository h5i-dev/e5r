import NoCompiler.VC.Straight
import NoCompiler.Fast.Mem

/-
Reflective verification conditions, milestone 2 (docs/design/prior-art-others.md,
"Implementation plan"): loads and stores.

Symbolic values now include loads from a symbolic memory, and the symbolic
memory is the base memory with symbolic writes on top (`SMem`), both
denoting with the machine's own `loadVal` and `writeLE`. A symbolic step
emits what an access needs as data (`Ob`: alignment and permission of the
address), so a run's output is the end state and a list of obligations, and
`Reach.of_runW` turns "every obligation holds and the end state satisfies Q"
into the trusted `Reach`, proved once. Simplifying the obligations (offsets
inside a known region, aligned bases) is the next milestone; here they are
left as they come.
-/
namespace NoCompiler.VC.M

mutual
/-- A symbolic 64-bit value. -/
inductive Sym
  | var (n : Nat)
  | const (w : Word)
  | iop (op : IOp) (a : Sym) (imm : Word)
  | rop (op : ROp) (a b : Sym)
  | load (op : LdOp) (m : SMem) (a : Sym)
  | addiw (a : Sym) (imm : Word)
  | sh (op : ShOp) (a : Sym) (n : Nat)
  | shw (op : ShWOp) (a : Sym) (n : Nat)
  | rwop (op : RWOp) (a b : Sym)
  | uop (op : UOp) (a : Sym)
/-- A symbolic memory: the base memory, then writes of `width` bytes. -/
inductive SMem
  | base
  | write (m : SMem) (a : Sym) (v : Sym) (width : Nat)
end

instance : Inhabited Sym := ⟨.const 0⟩

mutual
def Sym.den (ρ : Nat → Word) (μ : Word → Byte) : Sym → Word
  | .var n => ρ n
  | .const w => w
  | .iop op a imm => evalI op (a.den ρ μ) imm
  | .rop op a b => evalR op (a.den ρ μ) (b.den ρ μ)
  | .load op m a => loadVal op (m.den ρ μ) (a.den ρ μ)
  | .addiw a imm => sext32 (a.den ρ μ + imm)
  | .sh op a n => evalSh op (a.den ρ μ) n
  | .shw op a n => evalShW op (a.den ρ μ) n
  | .rwop op a b => evalRW op (a.den ρ μ) (b.den ρ μ)
  | .uop op a => evalU op (a.den ρ μ)
def SMem.den (ρ : Nat → Word) (μ : Word → Byte) : SMem → (Word → Byte)
  | .base => μ
  | .write m a v w => writeLE (m.den ρ μ) (a.den ρ μ) (v.den ρ μ).toNat w
end

/-- What an access needs. -/
inductive Ob
  | aligned (a : Sym) (width : Nat)
  | canRead (a : Sym) (width : Nat)
  | canWrite (a : Sym) (width : Nat)

def Ob.den (ρ : Nat → Word) (μ : Word → Byte) (P : Perm) : Ob → Prop
  | .aligned a w => NoCompiler.aligned (a.den ρ μ) w
  | .canRead a w => P.canRead (a.den ρ μ) w
  | .canWrite a w => P.canWrite (a.den ρ μ) w

/-- An address as variable `n` plus constant `k`, when it is one. -/
def Sym.lin : Sym → Option (Nat × Word)
  | .var n => some (n, 0)
  | .iop .addi a imm => (Sym.lin a).map fun p => (p.1, p.2 + imm)
  | _ => none

theorem Sym.lin_den {ρ : Nat → Word} {μ : Word → Byte} :
    ∀ {a : Sym} {n : Nat} {k : Word}, a.lin = some (n, k) → a.den ρ μ = ρ n + k
  | .var _, n, k, h => by
    simp only [Sym.lin, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    simp [Sym.den]
  | .iop op a imm, n, k, h => by
    cases op <;> simp only [Sym.lin, reduceCtorEq] at h
    cases ha : a.lin with
    | none => rw [ha] at h; simp at h
    | some p =>
      rw [ha] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [Sym.den, Sym.lin_den ha]; simp [evalI]; bv_omega
  | .const _, _, _, h | .rop .., _, _, h | .load .., _, _, h | .addiw .., _, _, h | .sh .., _, _, h
  | .shw .., _, _, h | .rwop .., _, _, h | .uop .., _, _, h => by simp [Sym.lin] at h

/-! ### Reading through symbolic writes

A load looks past the writes on top of the memory that are disjoint from it:
both addresses the same variable plus constants, the ranges decided on the
constants alone (`disj`), since `(x + k₁) - (x + k₂) = k₁ - k₂`. An 8-byte load
right after an 8-byte store at the same address is the stored value (`symLoad`). -/

def disj (a : Sym) (w : Nat) (b : Sym) (n : Nat) : Bool :=
  match a.lin, b.lin with
  | some (x, k₁), some (y, k₂) => x == y && decide (Fast.Disjoint k₁ w k₂ n)
  | _, _ => false

/-- The memory a `w`-byte load at `a` reads, with the disjoint writes on top removed. -/
def rdSkip (a : Sym) (w : Nat) : SMem → SMem
  | .base => .base
  | .write m b v n => if disj a w b n then rdSkip a w m else .write m b v n

/-- The symbolic value of a load. -/
def symLoad (op : LdOp) (m : SMem) (a : Sym) : Sym :=
  match op, m with
  | .ld, .write m' b v 8 => if a.lin.isSome && a.lin == b.lin then v else .load .ld (rdSkip a 8 (.write m' b v 8)) a
  | op, m => .load op (rdSkip a op.width m) a

theorem disj_sound {ρ : Nat → Word} {μ : Word → Byte} {a b : Sym} {w n : Nat} (h : disj a w b n = true) :
    Fast.Disjoint (a.den ρ μ) w (b.den ρ μ) n := by
  unfold disj at h
  split at h
  · rename_i x k₁ y k₂ ha hb
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨rfl, hd⟩ := h
    rw [Sym.lin_den ha, Sym.lin_den hb]
    have e₁ : ρ x + k₁ - (ρ x + k₂) = k₁ - k₂ := by bv_omega
    have e₂ : ρ x + k₂ - (ρ x + k₁) = k₂ - k₁ := by bv_omega
    unfold Fast.Disjoint at hd ⊢; rw [e₁, e₂]; exact hd
  · simp at h

theorem rdSkip_read {ρ : Nat → Word} {μ : Word → Byte} {a : Sym} {w : Nat} :
    ∀ m : SMem, readLE ((rdSkip a w m).den ρ μ) (a.den ρ μ) w = readLE (m.den ρ μ) (a.den ρ μ) w
  | .base => rfl
  | .write m b v n => by
    simp only [rdSkip]
    split
    · rename_i h
      rw [rdSkip_read m, SMem.den, Fast.readLE_writeLE_of_disjoint (disj_sound h)]
    · rfl

theorem loadVal_congr {op : LdOp} {m m' : Word → Byte} {a : Word}
    (h : readLE m a op.width = readLE m' a op.width) : loadVal op m a = loadVal op m' a := by
  cases op <;> simp only [loadVal, read8, read16, read32, read64, LdOp.width] at h ⊢ <;> rw [h]

theorem symLoad_den {ρ : Nat → Word} {μ : Word → Byte} (op : LdOp) (m : SMem) (a : Sym) :
    (symLoad op m a).den ρ μ = loadVal op (m.den ρ μ) (a.den ρ μ) := by
  unfold symLoad
  split
  · rename_i m' b v
    split
    · rename_i h
      simp only [Bool.and_eq_true, Option.isSome_iff_exists, beq_iff_eq] at h
      obtain ⟨⟨p, hp⟩, hab⟩ := h
      have hb : b.lin = some p := hab ▸ hp
      have e : a.den ρ μ = b.den ρ μ := by
        obtain ⟨x, k⟩ := p; rw [Sym.lin_den hp, Sym.lin_den hb]
      rw [SMem.den, e, loadVal, read64, Fast.readLE_writeLE_same (by decide)]
      apply BitVec.eq_of_toNat_eq
      have := (Sym.den ρ μ v).isLt
      simp only [BitVec.toNat_ofNat]
      omega
    · rw [Sym.den]; exact loadVal_congr (rdSkip_read _)
  · rw [Sym.den]; exact loadVal_congr (rdSkip_read _)

/-- The symbolic memory after an `n`-byte store of `v` at `a`: it replaces a
    write of the same range, moving past the disjoint writes above it, so a
    memory holds at most one write per range it can tell apart. -/
def symStore (a v : Sym) (n : Nat) : SMem → SMem
  | .base => .write .base a v n
  | .write m b w k =>
    if a.lin.isSome && a.lin == b.lin && n == k then .write m a v n
    else if disj a n b k then .write (symStore a v n m) b w k
    else .write (.write m b w k) a v n

theorem symStore_den {ρ : Nat → Word} {μ : Word → Byte} (a v : Sym) (n : Nat) :
    ∀ m : SMem, (symStore a v n m).den ρ μ = writeLE (m.den ρ μ) (a.den ρ μ) (v.den ρ μ).toNat n
  | .base => rfl
  | .write m b w k => by
    simp only [symStore]
    split
    · rename_i h
      simp only [Bool.and_eq_true, Option.isSome_iff_exists, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨x, c⟩, hp⟩, hab⟩, rfl⟩ := h
      have hb : b.lin = some (x, c) := hab ▸ hp
      have e : b.den ρ μ = a.den ρ μ := by rw [Sym.lin_den hp, Sym.lin_den hb]
      simp only [SMem.den, e, Fast.writeLE_overwrite]
    · split
      · rename_i _ h
        simp only [SMem.den, symStore_den a v n m]
        exact (Fast.writeLE_comm (disj_sound h)).symm
      · rfl

/-- A symbolic state: 32 register slots, the memory, a concrete pc. -/
structure SState where
  regs : List Sym
  mem : SMem
  pc : Word

namespace SState
def reg (S : SState) (r : Reg) : Sym := if r.val = 0 then .const 0 else S.regs.getD r.val (.const 0)
def setReg (S : SState) (r : Reg) (v : Sym) : SState :=
  if r.val = 0 then S else { S with regs := S.regs.set r.val v }
def init (pc : Word) : SState := ⟨(List.range 32).map .var, .base, pc⟩

theorem reg_setReg {S : SState} (hS : S.regs.length = 32) (r q : Reg) (v : Sym) :
    (S.setReg r v).reg q = if r.val = 0 then S.reg q else if q = r then v else S.reg q := by
  unfold SState.setReg SState.reg
  by_cases hr : r.val = 0
  · simp [hr]
  · simp only [hr, ite_false]
    by_cases hq : q = r
    · subst hq
      have : q.val < S.regs.length := by omega
      simp [hr, List.getD_eq_getElem?_getD, List.getElem?_set_self this]
    · have hv : r.val ≠ q.val := fun e => hq (Fin.ext e).symm
      simp [hq, List.getD_eq_getElem?_getD, List.getElem?_set_ne hv]

theorem length_setReg {S : SState} (hS : S.regs.length = 32) (r : Reg) (v : Sym) :
    (S.setReg r v).regs.length = 32 := by
  unfold SState.setReg; split
  · exact hS
  · simpa using hS

@[simp] theorem setReg_mem (S : SState) (r : Reg) (v : Sym) : (S.setReg r v).mem = S.mem := by
  unfold SState.setReg; split <;> rfl
end SState

/-- `S` describes `s` under `ρ` (registers) and `μ` (the base memory). -/
def Matches (ρ : Nat → Word) (μ : Word → Byte) (S : SState) (s : State) : Prop :=
  S.regs.length = 32 ∧ s.pc = S.pc ∧ (∀ r : Reg, s.reg r = (S.reg r).den ρ μ) ∧ s.mem = S.mem.den ρ μ

/-- The address of an access, as the machine computes it (`ea`). -/
def addr (S : SState) (rs1 : Reg) (off : BitVec 12) : Sym := .iop .addi (S.reg rs1) (off.signExtend 64)

/-- One symbolic step and what it needs; `none` for what milestone 2 does not cover. -/
def sstep (i : Instr) (S : SState) : Option (SState × List Ob) :=
  match i with
  | .iop op rd rs1 imm =>
    some ({ S.setReg rd (.iop op (S.reg rs1) (imm.signExtend 64)) with pc := S.pc + 4 }, [])
  | .rop op rd rs1 rs2 =>
    some ({ S.setReg rd (.rop op (S.reg rs1) (S.reg rs2)) with pc := S.pc + 4 }, [])
  | .lui rd imm =>
    some ({ S.setReg rd (.const ((imm.setWidth 32 <<< 12).signExtend 64)) with pc := S.pc + 4 }, [])
  | .auipc rd imm =>
    some ({ S.setReg rd (.const (S.pc + (imm.setWidth 32 <<< 12).signExtend 64)) with pc := S.pc + 4 }, [])
  | .addiw rd rs1 imm =>
    some ({ S.setReg rd (.addiw (S.reg rs1) (imm.signExtend 64)) with pc := S.pc + 4 }, [])
  | .shift op rd rs1 sh => some ({ S.setReg rd (.sh op (S.reg rs1) sh.toNat) with pc := S.pc + 4 }, [])
  | .shiftw op rd rs1 sh => some ({ S.setReg rd (.shw op (S.reg rs1) sh.toNat) with pc := S.pc + 4 }, [])
  | .rwop op rd rs1 rs2 =>
    some ({ S.setReg rd (.rwop op (S.reg rs1) (S.reg rs2)) with pc := S.pc + 4 }, [])
  | .uop op rd rs1 => some ({ S.setReg rd (.uop op (S.reg rs1)) with pc := S.pc + 4 }, [])
  | .load op rd rs1 off =>
    let a := addr S rs1 off
    some ({ S.setReg rd (symLoad op S.mem a) with pc := S.pc + 4 }, [.aligned a op.width, .canRead a op.width])
  | .store op rs1 rs2 off =>
    let a := addr S rs1 off
    some ({ S with mem := symStore a (S.reg rs2) op.width S.mem, pc := S.pc + 4 },
      [.aligned a op.width, .canWrite a op.width])
  | _ => none

theorem reg0 (S : SState) : S.reg 0 = .const 0 := by simp [SState.reg]

theorem addr_den {ρ : Nat → Word} {μ : Word → Byte} {S : SState} {s : State}
    (hr : ∀ r : Reg, s.reg r = (S.reg r).den ρ μ) (rs1 : Reg) (off : BitVec 12) :
    (addr S rs1 off).den ρ μ = ea s rs1 off := by
  simp [addr, Sym.den, evalI, ea, hr rs1]

/-- One step, sound: when its obligations hold, the machine steps (with the
    access permitted) to a state the next symbolic state describes. -/
theorem sstep_sound {ρ : Nat → Word} {μ : Word → Byte} {P : Perm} {S S' : SState} {s : State}
    {i : Instr} {obs : List Ob} (hm : Matches ρ μ S s) (h : sstep i S = some (S', obs))
    (hob : ∀ o ∈ obs, o.den ρ μ P) :
    ∃ s', exec i s = some s' ∧ InstrOk P i s ∧ Matches ρ μ S' s' := by
  obtain ⟨hl, hpc, hr, hmem⟩ := hm
  have upd : ∀ (rd : Reg) (v : Sym) (w : Word), w = v.den ρ μ →
      Matches ρ μ { S.setReg rd v with pc := S.pc + 4 } ((s.setReg rd w).setPc (s.pc + 4)) := by
    intro rd v w hw
    refine ⟨SState.length_setReg hl rd v, by simp [hpc], fun q => ?_, by simp [hmem]⟩
    simp only [State.setPc_reg, State.reg_setReg]
    show _ = ((S.setReg rd v).reg q).den ρ μ
    rw [SState.reg_setReg hl]
    by_cases hq0 : q = 0
    · subst hq0
      by_cases h0 : rd = 0
      · simp [h0, Sym.den, reg0]
      · have : (0 : Reg) ≠ rd := Ne.symm h0
        simp [h0, this, Sym.den, reg0]
    · by_cases hr0 : rd.val = 0
      · have : rd = 0 := Fin.ext hr0
        subst this
        simp [hq0, hr q]
      · by_cases hq : q = rd
        · subst hq; simp [hq0, hw]
        · simp [hq0, hr0, hq, hr q]
  cases i with
  | iop op rd rs1 imm =>
    simp only [sstep, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨(s.setReg rd (evalI op (s.reg rs1) (imm.signExtend 64))).setPc (s.pc + 4), by simp only [exec],
      trivial, upd _ _ _ (by simp [Sym.den, hr rs1])⟩
  | rop op rd rs1 rs2 =>
    simp only [sstep, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨(s.setReg rd (evalR op (s.reg rs1) (s.reg rs2))).setPc (s.pc + 4), by simp only [exec],
      trivial, upd _ _ _ (by simp [Sym.den, hr rs1, hr rs2])⟩
  | lui rd imm =>
    simp only [sstep, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨(s.setReg rd ((imm.setWidth 32 <<< 12).signExtend 64)).setPc (s.pc + 4), by simp only [exec], trivial, upd _ _ _ (by simp [Sym.den])⟩
  | auipc rd imm =>
    simp only [sstep, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨(s.setReg rd (s.pc + (imm.setWidth 32 <<< 12).signExtend 64)).setPc (s.pc + 4), by simp only [exec], trivial, upd _ _ _ (by simp [Sym.den, hpc])⟩
  | addiw rd rs1 imm =>
    simp only [sstep, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨(s.setReg rd (sext32 (s.reg rs1 + imm.signExtend 64))).setPc (s.pc + 4), by simp only [exec], trivial, upd _ _ _ (by simp [Sym.den, hr rs1])⟩
  | shift op rd rs1 sh =>
    simp only [sstep, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨(s.setReg rd (evalSh op (s.reg rs1) sh.toNat)).setPc (s.pc + 4), by simp only [exec], trivial, upd _ _ _ (by simp [Sym.den, hr rs1])⟩
  | shiftw op rd rs1 sh =>
    simp only [sstep, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨(s.setReg rd (evalShW op (s.reg rs1) sh.toNat)).setPc (s.pc + 4), by simp only [exec], trivial, upd _ _ _ (by simp [Sym.den, hr rs1])⟩
  | rwop op rd rs1 rs2 =>
    simp only [sstep, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨(s.setReg rd (evalRW op (s.reg rs1) (s.reg rs2))).setPc (s.pc + 4), by simp only [exec], trivial, upd _ _ _ (by simp [Sym.den, hr rs1, hr rs2])⟩
  | uop op rd rs1 =>
    simp only [sstep, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨(s.setReg rd (evalU op (s.reg rs1))).setPc (s.pc + 4), by simp only [exec], trivial, upd _ _ _ (by simp [Sym.den, hr rs1])⟩
  | load op rd rs1 off =>
    simp only [sstep, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have hal := hob (.aligned (addr S rs1 off) op.width) (by simp)
    have hcr := hob (.canRead (addr S rs1 off) op.width) (by simp)
    simp only [Ob.den, addr_den hr] at hal hcr
    refine ⟨(s.setReg rd (loadVal op s.mem (ea s rs1 off))).setPc (s.pc + 4), ?_, hcr,
      upd _ _ _ (by rw [symLoad_den, addr_den hr, hmem])⟩
    simp only [exec, hal, ite_true]
  | store op rs1 rs2 off =>
    simp only [sstep, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have hal := hob (.aligned (addr S rs1 off) op.width) (by simp)
    have hcw := hob (.canWrite (addr S rs1 off) op.width) (by simp)
    simp only [Ob.den, addr_den hr] at hal hcw
    refine ⟨(s.setMem (writeLE s.mem (ea s rs1 off) (s.reg rs2).toNat op.width)).setPc (s.pc + 4), ?_, hcw,
      ⟨hl, by simp [hpc], fun q => by simp [hr q, SState.reg], ?_⟩⟩
    · simp only [exec, hal, ite_true]
    · simp [symStore_den, addr_den hr, hmem, hr rs2]
  | _ => simp [sstep] at h

theorem exec_exit {i : Instr} {s s' : State} (h : exec i s = some s') : s'.exit = s.exit := by
  cases i <;> simp only [exec, jumpTo] at h <;> (try split at h) <;> (try split at h) <;>
    simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> simp

/-- An instruction leaves the trace alone (only a syscall adds to it). -/
theorem exec_trace {i : Instr} {s s' : State} (h : exec i s = some s') : s'.trace = s.trace := by
  cases i <;> simp only [exec, jumpTo] at h <;> (try split at h) <;> (try split at h) <;>
    simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> simp

/-- Run the words `ws` in order, inside `D`, collecting the obligations. -/
def runW (D : Dom) : List (BitVec 32) → SState → Option (SState × List Ob)
  | [], S => some (S, [])
  | w :: ws, S =>
    if D.mem S.pc then
      match decode w with
      | some i => match sstep i S with
        | some (S₁, o₁) => (runW D ws S₁).map fun (S', o) => (S', o₁ ++ o)
        | none => none
      | none => none
    else none

/-- The trusted `Reach` from a run: when the run's obligations hold, every
    execution of the image from a described state reaches `Q`, provided `Q`
    holds of every state the end state describes. -/
theorem Reach.of_runW {ρ : Nat → Word} {μ : Word → Byte} {c : Code} {P : Perm} {D : Dom}
    {Q : State → Prop} :
    ∀ {ws rest : List (BitVec 32)} {k : Nat} {S S' : SState} {obs : List Ob} {s : State},
      c.words.toList.drop k = ws ++ rest → 4 * (k + ws.length) < 2 ^ 64 →
      S.pc = c.base + BitVec.ofNat 64 (4 * k) → Matches ρ μ S s → s.exit = none →
      runW D ws S = some (S', obs) → (∀ o ∈ obs, o.den ρ μ P) →
      (∀ s', Matches ρ μ S' s' → s'.exit = none → Q s') → Reach c P D Q s
  | [], _, _, S, S', obs, s, _, _, _, hm, hx, h, _, hQ => by
    simp only [runW, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact .done (hQ s hm hx)
  | w :: ws, rest, k, S, S', obs, s, hd, hb, hpc, hm, hx, h, hob, hQ => by
    simp only [runW] at h
    split at h
    · rename_i hD
      split at h
      · rename_i i hi
        split at h
        · rename_i S₁ o₁ hst
          cases hr : runW D ws S₁ with
          | none => rw [hr] at h; simp at h
          | some p =>
            obtain ⟨S₂, o₂⟩ := p
            rw [hr] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hw : c.words.toList[k]? = some w := by rw [← List.head?_drop, hd]; rfl
            have hfetch : c.instr s.pc = some i := by
              rw [hm.2.1, hpc]; unfold Code.instr
              rw [Code.fetch_index c k (by simp at hb; omega), hw]; exact hi
            obtain ⟨s₁, he, hok, hm₁⟩ := sstep_sound (P := P) hm hst
              (fun o ho => hob o (List.mem_append_left _ ho))
            have hpc₁ : S₁.pc = c.base + BitVec.ofNat 64 (4 * (k + 1)) := by
              cases i <;> simp only [sstep, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hst <;>
                (try obtain ⟨rfl, rfl⟩ := hst) <;> simp_all [BitVec.ofNat_add] <;> bv_omega
            have hd₁ : c.words.toList.drop (k + 1) = ws ++ rest := by rw [← List.drop_drop, hd]; rfl
            have hx₁ : s₁.exit = none := (exec_exit he).trans hx
            have hD' : D.mem s.pc := by rw [hm.2.1]; exact hD
            have hrest : Reach c P D Q s₁ :=
              Reach.of_runW hd₁ (by simp at hb ⊢; omega) hpc₁ hm₁ hx₁ hr
                (fun o ho => hob o (List.mem_append_right _ ho)) hQ
            exact NoCompiler.Reach.exec_step hD' hx hfetch hok (by rw [he, NoCompiler.Reach.opt_some]; exact hrest)
        · simp at h
      · simp at h
    · simp at h

end NoCompiler.VC.M
