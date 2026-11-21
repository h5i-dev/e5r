import NoCompiler.Step
import NoCompiler.Lemmas

/-
Reflective verification conditions, milestone 1 (docs/isa/vcgen.md,
docs/design/prior-art-others.md "Implementation plan", step 2): straight-line
ALU code. Started by A (next-a, d61cbf7); continued by C.

Symbolic values are data (`Sym`) whose denotation is the machine's own
evaluation function, the symbolic register file is flat (32 slots), and a
symbolic run over the code is a function the kernel evaluates on closed data.
`run_sound` is proved once: whatever the run computes holds of every machine
state the symbolic state describes, after the same number of machine steps.
-/
namespace NoCompiler.VC

/-- A symbolic 64-bit value. -/
inductive Sym
  | var (n : Nat)
  | const (w : Word)
  | iop (op : IOp) (a : Sym) (imm : Word)
  | rop (op : ROp) (a b : Sym)
  deriving Inhabited, Repr

/-- What a symbolic value denotes, given the values `ρ` of its variables. -/
def Sym.den (ρ : Nat → Word) : Sym → Word
  | .var n => ρ n
  | .const w => w
  | .iop op a imm => evalI op (a.den ρ) imm
  | .rop op a b => evalR op (a.den ρ) (b.den ρ)

/-- A symbolic state: 32 register slots (x0 ignored) and a concrete pc. -/
structure SState where
  regs : List Sym
  pc : Word

namespace SState
def reg (S : SState) (r : Reg) : Sym := if r.val = 0 then .const 0 else S.regs.getD r.val (.const 0)
def setReg (S : SState) (r : Reg) (v : Sym) : SState :=
  if r.val = 0 then S else { S with regs := S.regs.set r.val v }
/-- The entry state: register r holds variable r. -/
def init (pc : Word) : SState := ⟨(List.range 32).map .var, pc⟩

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
end SState

/-- One symbolic step; `none` for what milestone 1 does not cover. -/
def sstep (i : Instr) (S : SState) : Option SState :=
  match i with
  | .iop op rd rs1 imm => some { S.setReg rd (.iop op (S.reg rs1) (imm.signExtend 64)) with pc := S.pc + 4 }
  | .rop op rd rs1 rs2 => some { S.setReg rd (.rop op (S.reg rs1) (S.reg rs2)) with pc := S.pc + 4 }
  | _ => none

/-- Run `n` instructions from `S`. -/
def run (c : Code) : Nat → SState → Option SState
  | 0, S => some S
  | n + 1, S => match c.instr S.pc with
    | some i => (sstep i S).bind (run c n)
    | none => none

/-- `S` describes `s` under `ρ`. -/
def Matches (ρ : Nat → Word) (S : SState) (s : State) : Prop :=
  S.regs.length = 32 ∧ s.pc = S.pc ∧ ∀ r : Reg, s.reg r = (S.reg r).den ρ

/-- The trusted machine, `n` instructions on (no syscalls). -/
def runT (c : Code) : Nat → State → Option State
  | 0, s => some s
  | n + 1, s => match c.instr s.pc with
    | some i => (exec i s).bind (runT c n)
    | none => none

theorem reg0 (S : SState) : S.reg 0 = .const 0 := by simp [SState.reg]

/-- One step, sound. -/
theorem sstep_sound {ρ : Nat → Word} {S S' : SState} {s : State} {i : Instr}
    (hm : Matches ρ S s) (h : sstep i S = some S') : ∃ s', exec i s = some s' ∧ Matches ρ S' s' := by
  obtain ⟨hl, hpc, hr⟩ := hm
  have upd : ∀ (rd : Reg) (v : Sym) (w : Word), w = v.den ρ →
      Matches ρ { S.setReg rd v with pc := S.pc + 4 } ((s.setReg rd w).setPc (s.pc + 4)) := by
    intro rd v w hw
    refine ⟨SState.length_setReg hl rd v, by simp [hpc], fun q => ?_⟩
    simp only [State.setPc_reg, State.reg_setReg]
    show _ = ((S.setReg rd v).reg q).den ρ
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
    simp only [sstep, Option.some.injEq] at h; subst h
    exact ⟨(s.setReg rd (evalI op (s.reg rs1) (imm.signExtend 64))).setPc (s.pc + 4), by simp only [exec],
      upd _ _ _ (by simp [Sym.den, hr rs1])⟩
  | rop op rd rs1 rs2 =>
    simp only [sstep, Option.some.injEq] at h; subst h
    exact ⟨(s.setReg rd (evalR op (s.reg rs1) (s.reg rs2))).setPc (s.pc + 4), by simp only [exec],
      upd _ _ _ (by simp [Sym.den, hr rs1, hr rs2])⟩
  | _ => simp [sstep] at h

/-- The symbolic run, sound: proved once for every code and every length. -/
theorem run_sound {ρ : Nat → Word} {c : Code} :
    ∀ {n : Nat} {S S' : SState} {s : State}, Matches ρ S s → run c n S = some S' →
      ∃ s', runT c n s = some s' ∧ Matches ρ S' s'
  | 0, S, S', s, hm, h => by
    simp only [run, Option.some.injEq] at h; subst h; exact ⟨s, rfl, hm⟩
  | n + 1, S, S', s, hm, h => by
    simp only [run] at h
    split at h
    · rename_i i hi
      cases hst : sstep i S with
      | none => rw [hst] at h; simp at h
      | some S₁ =>
        rw [hst] at h; simp only [Option.bind_some] at h
        obtain ⟨s₁, he, hm₁⟩ := sstep_sound hm hst
        obtain ⟨s', hr, hm'⟩ := run_sound hm₁ h
        refine ⟨s', ?_, hm'⟩
        simp only [runT]
        rw [show s.pc = S.pc from hm.2.1, hi]
        simp [he, hr]
    · simp at h

/-! ## The run over the code's words, in order

Looking an instruction up in the image (`Code.instr`) costs the kernel a walk
along the word list, so a run that looks up every pc is quadratic in the
code (measured: 500 instructions, 11.6 s of lookups alone). `runW` instead
consumes the words in order, which is what a straight-line run does, and
`runW_sound` relates it to the image once, by a general lemma. -/

/-- Run the words `ws` in order. -/
def runW : List (BitVec 32) → SState → Option SState
  | [], S => some S
  | w :: ws, S => match decode w with
    | some i => (sstep i S).bind (runW ws)
    | none => none

/-- The image's word at `base + 4 k` is its `k`-th word. -/
theorem Code.fetch_index (c : Code) (k : Nat) (hk : 4 * k < 2 ^ 64) :
    c.fetch (c.base + BitVec.ofNat 64 (4 * k)) = c.words.toList[k]? := by
  unfold Code.fetch
  have : (c.base + BitVec.ofNat 64 (4 * k) - c.base).toNat = 4 * k := by
    rw [show c.base + BitVec.ofNat 64 (4 * k) - c.base = BitVec.ofNat 64 (4 * k) by bv_omega]
    simp [Nat.mod_eq_of_lt hk]
  simp only [this, Nat.mul_mod_right, ite_true, Array.getElem?_toList]
  congr 1; omega

/-- The words run by `runW` are the image's, from index `k`. -/
theorem runW_sound {ρ : Nat → Word} {c : Code} :
    ∀ {ws : List (BitVec 32)} {k : Nat} {S S' : SState} {s : State},
      c.words.toList.drop k = ws → 4 * (k + ws.length) < 2 ^ 64 →
      S.pc = c.base + BitVec.ofNat 64 (4 * k) → Matches ρ S s → runW ws S = some S' →
      ∃ s', runT c ws.length s = some s' ∧ Matches ρ S' s'
  | [], _, S, S', s, _, _, _, hm, h => by
    simp only [runW, Option.some.injEq] at h; subst h; exact ⟨s, rfl, hm⟩
  | w :: ws, k, S, S', s, hd, hb, hpc, hm, h => by
    simp only [runW] at h
    split at h
    · rename_i i hi
      cases hst : sstep i S with
      | none => rw [hst] at h; simp at h
      | some S₁ =>
        rw [hst] at h; simp only [Option.bind_some] at h
        have hw : c.words.toList[k]? = some w := by
          rw [← List.head?_drop, hd]; rfl
        have hfetch : c.instr s.pc = some i := by
          rw [hm.2.1, hpc]; unfold Code.instr
          rw [Code.fetch_index c k (by simp at hb; omega), hw]; exact hi
        obtain ⟨s₁, he, hm₁⟩ := sstep_sound hm hst
        have hpc₁ : S₁.pc = c.base + BitVec.ofNat 64 (4 * (k + 1)) := by
          cases i <;> simp only [sstep, Option.some.injEq] at hst <;> (try subst hst) <;>
            simp_all [BitVec.ofNat_add] <;> bv_omega
        have hd₁ : c.words.toList.drop (k + 1) = ws := by
          rw [← List.drop_drop, hd]; rfl
        obtain ⟨s', hr, hm'⟩ := runW_sound hd₁ (by simp at hb ⊢; omega) hpc₁ hm₁ h
        exact ⟨s', by simp only [runT, List.length_cons, hfetch, he, Option.bind_some, hr], hm'⟩
    · simp at h

end NoCompiler.VC
