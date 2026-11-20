import NoCompiler.RefineLockstep
import NoCompiler.Attr

/-
Relational cut points (docs/isa/refine.md, "Relational cut points"): a
refinement whose relation at some paired program points is not "the live
registers are equal", for example strength reduction in a loop (B keeps a
pointer where A keeps an index).

The proof method is `BigSim` with a relation made of cut points: a cut pairs
a point of B with a point of A, with a live set (agreement) and an
invariant `inv s0 sa sb` (the relational part, over the entry state `s0`).
Between cut points both sides are run by `runUntil`, a function, so that a
path is evaluated by `simp` and its branches become `if`s:

* A's run from a cut, computed, is a run of A under the permission
  (`Exec.runUntil`), with A's permission at every step: A's safe run is the
  justification for B's accesses;
* B's run, computed, with B's permission at every step, is B's `Reach`
  (`Reach.of_runUntil`).

Syscalls are not covered yet: a path through an `ecall` does not compute.
-/
namespace NoCompiler

/-- One step of the code (no syscalls). -/
def stepC (c : Code) (s : State) : Option State :=
  match c.instr s.pc with
  | some i => exec i s
  | none => none

/-- Where a computed run stops: at `stop`, outside `D`, or after an exit. -/
def stops (D : Dom) (stop : Word → Bool) (s : State) : Bool :=
  stop s.pc || !decide (D.mem s.pc) || decide (s.exit ≠ none)

/-- Run from `s` (at least one step) until `stops`; `none` on a fault, an
    `ecall`, an instruction that does not decode, or when `fuel` runs out. -/
def runUntil (c : Code) (D : Dom) (stop : Word → Bool) : Nat → State → Option State
  | 0, _ => none
  | n + 1, s =>
    if D.mem s.pc ∧ s.exit = none then
      match stepC c s with
      | some s' => if stops D stop s' then some s' else runUntil c D stop n s'
      | none => none
    else none

/-- The permission every step of the computed run needs. -/
def okUntil (c : Code) (D : Dom) (stop : Word → Bool) (P : Perm) : Nat → State → Prop
  | 0, _ => True
  | n + 1, s =>
    (∀ i, c.instr s.pc = some i → InstrOk P i s) ∧
    ∀ s', stepC c s = some s' → stops D stop s' = false → okUntil c D stop P n s'

theorem stepC_some {c : Code} {s s' : State} (h : stepC c s = some s') :
    ∃ i, c.instr s.pc = some i ∧ exec i s = some s' := by
  unfold stepC at h
  split at h
  · rename_i i hi; exact ⟨i, hi, h⟩
  · simp at h

/-- A's side: a computed run from a safe state is a run of A, with A's
    permission at every step, and A's run from its end is still safe. -/
theorem Exec.runUntil {c : Code} {P : Perm} {D : Dom} {Q : State → Prop} {stop : Word → Bool} :
    ∀ {n : Nat} {s t : State}, Exec c P D Q s → runUntil c D stop n s = some t →
      RunPlus c P D s t ∧ okUntil c D stop P n s ∧ Exec c P D Q t
  | 0, _, _, _, h => by simp [NoCompiler.runUntil] at h
  | n + 1, s, t, hA, h => by
    by_cases hdx : D.mem s.pc ∧ s.exit = none
    · obtain ⟨hd, hx⟩ := hdx
      cases hs : stepC c s with
      | none => simp [NoCompiler.runUntil, hd, hx, hs] at h
      | some s' =>
        obtain ⟨i, hi, he⟩ := stepC_some hs
        obtain ⟨hok, hst, hA'⟩ := Exec.stepA hA hd hx hi he
        have hokI : ∀ i', c.instr s.pc = some i' → InstrOk P i' s := by
          intro i' hi'; rw [hi] at hi'; cases hi'; exact hok
        by_cases hstop : stops D stop s' = true
        · simp only [NoCompiler.runUntil, hd, hx, and_self, ite_true, hs, hstop, Option.some.injEq] at h
          subst h
          refine ⟨⟨_, hd, hst, .refl _⟩, ⟨hokI, fun s'' hs'' hn => ?_⟩, hA'⟩
          rw [hs] at hs''; cases hs''; rw [hstop] at hn; cases hn
        · simp only [Bool.not_eq_true] at hstop
          simp only [NoCompiler.runUntil, hd, hx, and_self, ite_true, hs, hstop, Bool.false_eq_true,
            ite_false] at h
          obtain ⟨⟨s₁, hd₁, hst₁, hrun⟩, hok', hA''⟩ := Exec.runUntil hA' h
          refine ⟨⟨_, hd, hst, .step hd₁ hst₁ hrun⟩, ⟨hokI, fun s'' hs'' _ => ?_⟩, hA''⟩
          rw [hs] at hs''; cases hs''; exact hok'
    · simp [NoCompiler.runUntil, hdx] at h

/-- B's side: a computed run with the permission at every step reaches its
    end, on every run (the run is deterministic: no syscalls). -/
theorem Reach.of_runUntil {c : Code} {P : Perm} {D : Dom} {Q : State → Prop} {stop : Word → Bool} :
    ∀ {n : Nat} {s t : State}, runUntil c D stop n s = some t → okUntil c D stop P n s → Q t →
      Reach c P D Q s
  | 0, _, _, h, _, _ => by simp [NoCompiler.runUntil] at h
  | n + 1, s, t, h, hok, hq => by
    by_cases hdx : D.mem s.pc ∧ s.exit = none
    · obtain ⟨hd, hx⟩ := hdx
      cases hs : stepC c s with
      | none => simp [NoCompiler.runUntil, hd, hx, hs] at h
      | some s' =>
        obtain ⟨i, hi, he⟩ := stepC_some hs
        refine Reach.exec_some hd hx hi (hok.1 i hi) he ?_
        by_cases hstop : stops D stop s' = true
        · simp only [NoCompiler.runUntil, hd, hx, and_self, ite_true, hs, hstop, Option.some.injEq] at h
          subst h; exact .done hq
        · simp only [Bool.not_eq_true] at hstop
          simp only [NoCompiler.runUntil, hd, hx, and_self, ite_true, hs, hstop, Bool.false_eq_true,
            ite_false] at h
          exact Reach.of_runUntil h (hok.2 s' hs hstop) hq
    · simp [NoCompiler.runUntil, hdx] at h

/-! ## A's computed run, without alignment checks

A's run is known to be safe, so at every step `exec` succeeds; `execNA` is
`exec` without the alignment test of loads and stores, equal to `exec`
wherever `exec` succeeds. Computing A's path with it leaves no fault
branches, and the alignment of A's accesses comes out as facts (`okUntilA`),
which is what B's accesses at the same addresses need. -/

def execNA (i : Instr) (s : State) : Option State :=
  match i with
  | .load op rd rs1 off => some ((s.setReg rd (loadVal op s.mem (ea s rs1 off))).setPc (s.pc + 4))
  | .store op rs1 rs2 off =>
    some ((s.setMem (writeLE s.mem (ea s rs1 off) (s.reg rs2).toNat op.width)).setPc (s.pc + 4))
  | i => exec i s

/-- A load or store is aligned. -/
def AlignOk : Instr → State → Prop
  | .load op _ rs1 off, s => aligned (ea s rs1 off) op.width
  | .store op rs1 _ off, s => aligned (ea s rs1 off) op.width
  | _, _ => True

theorem execNA_of_exec {i : Instr} {s s' : State} (h : exec i s = some s') :
    execNA i s = some s' ∧ AlignOk i s := by
  cases i with
  | load op rd rs1 off =>
    simp only [exec] at h; split at h
    · rename_i ha; simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, ha⟩
    · simp at h
  | store op rs1 rs2 off =>
    simp only [exec] at h; split at h
    · rename_i ha; simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, ha⟩
    · simp at h
  | _ => exact ⟨h, trivial⟩

def stepCA (c : Code) (s : State) : Option State :=
  match c.instr s.pc with
  | some i => execNA i s
  | none => none

def runUntilA (c : Code) (D : Dom) (stop : Word → Bool) : Nat → State → Option State
  | 0, _ => none
  | n + 1, s =>
    if D.mem s.pc ∧ s.exit = none then
      match stepCA c s with
      | some s' => if stops D stop s' then some s' else runUntilA c D stop n s'
      | none => none
    else none

/-- What A's computed run does after one step. -/
def contA (c : Code) (D : Dom) (stop : Word → Bool) (n : Nat) : Option State → Option State
  | some s' => if stops D stop s' then some s' else runUntilA c D stop n s'
  | none => none

@[simp] theorem contA_some (c : Code) (D : Dom) (stop : Word → Bool) (n : Nat) (s' : State) :
    contA c D stop n (some s') = if stops D stop s' then some s' else runUntilA c D stop n s' := rfl
@[simp] theorem contA_none (c : Code) (D : Dom) (stop : Word → Bool) (n : Nat) :
    contA c D stop n none = none := rfl

/-- One step of A's computed run, for rewriting one step at a time. -/
theorem runUntilA_succ (c : Code) (D : Dom) (stop : Word → Bool) (n : Nat) (s : State) :
    runUntilA c D stop (n + 1) s =
      if D.mem s.pc ∧ s.exit = none then contA c D stop n (stepCA c s) else none := by
  simp only [runUntilA]; split <;> rfl

/-- What A's computed run gives at every step: the permission and the alignment. -/
def okUntilA (c : Code) (D : Dom) (stop : Word → Bool) (P : Perm) : Nat → State → Prop
  | 0, _ => True
  | n + 1, s =>
    (∀ i, c.instr s.pc = some i → InstrOk P i s ∧ AlignOk i s) ∧
    ∀ s', stepCA c s = some s' → stops D stop s' = false → okUntilA c D stop P n s'

/-- A's side: A's computed path from a safe state is a run of A, with A's
    permission and alignment at every step; A is still safe at its end. -/
theorem Exec.runUntilA {c : Code} {P : Perm} {D : Dom} {Q : State → Prop} {stop : Word → Bool} :
    ∀ {n : Nat} {s t : State}, Exec c P D Q s → runUntilA c D stop n s = some t →
      RunPlus c P D s t ∧ okUntilA c D stop P n s ∧ Exec c P D Q t
  | 0, _, _, _, h => by simp [NoCompiler.runUntilA] at h
  | n + 1, s, t, hA, h => by
    by_cases hdx : D.mem s.pc ∧ s.exit = none
    · obtain ⟨hd, hx⟩ := hdx
      cases hs : stepCA c s with
      | none => simp [NoCompiler.runUntilA, hd, hx, hs] at h
      | some s' =>
        have hi' : ∃ i, c.instr s.pc = some i ∧ execNA i s = some s' := by
          unfold stepCA at hs; split at hs
          · rename_i i hi; exact ⟨i, hi, hs⟩
          · simp at hs
        obtain ⟨i, hi, hna⟩ := hi'
        have hne : i ≠ .ecall := by rintro rfl; simp [execNA, exec_ecall] at hna
        obtain ⟨s'', he, hok, hst, hA'⟩ := Exec.stepA' hA hd hx hi hne
        obtain ⟨hna', hal⟩ := execNA_of_exec he
        rw [hna] at hna'; cases hna'
        have hokI : ∀ i', c.instr s.pc = some i' → InstrOk P i' s ∧ AlignOk i' s := by
          intro i' hi''; rw [hi] at hi''; cases hi''; exact ⟨hok, hal⟩
        by_cases hstop : stops D stop s' = true
        · simp only [NoCompiler.runUntilA, hd, hx, and_self, ite_true, hs, hstop, Option.some.injEq] at h
          subst h
          refine ⟨⟨_, hd, hst, .refl _⟩, ⟨hokI, fun s₂ hs₂ hn => ?_⟩, hA'⟩
          rw [hs] at hs₂; cases hs₂; rw [hstop] at hn; cases hn
        · simp only [Bool.not_eq_true] at hstop
          simp only [NoCompiler.runUntilA, hd, hx, and_self, ite_true, hs, hstop, Bool.false_eq_true,
            ite_false] at h
          obtain ⟨⟨s₁, hd₁, hst₁, hrun⟩, hok', hA''⟩ := Exec.runUntilA hA' h
          refine ⟨⟨_, hd, hst, .step hd₁ hst₁ hrun⟩, ⟨hokI, fun s₂ hs₂ _ => ?_⟩, hA''⟩
          rw [hs] at hs₂; cases hs₂; exact hok'
    · simp [NoCompiler.runUntilA, hdx] at h

/-! ## Cut points -/

/-- A cut: B at `pb` and A at `pa`, agreeing on `live`, with the relational
    invariant `inv s0 sa sb` (`s0` the entry state). -/
structure Cut where
  pb : Word
  pa : Word
  live : List Reg
  inv : State → State → State → Prop

/-- Running at a cut, both returned to `s0`'s ra, or both exited. -/
def CutRel (cuts : List Cut) (s0 sa sb : State) : Prop :=
  (∃ c ∈ cuts, sb.pc = c.pb ∧ sa.pc = c.pa ∧ sa.exit = none ∧ sa.reg 1 = s0.reg 1 ∧
    Agree c.live sa sb ∧ c.inv s0 sa sb) ∨
  (sa.exit = none ∧ sa.pc = s0.reg 1 ∧ sb.pc = s0.reg 1 ∧ Agree Lockstep.obsRegs sa sb) ∨
  (sa.exit ≠ none ∧ Agree [] sa sb)

/-- The pcs of A's cuts, as a stop predicate for `runUntil`. -/
def Cut.stopA (cuts : List Cut) (p : Word) : Bool := cuts.any (·.pa == p)
def Cut.stopB (cuts : List Cut) (p : Word) : Bool := cuts.any (·.pb == p)

/-- Refinement from cut points: the entry pair is a cut whose invariant holds
    at the entry, every cut is inside both functions, and from every cut the
    paths of both reach `CutRel` again (`move`, the obligation one path at a
    time). -/
theorem Refines.of_cuts {α : Type} {sp : Spec α} {cA cB : Code} {DA DB : Dom} {eA eB : Word}
    (cuts : List Cut) (c0 : Cut) (hc0 : c0 ∈ cuts) (hb0 : c0.pb = eB) (ha0 : c0.pa = eA)
    (hinv0 : ∀ a s, Entry DA eA s → sp.pre a s → c0.inv s s (s.setPc eB))
    (hmem : ∀ c ∈ cuts, DB.mem c.pb ∧ DA.mem c.pa)
    (move : ∀ a s, Entry DA eA s → ¬ DB.mem (s.reg Reg.ra) → sp.pre a s → ∀ c ∈ cuts, ∀ sa sb,
      sb.pc = c.pb → sa.pc = c.pa → sa.exit = none → sa.reg 1 = s.reg 1 → Agree c.live sa sb →
      c.inv s sa sb → Exec cA (sp.perm a s) DA (fun _ => True) sa →
      Reach cB (sp.perm a s) DB (fun tb => ∃ ta, RunPlus cA (sp.perm a s) DA sa ta ∧ CutRel cuts s ta tb) sb) :
    Refines sp cA DA eA cB DB eB := by
  refine Refines.of_bigSim (fun _ s => CutRel cuts s) (fun a s he hraB hp => ?_)
    (fun a s he hp => .inl ⟨c0, hc0, by simp [hb0], by rw [he.pc, ha0], he.live, rfl,
      ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, hinv0 a s he hp⟩)
  have hraA := he.ret
  refine ⟨?fin, ?move⟩
  · intro sa sb hr hf
    rcases hr with ⟨c, hc, hpb, _, hx, _, hag, _⟩ | ⟨hx, hpa, hpb, hag⟩ | ⟨hx, hag⟩
    · exfalso
      rcases hf with h | h
      · exact h (hpb ▸ (hmem c hc).1)
      · exact h (hag.exit ▸ hx)
    · refine ⟨sa, .refl _, .inl (hpa ▸ hraA), hag.trace, hag.exit, fun _ => ⟨hpa.trans hpb.symm,
        fun r hr => hag.regs r (List.mem_cons_of_mem _ hr), fun x _ => by rw [hag.mem]⟩⟩
    · exact ⟨sa, .refl _, .inr hx, hag.trace, hag.exit, fun h => absurd h hx⟩
  · intro sa sb hr hf hA
    rcases hr with ⟨c, hc, hpb, hpa, hx, hra, hag, hinv⟩ | ⟨_, _, hpb, _⟩ | ⟨hx, hag⟩
    · exact move a s he hraB hp c hc sa sb hpb hpa hx hra hag hinv hA
    · exact absurd (.inl (hpb ▸ hraB)) hf
    · exact absurd (.inr (hag.exit ▸ hx)) hf

/-! ## Computed runs that carry their facts

`runUntilP` (B) returns the end state and the conjunction of B's permission
obligations along the path; `runUntilAP` (A) returns the end state and the
conjunction of A's permissions and alignments along its path, which A's
safety proves. One symbolic evaluation of each gives everything a path
needs. -/

def contP (c : Code) (D : Dom) (stop : Word → Bool) (P : Perm)
    (run : State → Option (State × Prop)) (q : Prop) : Option State → Option (State × Prop)
  | some s' => if stops D stop s' then some (s', q) else (run s').map fun x => (x.1, q ∧ x.2)
  | none => none

def runUntilP (c : Code) (D : Dom) (stop : Word → Bool) (P : Perm) : Nat → State → Option (State × Prop)
  | 0, _ => none
  | n + 1, s =>
    if D.mem s.pc ∧ s.exit = none then
      match c.instr s.pc with
      | some i => contP c D stop P (runUntilP c D stop P n) (InstrOk P i s) (exec i s)
      | none => none
    else none

def runUntilAP (c : Code) (D : Dom) (stop : Word → Bool) (P : Perm) : Nat → State → Option (State × Prop)
  | 0, _ => none
  | n + 1, s =>
    if D.mem s.pc ∧ s.exit = none then
      match c.instr s.pc with
      | some i => contP c D stop P (runUntilAP c D stop P n) (InstrOk P i s ∧ AlignOk i s) (execNA i s)
      | none => none
    else none

theorem runUntilP_succ (c : Code) (D : Dom) (stop : Word → Bool) (P : Perm) (n : Nat) (s : State) :
    runUntilP c D stop P (n + 1) s =
      if D.mem s.pc ∧ s.exit = none then
        match c.instr s.pc with
        | some i => contP c D stop P (runUntilP c D stop P n) (InstrOk P i s) (exec i s)
        | none => none
      else none := rfl

theorem runUntilAP_succ (c : Code) (D : Dom) (stop : Word → Bool) (P : Perm) (n : Nat) (s : State) :
    runUntilAP c D stop P (n + 1) s =
      if D.mem s.pc ∧ s.exit = none then
        match c.instr s.pc with
        | some i => contP c D stop P (runUntilAP c D stop P n) (InstrOk P i s ∧ AlignOk i s) (execNA i s)
        | none => none
      else none := rfl

@[simp] theorem contP_some (c : Code) (D : Dom) (stop : Word → Bool) (P : Perm)
    (run : State → Option (State × Prop)) (q : Prop) (s' : State) :
    contP c D stop P run q (some s') =
      if stops D stop s' then some (s', q) else (run s').map fun x => (x.1, q ∧ x.2) := rfl
@[simp] theorem contP_none (c : Code) (D : Dom) (stop : Word → Bool) (P : Perm)
    (run : State → Option (State × Prop)) (q : Prop) : contP c D stop P run q none = none := rfl

/-- B's side: the computed path, its obligations met, reaches its end. -/
theorem Reach.of_runUntilP {c : Code} {P : Perm} {D : Dom} {Q : State → Prop} {stop : Word → Bool} :
    ∀ {n : Nat} {s t : State} {q : Prop}, runUntilP c D stop P n s = some (t, q) → q → Q t →
      Reach c P D Q s
  | 0, _, _, _, h, _, _ => by simp [runUntilP] at h
  | n + 1, s, t, q, h, hq, hQ => by
    by_cases hdx : D.mem s.pc ∧ s.exit = none
    · obtain ⟨hd, hx⟩ := hdx
      rw [runUntilP_succ, if_pos ⟨hd, hx⟩] at h
      cases hi : c.instr s.pc with
      | none => rw [hi] at h; simp at h
      | some i =>
        rw [hi] at h; try simp only at h
        cases he : exec i s with
        | none => rw [he] at h; simp at h
        | some s' =>
          rw [he, contP_some] at h
          by_cases hst : stops D stop s' = true
          · rw [if_pos hst] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact Reach.exec_some hd hx hi hq he (.done hQ)
          · rw [if_neg hst] at h
            cases hr : runUntilP c D stop P n s' with
            | none => rw [hr] at h; simp at h
            | some p =>
              obtain ⟨t', q'⟩ := p
              rw [hr] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact Reach.exec_some hd hx hi hq.1 he (Reach.of_runUntilP hr hq.2 hQ)
    · rw [runUntilP_succ, if_neg hdx] at h; simp at h

/-- A's side: the computed path from a safe state is a run of A, and its
    facts (permission, alignment at every step) hold; A is still safe at the end. -/
theorem Exec.runUntilAP {c : Code} {P : Perm} {D : Dom} {Q : State → Prop} {stop : Word → Bool} :
    ∀ {n : Nat} {s t : State} {q : Prop}, Exec c P D Q s → runUntilAP c D stop P n s = some (t, q) →
      RunPlus c P D s t ∧ q ∧ Exec c P D Q t
  | 0, _, _, _, _, h => by simp [NoCompiler.runUntilAP] at h
  | n + 1, s, t, q, hA, h => by
    by_cases hdx : D.mem s.pc ∧ s.exit = none
    · obtain ⟨hd, hx⟩ := hdx
      rw [runUntilAP_succ, if_pos ⟨hd, hx⟩] at h
      cases hi : c.instr s.pc with
      | none => rw [hi] at h; simp at h
      | some i =>
        rw [hi] at h; try simp only at h
        cases hna : execNA i s with
        | none => rw [hna] at h; simp at h
        | some s' =>
          have hne : i ≠ .ecall := by rintro rfl; simp [execNA, exec_ecall] at hna
          obtain ⟨s'', he, hok, hst, hA'⟩ := Exec.stepA' hA hd hx hi hne
          obtain ⟨hna', hal⟩ := execNA_of_exec he
          rw [hna] at hna'; cases hna'
          rw [hna, contP_some] at h
          by_cases hsp : stops D stop s' = true
          · rw [if_pos hsp] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨⟨_, hd, hst, .refl _⟩, ⟨hok, hal⟩, hA'⟩
          · rw [if_neg hsp] at h
            cases hr : NoCompiler.runUntilAP c D stop P n s' with
            | none => rw [hr] at h; simp at h
            | some p =>
              obtain ⟨t', q'⟩ := p
              rw [hr] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨⟨s₁, hd₁, hst₁, hrun⟩, hq', hA''⟩ := Exec.runUntilAP hA' hr
              exact ⟨⟨_, hd, hst, .step hd₁ hst₁ hrun⟩, ⟨⟨hok, hal⟩, hq'⟩, hA''⟩
    · rw [runUntilAP_succ, if_neg hdx] at h; simp at h

/-- Writing x0 does nothing. -/
theorem setReg_x0 (s : State) (v : Word) : s.setReg 0 v = s := by simp [State.setReg]

/-! ## Stepping lemmas for evaluation -/

def contB (c : Code) (D : Dom) (stop : Word → Bool) (n : Nat) : Option State → Option State
  | some s' => if stops D stop s' then some s' else runUntil c D stop n s'
  | none => none

@[simp] theorem contB_some (c : Code) (D : Dom) (stop : Word → Bool) (n : Nat) (s' : State) :
    contB c D stop n (some s') = if stops D stop s' then some s' else runUntil c D stop n s' := rfl
@[simp] theorem contB_none (c : Code) (D : Dom) (stop : Word → Bool) (n : Nat) :
    contB c D stop n none = none := rfl

theorem runUntil_succ (c : Code) (D : Dom) (stop : Word → Bool) (n : Nat) (s : State) :
    runUntil c D stop (n + 1) s =
      if D.mem s.pc ∧ s.exit = none then contB c D stop n (stepC c s) else none := by
  simp only [runUntil]; split <;> rfl

/-- The facts A's computed path gives, one step at a time: at `s`, the
    instruction's permission and alignment; then the rest. -/
theorem okUntilA_succ {c : Code} {D : Dom} {stop : Word → Bool} {P : Perm} {n : Nat} {s : State}
    {i : Instr} (h : okUntilA c D stop P (n + 1) s) (hi : c.instr s.pc = some i) :
    InstrOk P i s ∧ AlignOk i s ∧ ∀ s', stepCA c s = some s' → stops D stop s' = false →
      okUntilA c D stop P n s' :=
  ⟨(h.1 i hi).1, (h.1 i hi).2, h.2⟩

/-- B's permission obligations, one step at a time. -/
theorem okUntil_succ_intro {c : Code} {D : Dom} {stop : Word → Bool} {P : Perm} {n : Nat} {s : State}
    {i : Instr} (hi : c.instr s.pc = some i) (hok : InstrOk P i s)
    (hrest : ∀ s', stepC c s = some s' → stops D stop s' = false → okUntil c D stop P n s') :
    okUntil c D stop P (n + 1) s :=
  ⟨fun i' hi' => by rw [hi] at hi'; cases hi'; exact hok, hrest⟩

/-- Evaluate A's computed run in hypothesis `h` one step at a time: the
    instruction from the image (`nocompiler_image` lemmas), pcs and region
    tests on literals, branches the context decides (the local hypotheses are
    used); a branch it does not decide is split (`split at h`), giving one
    goal per path, with the branch condition as a hypothesis. -/
macro "rel_runA" h:ident : tactic => `(tactic| repeat' (first
  | (split at $h:ident)
  | (rw [runUntilA_succ] at $h:ident
     simp only [nocompiler_image, stepCA, stops, execNA, exec, evalBr, jumpTo, Dom.mem, beq_iff_eq,
       aligned, State.setPc_pc, State.setReg_pc, State.setMem_pc, State.setPc_exit, State.setReg_exit,
       State.setMem_exit, State.setPc_reg, State.setPc_mem, State.setPc_setPc, decide_true, decide_false,
       and_true, and_false, true_and, false_and, ite_true, ite_false, decide_not,
       Bool.false_eq_true, Bool.true_eq_false, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceToNat,
       BitVec.reduceBEq, BitVec.reduceSignExtend, List.any_cons, List.any_nil, Nat.reduceLT, Nat.reduceMod,
       Bool.or_false, Bool.or_true, Bool.false_or, Bool.true_or, Bool.or_self, Bool.not_true,
       Bool.not_false, ne_eq, not_true_eq_false, not_false_eq_true, Option.some.injEq, reduceCtorEq,
       apply_ite (contA _ _ _ _), contA_some, contA_none, *] at $h:ident)))

/-- B's run, the same way (`exec`, so a load's or store's alignment is a
    condition: it is split on, and the misaligned branch has to be refuted,
    by A's alignment at the same address). -/
macro "rel_runB" h:ident : tactic => `(tactic| repeat' (first
  | (split at $h:ident)
  | (rw [runUntil_succ] at $h:ident
     simp only [nocompiler_image, stepC, stops, exec, evalBr, jumpTo, Dom.mem, beq_iff_eq,
       State.setPc_pc, State.setReg_pc, State.setMem_pc, State.setPc_exit, State.setReg_exit,
       State.setMem_exit, State.setPc_reg, State.setPc_mem, State.setPc_setPc, decide_true, decide_false,
       and_true, and_false, true_and, false_and, ite_true, ite_false, decide_not,
       Bool.false_eq_true, Bool.true_eq_false, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceToNat,
       BitVec.reduceBEq, BitVec.reduceSignExtend, List.any_cons, List.any_nil, Nat.reduceLT, Nat.reduceMod,
       Bool.or_false, Bool.or_true, Bool.false_or, Bool.true_or, Bool.or_self, Bool.not_true,
       Bool.not_false, ne_eq, not_true_eq_false, not_false_eq_true, Option.some.injEq, reduceCtorEq,
       apply_ite (contB _ _ _ _), contB_some, contB_none, *] at $h:ident)))

/-- Evaluate a computed run (`runUntilP` or `runUntilAP`) in hypothesis `h`,
    one step at a time; undecided branches are split. -/
macro "rel_eval" h:ident : tactic => `(tactic| repeat' (first
  | (split at $h:ident)
  | ((first | rw [runUntilP_succ] at $h:ident | rw [runUntilAP_succ] at $h:ident)
     simp only [nocompiler_image, stops, execNA, exec, evalBr, jumpTo, Dom.mem, beq_iff_eq, aligned, ea,
       setReg_x0, State.reg_setReg, Fin.isValue, Fin.reduceEq, State.setReg_mem, State.setReg_trace,
       State.setPc_trace,
       State.setPc_pc, State.setReg_pc, State.setMem_pc, State.setPc_exit, State.setReg_exit,
       State.setMem_exit, State.setPc_reg, State.setPc_mem, State.setPc_setPc, decide_true, decide_false,
       and_true, and_false, true_and, false_and, ite_true, ite_false, decide_not,
       Bool.false_eq_true, Bool.true_eq_false, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceToNat,
       BitVec.reduceBEq, BitVec.reduceSignExtend, List.any_cons, List.any_nil, Nat.reduceLT, Nat.reduceMod,
       Bool.or_false, Bool.or_true, Bool.false_or, Bool.true_or, Bool.or_self, Bool.not_true,
       Bool.not_false, ne_eq, not_true_eq_false, not_false_eq_true, Option.some.injEq, reduceCtorEq,
       apply_ite (contP _ _ _ _ _ _), apply_ite (Option.map _), contP_some, contP_none, Option.map_some,
       Option.map_none, *] at $h:ident)))

end NoCompiler
