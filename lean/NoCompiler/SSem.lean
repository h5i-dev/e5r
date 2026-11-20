import NoCompiler.Frame
import NoCompiler.Spec

/-
The structured semantics of the profile, version 1 (docs/isa/v1.md, "The
structured semantics"), and theorem T1: what is shown in it holds of the
machine.

A function at level L2 runs with a *structured* permission `P`: the regions
of its specification, its own address-taken ranges, and the stack below its
frame for its callees, but not its slots. Its slots are not memory it has
permission for; they are touched only by the `ld`/`sd` instructions that R6
lets touch them, at exactly a slot's address, and those steps need no
permission (`SStep.slot`). Every other step is a `Step` under `P`, so it gets
stuck (has no step) on an access outside `P`: a store through a pointer into
a slot has no structured step. A call is a run of the callee under `P`
(`SReach.call`), which the caller sees only through what a verified callee
guarantees.

The pc stays in the state: what the structured semantics removes from a
proof is not the pc but the need to reason about the frame in memory
(theorems T2 and T3, NoCompiler/SFrame.lean). Labels instead of addresses are
the tactic's business (NoCompiler/Auto.lean).

T1 (`SReach.sound`): a structured run is a machine run under `P` plus the
frame, `P.withFrame`. The frame is the one place the structured permission
is narrower than the machine's.
-/
namespace NoCompiler
namespace Struct

namespace Frame
/-- The bottom of the frame of a function entered with `sp0`. -/
def base (fr : Frame) (sp0 : Word) : Word := sp0 - BitVec.ofNat 64 fr.size

/-- The frame's bytes. -/
def region (fr : Frame) (sp0 : Word) : Region := ⟨fr.base sp0, fr.size⟩

/-- `a` is the address of one of the slots. -/
def isSlot (fr : Frame) (sp0 a : Word) : Bool :=
  fr.slots.any fun s => s.off + 8 ≤ fr.size && fr.size < 2 ^ 64 &&
    a == fr.base sp0 + BitVec.ofNat 64 s.off

/-- The address-taken ranges as regions. -/
def rangeRegions (fr : Frame) (sp0 : Word) : List Region :=
  fr.ranges.map fun g => ⟨fr.base sp0 + BitVec.ofNat 64 g.off, g.len⟩
end Frame

/-- `P`, with the whole frame writable too: the machine's view. -/
def _root_.NoCompiler.Perm.withFrame (P : Perm) (fr : Frame) (sp0 : Word) : Perm :=
  { rd := P.rd, wr := P.wr ++ [fr.region sp0] }

theorem _root_.NoCompiler.Perm.le_withFrame (P : Perm) (fr : Frame) (sp0 : Word) :
    P.le (P.withFrame fr sp0) := by
  constructor
  · rintro a n (h0 | ⟨r, hr, hc⟩)
    · exact .inl h0
    · refine .inr ⟨r, ?_, hc⟩
      simp only [Perm.withFrame, List.mem_append] at hr ⊢
      rcases hr with h | h
      · exact .inl h
      · exact .inr (.inl h)
  · rintro a n (h0 | ⟨r, hr, hc⟩)
    · exact .inl h0
    · exact .inr ⟨r, by simp only [Perm.withFrame, List.mem_append]; exact .inl hr, hc⟩

/-- A slot instruction at `s`: `ld` or `sd` with base `sp` at a slot's address. -/
def slotAccess (fr : Frame) (sp0 : Word) (s : State) : Instr → Bool
  | .load .ld _ rs1 k => rs1.val == 2 && fr.isSlot sp0 (ea s rs1 k)
  | .store .sd rs1 _ k => rs1.val == 2 && fr.isSlot sp0 (ea s rs1 k)
  | _ => false

/-- A structured step. -/
inductive SStep (c : Code) (fr : Frame) (sp0 : Word) (P : Perm) : State → State → Prop
  | slot {s s' : State} {i : Instr} :
      s.exit = none → c.instr s.pc = some i → slotAccess fr sp0 s i = true → exec i s = some s' →
      SStep c fr sp0 P s s'
  | step {s s' : State} : Step c P s s' → SStep c fr sp0 P s s'

/-- What a caller knows when a verified callee entered at `s` returns at `s'`. -/
def CallDone (P : Perm) (s s' : State) : Prop :=
  s'.exit = none ∧ s'.pc = s.reg Reg.ra ∧ Preserved s s' ∧ ∀ x, ¬ P.writable x → s'.mem x = s.mem x

/-- Structured reachability: like `Reach`, over `SStep`, with calls as runs
    of the callee under `P` that end as a verified callee does (or end the
    process). -/
inductive SReach (c : Code) (fr : Frame) (sp0 : Word) (P : Perm) (D : Dom) (Q : State → Prop) :
    State → Prop
  | done {s : State} : Q s → SReach c fr sp0 P D Q s
  | step {s : State} :
      D.mem s.pc → (∃ s', SStep c fr sp0 P s s') → (∀ s', SStep c fr sp0 P s s' → SReach c fr sp0 P D Q s') →
      SReach c fr sp0 P D Q s
  | call {s : State} {Q' : State → Prop} :
      Reach c P D Q' s → (∀ s', Q' s' → CallDone P s s' ∨ s'.exit ≠ none) →
      (∀ s', Q' s' → SReach c fr sp0 P D Q s') → SReach c fr sp0 P D Q s

/-- A structured run until the first exit from `D`. -/
def SExec (c : Code) (fr : Frame) (sp0 : Word) (P : Perm) (D : Dom) (Q : State → Prop) (s : State) : Prop :=
  SReach c fr sp0 P D (fun s => Final D s ∧ Q s) s

theorem isSlot_covers {fr : Frame} {sp0 a : Word} (h : fr.isSlot sp0 a = true) :
    (fr.region sp0).covers a 8 := by
  unfold Frame.isSlot at h
  obtain ⟨sl, _, hs⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hs
  obtain ⟨⟨hle, hlt⟩, rfl⟩ := hs
  unfold Region.covers Frame.region
  simp only
  rw [show fr.base sp0 + BitVec.ofNat 64 sl.off - fr.base sp0 = BitVec.ofNat 64 sl.off by bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact hle

/-- A slot step is a machine step under `P.withFrame`. -/
theorem slot_step {c : Code} {fr : Frame} {sp0 : Word} {P : Perm} {s s' : State} {i : Instr}
    (hx : s.exit = none) (hi : c.instr s.pc = some i) (hsl : slotAccess fr sp0 s i = true)
    (he : exec i s = some s') : Step c (P.withFrame fr sp0) s s' := by
  refine .exec hx hi ?_ he
  have hreg : ∀ a, (fr.region sp0) ∈ (P.withFrame fr sp0).wr → (fr.region sp0).covers a 8 →
      ∃ r ∈ (P.withFrame fr sp0).wr, r.covers a 8 := fun a hm hc => ⟨_, hm, hc⟩
  have hm : (fr.region sp0) ∈ (P.withFrame fr sp0).wr := by simp [Perm.withFrame]
  cases i with
  | load op rd rs1 k =>
    cases op <;> simp [slotAccess] at hsl
    obtain ⟨_, hs⟩ := hsl
    obtain ⟨r, hr, hc⟩ := hreg _ hm (isSlot_covers hs)
    exact .inr ⟨r, List.mem_append.2 (.inr hr), hc⟩
  | store op rs1 rs2 k =>
    cases op <;> simp [slotAccess] at hsl
    obtain ⟨_, hs⟩ := hsl
    obtain ⟨r, hr, hc⟩ := hreg _ hm (isSlot_covers hs)
    exact .inr ⟨r, hr, hc⟩
  | _ => simp [slotAccess] at hsl

/-- Every structured step is a machine step under `P.withFrame`. -/
theorem SStep.machine {c : Code} {fr : Frame} {sp0 : Word} {P : Perm} {s s' : State}
    (h : SStep c fr sp0 P s s') : Step c (P.withFrame fr sp0) s s' := by
  cases h with
  | slot hx hi hsl he => exact slot_step hx hi hsl he
  | step h => exact h.mono (P.le_withFrame fr sp0)

/-- A machine step from a state that has a structured step is a structured
    step: the machine is deterministic but for syscalls, and those are
    `Step`s under `P` either way. -/
theorem SStep.of_machine {c : Code} {fr : Frame} {sp0 : Word} {P : Perm} {s s₁ s' : State}
    (h : SStep c fr sp0 P s s₁) (h' : Step c (P.withFrame fr sp0) s s') : SStep c fr sp0 P s s' := by
  cases h with
  | step h => exact .step (h.restrict h')
  | slot hx hi hsl he =>
    cases h' with
    | exec _ hi' _ he' =>
      rw [hi] at hi'; cases hi'
      exact .slot hx hi hsl he'
    | sys _ hi' _ _ =>
      rw [hi] at hi'; cases hi'
      simp [slotAccess] at hsl

/-- T1: a structured run is a machine run, under `P` with the frame. -/
theorem SReach.sound {c : Code} {fr : Frame} {sp0 : Word} {P : Perm} {D : Dom} {Q : State → Prop}
    {s : State} (h : SReach c fr sp0 P D Q s) : Reach c (P.withFrame fr sp0) D Q s := by
  induction h with
  | done hq => exact .done hq
  | step hd hex _ ih =>
    obtain ⟨s₁, h₁⟩ := hex
    exact .step hd ⟨s₁, h₁.machine⟩ (fun s' h' => ih s' (h₁.of_machine h'))
  | call hr _ _ ih => exact Reach.bind hr (P.le_withFrame fr sp0) (fun _ h => h) ih

theorem SExec.sound {c : Code} {fr : Frame} {sp0 : Word} {P : Perm} {D : Dom} {Q : State → Prop}
    {s : State} (h : SExec c fr sp0 P D Q s) : Exec c (P.withFrame fr sp0) D Q s :=
  SReach.sound h

end Struct
end NoCompiler
