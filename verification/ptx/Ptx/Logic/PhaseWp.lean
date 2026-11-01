/-
Symbolic execution for phase derivations.

`wpR … cut Q f s h d` runs the instruction table from `s` for at most `f`
steps, through loads, stores and atomics on the cells, until a cut point, a
`bar.sync` or `ret`, and asks `Q` there; `wpR_sound` turns it into a `Run`
derivation with index `f`. On a concrete kernel `simp only [ptx_eval, …]`
evaluates it the way `wp` is evaluated for the M3 class (Ptx/Tactics/Eval.lean),
leaving the access legality, the footprint and `Q`.

`Run.seq` and `Run.loop` compose derivations, adding their indices.
-/
import Ptx.Logic.Phases

namespace Ptx

section
variable (K : Kernel) (al : Sp → List Region) (c : Ctx) (F : Foot) (Cell : Addr → Prop) (A : CellAlg)


def wpR (cut : Nat → Bool) (Q : TState → Heap → Ghost → Prop) :
    Nat → TState → Heap → Ghost → Prop
  | 0, _, _, _ => False
  | f + 1, s, h, d =>
    match action K c s with
    | .next s' => if cut s'.pc then Q s' h d else wpR cut Q f s' h d
    | .load sp a sz k =>
      accessOk (al sp) a sz = true ∧ (∀ x, covers a sz.bytes x → F.touches (sp, x)) ∧
        (if cut (k (rd (h.at sp) a sz)).pc then Q (k (rd (h.at sp) a sz)) h d
         else wpR cut Q f (k (rd (h.at sp) a sz)) h d)
    | .store sp a sz v s' =>
      accessOk (al sp) a sz = true ∧ (∀ x, covers a sz.bytes x → F.w (sp, x)) ∧
        (if cut s'.pc then Q s' (h.set sp (wr (h.at sp) a sz v)) d
         else wpR cut Q f s' (h.set sp (wr (h.at sp) a sz v)) d)
    | .atom .global a sz g k =>
      sz = A.sz ∧ accessOk (al .global) a sz = true ∧ Cell a ∧ ∃ δ, Accum A g δ ∧
        ∀ v, (if cut (k v).pc then Q (k v) h (d.acc A a δ) else wpR cut Q f (k v) h (d.acc A a δ))
    | .bar => Q s h d
    | .done => Q s h d
    | _ => False

/-- `wpR` after the action is known, so `simp` unfolds one step at a time. -/
def wpRAct (cut : Nat → Bool) (Q : TState → Heap → Ghost → Prop) (f : Nat) (act : Action)
    (s : TState) (h : Heap) (d : Ghost) : Prop :=
  match act with
  | .next s' => if cut s'.pc then Q s' h d else wpR K al c F Cell A cut Q f s' h d
  | .load sp a sz k =>
    accessOk (al sp) a sz = true ∧ (∀ x, covers a sz.bytes x → F.touches (sp, x)) ∧
      (if cut (k (rd (h.at sp) a sz)).pc then Q (k (rd (h.at sp) a sz)) h d
       else wpR K al c F Cell A cut Q f (k (rd (h.at sp) a sz)) h d)
  | .store sp a sz v s' =>
    accessOk (al sp) a sz = true ∧ (∀ x, covers a sz.bytes x → F.w (sp, x)) ∧
      (if cut s'.pc then Q s' (h.set sp (wr (h.at sp) a sz v)) d
       else wpR K al c F Cell A cut Q f s' (h.set sp (wr (h.at sp) a sz v)) d)
  | .atom .global a sz g k =>
    sz = A.sz ∧ accessOk (al .global) a sz = true ∧ Cell a ∧ ∃ δ, Accum A g δ ∧
      ∀ v, (if cut (k v).pc then Q (k v) h (d.acc A a δ)
            else wpR K al c F Cell A cut Q f (k v) h (d.acc A a δ))
  | .bar => Q s h d
  | .done => Q s h d
  | _ => False

theorem wpR_succ (cut Q f s h d) :
    wpR K al c F Cell A cut Q (f + 1) s h d = wpRAct K al c F Cell A cut Q f (action K c s) s h d := by
  simp only [wpR, wpRAct]

end

section
variable {K : Kernel} {al : Sp → List Region} {c : Ctx} {F : Foot} {Cell : Addr → Prop} {A : CellAlg}
  {cut : Nat → Bool} {Q : TState → Heap → Ghost → Prop} {f : Nat} {s : TState} {h : Heap} {d : Ghost}

@[simp] theorem wpR_zero : wpR K al c F Cell A cut Q 0 s h d = False := rfl
@[simp] theorem wpRAct_next {s'} : wpRAct K al c F Cell A cut Q f (.next s') s h d =
    if cut s'.pc then Q s' h d else wpR K al c F Cell A cut Q f s' h d := rfl
@[simp] theorem wpRAct_load {sp a sz k} : wpRAct K al c F Cell A cut Q f (.load sp a sz k) s h d =
    (accessOk (al sp) a sz = true ∧ (∀ x, covers a sz.bytes x → F.touches (sp, x)) ∧
      (if cut (k (rd (h.at sp) a sz)).pc then Q (k (rd (h.at sp) a sz)) h d
       else wpR K al c F Cell A cut Q f (k (rd (h.at sp) a sz)) h d)) := rfl
@[simp] theorem wpRAct_store {sp a sz v s'} : wpRAct K al c F Cell A cut Q f (.store sp a sz v s') s h d =
    (accessOk (al sp) a sz = true ∧ (∀ x, covers a sz.bytes x → F.w (sp, x)) ∧
      (if cut s'.pc then Q s' (h.set sp (wr (h.at sp) a sz v)) d
       else wpR K al c F Cell A cut Q f s' (h.set sp (wr (h.at sp) a sz v)) d)) := rfl
@[simp] theorem wpRAct_atom {a sz g k} : wpRAct K al c F Cell A cut Q f (.atom .global a sz g k) s h d =
    (sz = A.sz ∧ accessOk (al .global) a sz = true ∧ Cell a ∧ ∃ δ, Accum A g δ ∧
      ∀ v, (if cut (k v).pc then Q (k v) h (d.acc A a δ)
            else wpR K al c F Cell A cut Q f (k v) h (d.acc A a δ))) := rfl
@[simp] theorem wpRAct_atom_shared {a sz g k} :
    wpRAct K al c F Cell A cut Q f (.atom .shared a sz g k) s h d = False := rfl
@[simp] theorem wpRAct_bar : wpRAct K al c F Cell A cut Q f .bar s h d = Q s h d := rfl
@[simp] theorem wpRAct_done : wpRAct K al c F Cell A cut Q f .done s h d = Q s h d := rfl
@[simp] theorem wpRAct_fault : wpRAct K al c F Cell A cut Q f .fault s h d = False := rfl
@[simp] theorem wpRAct_ite {p : Prop} [Decidable p] {a b : Action} :
    wpRAct K al c F Cell A cut Q f (if p then a else b) s h d =
      if p then wpRAct K al c F Cell A cut Q f a s h d else wpRAct K al c F Cell A cut Q f b s h d := by
  split <;> rfl

/-- Where `wpR` stops: a cut point after at least one step, a barrier or
`ret`. -/
def StopR (K : Kernel) (c : Ctx) (cut : Nat → Bool) (Q : TState → Heap → Ghost → Prop)
    (s : TState) (h : Heap) (d : Ghost) : Prop :=
  Q s h d ∧ (cut s.pc = true ∨ action K c s = .bar ∨ action K c s = .done)

theorem wpR_sound : ∀ {f s h d}, wpR K al c F Cell A cut Q f s h d →
    Run K al c F Cell A (StopR K c cut Q) f s h d := by
  intro f
  induction f with
  | zero => intro s h d hw; exact hw.elim
  | succ f ih =>
    intro s h d hw
    unfold wpR at hw
    have go : ∀ {s' h' d'}, (if cut s'.pc then Q s' h' d' else wpR K al c F Cell A cut Q f s' h' d') →
        Run K al c F Cell A (StopR K c cut Q) f s' h' d' := by
      intro s' h' d' hq
      by_cases hc : cut s'.pc = true
      · simp only [hc, ↓reduceIte] at hq; exact .stop ⟨hq, .inl hc⟩
      · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hq; exact ih hq
    split at hw
    · next s' ha => exact .next ha (go hw)
    · next sp a sz k ha => exact .load ha hw.1 hw.2.1 (go hw.2.2)
    · next sp a sz v s' ha => exact .store ha hw.1 hw.2.1 (go hw.2.2)
    · next a sz g k ha =>
      obtain ⟨rfl, hok, hc, δ, hδ, hk⟩ := hw
      exact .atom δ ha hok hc hδ fun v => go (hk v)
    · next ha => exact .stop ⟨hw, .inr (.inl ha)⟩
    · next ha => exact .stop ⟨hw, .inr (.inr ha)⟩
    · exact hw.elim

theorem Run.mono {J J' : TState → Heap → Ghost → Prop} {n m s h d}
    (hr : Run K al c F Cell A J n s h d) (hJ : ∀ s h d, J s h d → Run K al c F Cell A J' m s h d) :
    Run K al c F Cell A J' (n + m) s h d := by
  induction hr with
  | stop hj => exact (hJ _ _ _ hj).mono_index (by omega)
  | next ha _ ih => rw [Nat.add_right_comm]; exact .next ha ih
  | load ha hok hf _ ih => rw [Nat.add_right_comm]; exact .load ha hok hf ih
  | store ha hok hf _ ih => rw [Nat.add_right_comm]; exact .store ha hok hf ih
  | atom δ ha hok hc hf _ ih => rw [Nat.add_right_comm]; exact .atom δ ha hok hc hf ih

theorem Run.weaken {J J' : TState → Heap → Ghost → Prop} {n s h d}
    (hr : Run K al c F Cell A J n s h d) (hJ : ∀ s h d, J s h d → J' s h d) :
    Run K al c F Cell A J' n s h d := by
  induction hr with
  | stop hj => exact .stop (hJ _ _ _ hj)
  | next ha _ ih => exact .next ha ih
  | load ha hok hf _ ih => exact .load ha hok hf ih
  | store ha hok hf _ ih => exact .store ha hok hf ih
  | atom δ ha hok hc hf _ ih => exact .atom δ ha hok hc hf ih

/-- Loop rule: from every invariant state with measure `v`, `F` steps reach
an invariant state of smaller measure, or the exit condition. -/
theorem Run.loop {I : Nat → TState → Heap → Ghost → Prop} {J : TState → Heap → Ghost → Prop}
    {B : Nat}
    (step : ∀ v s h d, I v s h d →
      Run K al c F Cell A (fun s h d => (∃ v' < v, I v' s h d) ∨ J s h d) B s h d) :
    ∀ v s h d, I v s h d → Run K al c F Cell A J ((v + 1) * B) s h d := by
  intro v
  induction v using Nat.strongRecOn with
  | _ v ih =>
    intro s h d hI
    have := (step v s h d hI).mono (m := v * B) fun s' h' d' hq => by
      rcases hq with ⟨v', hv, hI'⟩ | hj
      · exact (ih v' hv s' h' d' hI').mono_index (Nat.mul_le_mul_right _ (by omega))
      · exact .stop hj
    rw [Nat.succ_mul, Nat.add_comm]
    exact this

end

end Ptx
