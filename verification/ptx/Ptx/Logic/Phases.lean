/-
One thread between two barriers: the per-phase logic for kernels with
shared memory, `bar.sync` and atomics.

`Run … F J n s h d` is an inductive derivation that thread state `s`, seeing
heap `h` (global memory and its CTA's shared memory), reaches a state
satisfying `J` in at most `n` steps, with every access legal and inside the
footprint `F`: loads in `F.r ∪ F.w`, stores in `F.w`, atomics only as 32-bit
additions to the accumulator cells `Cell` (global, 4-byte). The thread's own
derivation does not see what an atomic returns (it must hold for every
value) nor the cell it adds to; `d` records, as a ghost, how much it has
added to each cell so far. `J` is where the phase ends: a `bar.sync` or
`ret`. `Run` is what the phase theorem (Ptx/Logic/PhaseSound.lean) consumes.

`Run.frame`: a derivation stays valid when memory outside the footprint
changes, which is how one thread's proof survives the other threads.
`Run.step` inverts one step of the grid against it.
-/
import Ptx.Logic.Hoare

namespace Ptx

/-- A location a thread can name: a space and an address in it. -/
abbrev Loc := Sp × Addr

def Heap.get (h : Heap) (x : Loc) : BitVec 8 := h.at x.1 x.2

@[simp] theorem Heap.get_global (h : Heap) (a : Addr) : h.get (.global, a) = h.g a := rfl
@[simp] theorem Heap.get_shared (h : Heap) (a : Addr) : h.get (.shared, a) = h.s a := rfl

/-- What one thread may touch in one phase: `r` it may only read, `w` it may
read and write. -/
structure Foot where
  r : Loc → Prop
  w : Loc → Prop

def Foot.touches (F : Foot) (x : Loc) : Prop := F.r x ∨ F.w x

/-- Contributions to the accumulator cells, by cell address. -/
abbrev Ghost := Addr → BitVec 32

def Ghost.add (d : Ghost) (a : Addr) (δ : BitVec 32) : Ghost := fun x => if x = a then d x + δ else d x

section
variable (K : Kernel) (al : Sp → List Region) (c : Ctx) (F : Foot) (Cell : Addr → Prop)

inductive Run (J : TState → Heap → Ghost → Prop) : Nat → TState → Heap → Ghost → Prop
  | stop {n s h d} : J s h d → Run J n s h d
  | next {n s s' h d} : action K c s = .next s' → Run J n s' h d → Run J (n + 1) s h d
  | load {n s h d sp a sz k} : action K c s = .load sp a sz k → accessOk (al sp) a sz = true →
      (∀ x, covers a sz.bytes x → F.touches (sp, x)) →
      Run J n (k (rd (h.at sp) a sz)) h d → Run J (n + 1) s h d
  | store {n s h d sp a sz v s'} : action K c s = .store sp a sz v s' → accessOk (al sp) a sz = true →
      (∀ x, covers a sz.bytes x → F.w (sp, x)) →
      Run J n s' (h.set sp (wr (h.at sp) a sz v)) d → Run J (n + 1) s h d
  | atom {n s h d a f k} (δ : BitVec 32) : action K c s = .atom .global a .b4 f k →
      accessOk (al .global) a .b4 = true → Cell a →
      (∀ w : BitVec 32, lo32 (f (ext32 w)) = w + δ) →
      (∀ v, Run J n (k v) h (d.add a δ)) → Run J (n + 1) s h d

end

section
variable {K : Kernel} {al : Sp → List Region} {c : Ctx} {F : Foot} {Cell : Addr → Prop}
  {J : TState → Heap → Ghost → Prop}

theorem Run.mono_index {n m s h d} (hr : Run K al c F Cell J n s h d) (hle : n ≤ m) :
    Run K al c F Cell J m s h d := by
  induction hr generalizing m with
  | stop hj => exact .stop hj
  | next ha _ ih =>
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact .next ha (ih (by omega))
  | load ha hok hf _ ih =>
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact .load ha hok hf (ih (by omega))
  | store ha hok hf _ ih =>
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact .store ha hok hf (ih (by omega))
  | atom δ ha hok hacc hf _ ih =>
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact .atom δ ha hok hacc hf fun v => ih v (by omega)

/-- Two heaps agree on the locations `P`. -/
def Heap.Agree (P : Loc → Prop) (h h' : Heap) : Prop := ∀ x, P x → h.get x = h'.get x

theorem Heap.Agree.at {P : Loc → Prop} {h h' : Heap} (hg : Heap.Agree P h h') {sp : Sp} {x : Addr}
    (hx : P (sp, x)) : h.at sp x = h'.at sp x := hg (sp, x) hx

theorem Heap.Agree.wr {P : Loc → Prop} {h h' : Heap} (hg : Heap.Agree P h h') (sp : Sp) (a : Addr)
    (sz : Size) (v : Val) :
    Heap.Agree P (h.set sp (Ptx.wr (h.at sp) a sz v)) (h'.set sp (Ptx.wr (h'.at sp) a sz v)) := by
  rintro ⟨sp', x⟩ hx
  have base := hg (sp', x) hx
  cases sp <;> cases sp' <;> simp only [Heap.get, Heap.at, Heap.set] at base ⊢
  · by_cases hc : covers a sz.bytes x
    · rw [wr_inside hc, wr_inside hc]
    · rw [wr_outside hc, wr_outside hc]; exact base
  · exact base
  · exact base
  · by_cases hc : covers a sz.bytes x
    · rw [wr_inside hc, wr_inside hc]
    · rw [wr_outside hc, wr_outside hc]; exact base

/-- A derivation holds of every heap that agrees with its own on the
footprint, provided the postcondition does too. -/
theorem Run.frame (hJ : ∀ s h h' d, J s h d → Heap.Agree F.touches h h' → J s h' d) :
    ∀ {n s h d}, Run K al c F Cell J n s h d → ∀ {h'}, Heap.Agree F.touches h h' →
      Run K al c F Cell J n s h' d := by
  intro n s h d hr
  induction hr with
  | stop hj => intro h' hg; exact .stop (hJ _ _ _ _ hj hg)
  | next ha _ ih => intro h' hg; exact .next ha (ih hg)
  | @load n s h d sp a sz k ha hok hf _ ih =>
    intro h' hg
    have : rd (h.at sp) a sz = rd (h'.at sp) a sz := rd_congr fun x hx => hg.at (hf x hx)
    exact .load ha hok hf (this ▸ ih hg)
  | @store n s h d sp a sz v s' ha hok hf _ ih =>
    intro h' hg
    exact .store ha hok hf (ih (hg.wr sp a sz v))
  | atom δ ha hok hacc hf _ ih => intro h' hg; exact .atom δ ha hok hacc hf fun v => ih v hg

/-- A derivation never faults: the next step of a thread it covers is legal,
or the thread waits or has finished in a state satisfying `J`. -/
theorem Run.not_fault (hJ : ∀ s h d, J s h d → action K c s = .bar ∨ action K c s = .done)
    {n s h d} (hr : Run K al c F Cell J n s h d) : tstep K al c s h ≠ .fault := by
  cases hr with
  | stop hj => rcases hJ _ _ _ hj with h | h <;> simp [tstep, h]
  | next ha => simp [tstep, ha]
  | load ha hok => simp [tstep, ha, hok]
  | store ha hok => simp [tstep, ha, hok]
  | atom δ ha hok => simp [tstep, ha, hok]

/-- A thread that waits or has finished is at the end of its derivation. -/
theorem Run.stop_of {n s h d} (hr : Run K al c F Cell J n s h d)
    (ha : action K c s = .bar ∨ action K c s = .done) : J s h d := by
  cases hr with
  | stop hj => exact hj
  | next ha' => rcases ha with h | h <;> rw [h] at ha' <;> cases ha'
  | load ha' => rcases ha with h | h <;> rw [h] at ha' <;> cases ha'
  | store ha' => rcases ha with h | h <;> rw [h] at ha' <;> cases ha'
  | atom δ ha' => rcases ha with h | h <;> rw [h] at ha' <;> cases ha'

theorem action_of_wait {s h} (hw : tstep K al c s h = .wait) : action K c s = .bar := by
  unfold tstep at hw; split at hw <;> (try split at hw) <;> simp_all

theorem action_of_halted {s h} (hw : tstep K al c s h = .halted) : action K c s = .done := by
  unfold tstep at hw; split at hw <;> (try split at hw) <;> simp_all

/-- The access a derivation is about to make is inside its footprint. -/
theorem Run.pending {n s h d} (hr : Run K al c F Cell J n s h d)
    (hJ : ∀ s h d, J s h d → action K c s = .bar ∨ action K c s = .done) {x : Ptx.Acc}
    (hx : (action K c s).acc = some x) :
    (x.kind = .read ∧ ∀ b, covers x.a x.sz.bytes b → F.touches (x.sp, b)) ∨
    (x.kind = .write ∧ ∀ b, covers x.a x.sz.bytes b → F.w (x.sp, b)) ∨
    (x.kind = .atomic ∧ x.sp = .global ∧ x.sz = .b4 ∧ Cell x.a) := by
  cases hr with
  | stop hj => rcases hJ _ _ _ hj with h | h <;> rw [h] at hx <;> cases hx
  | next ha => rw [ha] at hx; cases hx
  | load ha _ hf => rw [ha] at hx; cases hx; exact .inl ⟨rfl, hf⟩
  | store ha _ hf => rw [ha] at hx; cases hx; exact .inr (.inl ⟨rfl, hf⟩)
  | atom δ ha _ hacc => rw [ha] at hx; cases hx; exact .inr (.inr ⟨rfl, rfl, rfl, hacc⟩)

/-- The cells are outside the footprint. -/
def CellsOut (F : Foot) (Cell : Addr → Prop) : Prop :=
  ∀ a, Cell a → ∀ y, covers a 4 y → ¬ F.touches (.global, y)

/-- What one step does to the heap: nothing, a store inside `F.w`, or the
addition of `δ` to an accumulator cell (recorded in the ghost). -/
inductive Effect (F : Foot) (Cell : Addr → Prop) (h : Heap) (d : Ghost) : Heap → Ghost → Prop
  | none : Effect F Cell h d h d
  | store {sp a sz v} : (∀ x, covers a sz.bytes x → F.w (sp, x)) →
      Effect F Cell h d (h.set sp (wr (h.at sp) a sz v)) d
  | atom {a g} (δ : BitVec 32) : Cell a → lo32 g = rd32 h.g a + δ →
      Effect F Cell h d (h.set .global (wr h.g a .b4 g)) (d.add a δ)

theorem rd_b4_ext (m : Mem) (a : Addr) : rd m a .b4 = ext32 (rd32 m a) := rfl

/-- One step of a thread covered by a derivation continues the derivation,
with a smaller index, and changes the heap only as `Effect` allows. -/
theorem Run.step (hJ : ∀ s h d, J s h d → action K c s = .bar ∨ action K c s = .done)
    (hJf : ∀ s h h' d, J s h d → Heap.Agree F.touches h h' → J s h' d) (hco : CellsOut F Cell)
    {n s h d s' h'} (hr : Run K al c F Cell J n s h d) (hs : tstep K al c s h = .ok s' h') :
    ∃ n' < n, ∃ d', Run K al c F Cell J n' s' h' d' ∧ Effect F Cell h d h' d' := by
  cases hr with
  | stop hj => rcases hJ _ _ _ hj with ha | ha <;> simp [tstep, ha] at hs
  | @next n _ s'' _ _ ha hr =>
    simp only [tstep, ha] at hs; cases hs
    exact ⟨n, by omega, d, hr, .none⟩
  | @load n _ _ _ sp a sz k ha hok _ hr =>
    simp only [tstep, ha, hok, ↓reduceIte] at hs; cases hs
    exact ⟨n, by omega, d, hr, .none⟩
  | @store n _ _ _ sp a sz v s'' ha hok hf hr =>
    simp only [tstep, ha, hok, ↓reduceIte] at hs; cases hs
    exact ⟨n, by omega, d, hr, .store hf⟩
  | @atom n _ _ _ a f k δ ha hok hacc hf hr =>
    simp only [tstep, ha, hok, ↓reduceIte] at hs; cases hs
    refine ⟨n, by omega, d.add a δ, ?_, .atom δ hacc ?_⟩
    · refine (hr _).frame hJf ?_
      rintro ⟨sp, x⟩ hx
      cases sp with
      | shared => rfl
      | global =>
        show h.g x = wr h.g a .b4 _ x
        rw [wr_outside]
        intro hc; exact hco a hacc x hc hx
    · rw [rd_b4_ext]; exact hf _

end

end Ptx
