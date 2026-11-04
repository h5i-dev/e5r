/-
One thread between two barriers: the per-phase logic for kernels with
shared memory, `bar.sync` and atomics.

`Run … F J n s h d` is an inductive derivation that thread state `s`, seeing
heap `h` (global memory and its CTA's shared memory), reaches a state
satisfying `J` in at most `n` steps, with every access legal and inside the
footprint `F`: loads in `F.r ∪ F.w`, stores in `F.w`, atomics only on the
accumulator cells `Cell` (global), and only as an operation of the cells'
algebra `A`: a commutative, associative operation with a unit on values of
one access size (`add`, `min`, `max`, `and`, `or`, `xor` at 32 or 64 bits,
Ptx/Logic/CellAlgs.lean). The thread's own derivation does not see what an
atomic returns (it must hold for every value) nor the cell it combines into;
`d` records, as a ghost, what it has combined into each cell so far. `J` is where the phase ends: a `bar.sync` or
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

/-- The value a load of `sz` bytes can return: the low `sz` bytes. -/
def Size.trunc : Size → Val → Val
  | .b4, v => (v.setWidth 32).setWidth 64
  | .b8, v => v

theorem rd_wr_trunc (m : Mem) (a : Addr) (sz : Size) (v : Val) :
    rd (wr m a sz v) a sz = sz.trunc v := by
  cases sz <;> simp [rd_wr_same, Size.trunc]

theorem trunc_rd (m : Mem) (a : Addr) (sz : Size) : sz.trunc (rd m a sz) = rd m a sz := by
  cases sz
  · simp only [Size.trunc, rd]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    have := (rd32 m a).isLt
    rw [Nat.mod_eq_of_lt (a := (rd32 m a).toNat) (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  · rfl

/-- The algebra of the accumulator cells: the access size, and a
commutative, associative operation with a unit on the values of that size.
An atomic on a cell must combine the old value with some `δ` by `op`. -/
structure CellAlg where
  sz : Size
  op : Val → Val → Val
  e : Val
  comm : ∀ x y, op x y = op y x
  assoc : ∀ x y z, op (op x y) z = op x (op y z)
  unit : ∀ x, sz.trunc x = x → op x e = x
  closed : ∀ x y, sz.trunc (op x y) = op x y
  e_ok : sz.trunc e = e

/-- Contributions to the accumulator cells, by cell address. -/
abbrev Ghost := Addr → Val

/-- Combine `δ` into the contribution to cell `a`. -/
def Ghost.acc (A : CellAlg) (d : Ghost) (a : Addr) (δ : Val) : Ghost :=
  fun x => if x = a then A.op (d x) δ else d x

/-- `g` combines the old value of a cell with `δ`. -/
def Accum (A : CellAlg) (g : Val → Val) (δ : Val) : Prop :=
  ∀ w, A.sz.trunc w = w → A.sz.trunc (g w) = A.op w δ

section
variable (K : Kernel) (al : Sp → List Region) (c : Ctx) (F : Foot) (Cell : Addr → Prop) (A : CellAlg)

inductive Run (J : TState → Heap → Ghost → Prop) : Nat → TState → Heap → Ghost → Prop
  | stop {n s h d} : J s h d → Run J n s h d
  | next {n s s' h d} : action K c s = .next s' → Run J n s' h d → Run J (n + 1) s h d
  | load {n s h d sp a sz k} : action K c s = .load sp a sz k → accessOk (al sp) a sz = true →
      (∀ x, covers a sz.bytes x → F.touches (sp, x)) →
      Run J n (k (rd (h.at sp) a sz)) h d → Run J (n + 1) s h d
  | store {n s h d sp a sz v s'} : action K c s = .store sp a sz v s' → accessOk (al sp) a sz = true →
      (∀ x, covers a sz.bytes x → F.w (sp, x)) →
      Run J n s' (h.set sp (wr (h.at sp) a sz v)) d → Run J (n + 1) s h d
  | atom {n s h d a f k} (δ : Val) : action K c s = .atom .global a A.sz f k →
      accessOk (al .global) a A.sz = true → Cell a → Accum A f δ →
      (∀ v, Run J n (k v) h (d.acc A a δ)) → Run J (n + 1) s h d

end

section
variable {K : Kernel} {al : Sp → List Region} {c : Ctx} {F : Foot} {Cell : Addr → Prop}
  {A : CellAlg} {J : TState → Heap → Ghost → Prop}

theorem Run.mono_index {n m s h d} (hr : Run K al c F Cell A J n s h d) (hle : n ≤ m) :
    Run K al c F Cell A J m s h d := by
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
    ∀ {n s h d}, Run K al c F Cell A J n s h d → ∀ {h'}, Heap.Agree F.touches h h' →
      Run K al c F Cell A J n s h' d := by
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
    {n s h d} (hr : Run K al c F Cell A J n s h d) : tstep K al c s h ≠ .fault := by
  cases hr with
  | stop hj => rcases hJ _ _ _ hj with h | h <;> simp [tstep, h]
  | next ha => simp [tstep, ha]
  | load ha hok => simp [tstep, ha, hok]
  | store ha hok => simp [tstep, ha, hok]
  | atom δ ha hok => simp [tstep, ha, hok]

/-- A thread that waits or has finished is at the end of its derivation. -/
theorem Run.stop_of {n s h d} (hr : Run K al c F Cell A J n s h d)
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
theorem Run.pending {n s h d} (hr : Run K al c F Cell A J n s h d)
    (hJ : ∀ s h d, J s h d → action K c s = .bar ∨ action K c s = .done) {x : Ptx.Acc}
    (hx : (action K c s).acc = some x) :
    (x.kind = .read ∧ ∀ b, covers x.a x.sz.bytes b → F.touches (x.sp, b)) ∨
    (x.kind = .write ∧ ∀ b, covers x.a x.sz.bytes b → F.w (x.sp, b)) ∨
    (x.kind = .atomic ∧ x.sp = .global ∧ x.sz = A.sz ∧ Cell x.a) := by
  cases hr with
  | stop hj => rcases hJ _ _ _ hj with h | h <;> rw [h] at hx <;> cases hx
  | next ha => rw [ha] at hx; cases hx
  | load ha _ hf => rw [ha] at hx; cases hx; exact .inl ⟨rfl, hf⟩
  | store ha _ hf => rw [ha] at hx; cases hx; exact .inr (.inl ⟨rfl, hf⟩)
  | atom δ ha _ hacc => rw [ha] at hx; cases hx; exact .inr (.inr ⟨rfl, rfl, rfl, hacc⟩)

/-- The cells are outside the footprint. -/
def CellsOut (F : Foot) (Cell : Addr → Prop) (sz : Size) : Prop :=
  ∀ a, Cell a → ∀ y, covers a sz.bytes y → ¬ F.touches (.global, y)

/-- What one step does to the heap: nothing, a store inside `F.w`, or
combining `δ` into an accumulator cell (recorded in the ghost). -/
inductive Effect (F : Foot) (Cell : Addr → Prop) (A : CellAlg) (h : Heap) (d : Ghost) :
    Heap → Ghost → Prop
  | none : Effect F Cell A h d h d
  | store {sp a sz v} : (∀ x, covers a sz.bytes x → F.w (sp, x)) →
      Effect F Cell A h d (h.set sp (wr (h.at sp) a sz v)) d
  | atom {a g} (δ : Val) : Cell a → A.sz.trunc g = A.op (rd h.g a A.sz) δ →
      Effect F Cell A h d (h.set .global (wr h.g a A.sz g)) (d.acc A a δ)

theorem rd_b4_ext (m : Mem) (a : Addr) : rd m a .b4 = ext32 (rd32 m a) := rfl

/-- One step of a thread covered by a derivation continues the derivation,
with a smaller index, and changes the heap only as `Effect` allows. -/
theorem Run.step (hJ : ∀ s h d, J s h d → action K c s = .bar ∨ action K c s = .done)
    (hJf : ∀ s h h' d, J s h d → Heap.Agree F.touches h h' → J s h' d) (hco : CellsOut F Cell A.sz)
    {n s h d s' h'} (hr : Run K al c F Cell A J n s h d) (hs : tstep K al c s h = .ok s' h') :
    ∃ n' < n, ∃ d', Run K al c F Cell A J n' s' h' d' ∧ Effect F Cell A h d h' d' := by
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
    refine ⟨n, by omega, d.acc A a δ, ?_, .atom δ hacc ?_⟩
    · refine (hr _).frame hJf ?_
      rintro ⟨sp, x⟩ hx
      cases sp with
      | shared => rfl
      | global =>
        show h.g x = wr h.g a A.sz _ x
        rw [wr_outside]
        intro hc; exact hco a hacc x hc hx
    · exact hf _ (trunc_rd _ _ _)

end

end Ptx
