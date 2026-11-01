/-
From per-thread, per-phase proofs to the whole grid, for kernels with
shared memory, `bar.sync` and atomic accumulation: the M4 composition
theorem, `phase_sound`.

A `Phased` description of a launch says, for each CTA `b`, how many phases
`P b` its threads run (phase `k` ends at the `k`-th `bar.sync`, the last one
at `ret`), and for each thread `t` and phase `k`:

* `F t k`, what it may touch (read-only `r`, read-write `w`), over global and
  shared locations;
* `T t k`, what its registers and pc satisfy when the phase starts, and
  `N t k`, a bound on the steps it takes in the phase;
* `M b k`, CTA `b`'s view of memory when phase `k` starts (`M b (P b)` is
  the view at the end);
* `bpc b k`, the `bar.sync` that ends phase `k`;
* `Δ t k`, what it adds to each accumulator cell (`Cell`) in the phase.

The hypotheses (`Phased.Ok`) are per thread and per phase: from every state
in `T t k`, with memory `M b k`, the thread reaches its barrier (with
`T t (k+1)` after it) or `ret`, inside `F t k`, in at most `N t k` steps,
leaving `M b (k+1)` on what it wrote and having added `Δ t k` to the cells
(`Run`, Ptx/Logic/Phases.lean); `M b (k+1)` equals `M b k` where no thread of
`b` wrote in phase `k`; in one phase of one CTA no thread writes what another
touches; across CTAs no thread writes a global byte another touches in any
phase; the cells are touched only by atomic additions.

`phase_sound` concludes, for every execution of the grid: no fault (bounds,
alignment, a diverged barrier), progress, a bound on the length of every
execution, phase-relative race freedom (`RaceFree`), and when all threads are
done: every global byte a thread wrote holds what `M b (P b)` says, every
byte nobody wrote and no cell covers is unchanged, and every cell holds its
initial value plus the sum of all contributions.

The proof keeps, for every reachable configuration, a remaining derivation
for every thread against the actual memory (transported with `Run.frame`
when other threads write elsewhere), the agreement of each CTA's view with
`M b k` on what it touches and nobody has written yet in the phase, and the
cells as initial value plus contributions so far. At a barrier every thread
of the CTA is at the end of its derivation; the next phase's derivation is
moved from `M b (k+1)` onto the actual memory.
-/
import Ptx.Logic.Phases
import Ptx.Logic.Launch1D

namespace Ptx

/-! ## Sums and thread lists -/

/-- `f 0 + … + f (k-1)`. -/
def accUpTo (f : Nat → BitVec 32) : Nat → BitVec 32
  | 0 => 0
  | k + 1 => accUpTo f k + f k

/-- The sum of `f t` over a list of threads, modulo `2^32`. -/
def tsum (l : List Tid) (f : Tid → BitVec 32) : BitVec 32 := (l.map f).foldr (· + ·) 0

theorem tsum_congr {l : List Tid} {f g : Tid → BitVec 32} (h : ∀ t ∈ l, f t = g t) :
    tsum l f = tsum l g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [tsum, List.map_cons, List.foldr_cons] at ih ⊢
    rw [h a (by simp), ih fun t ht => h t (by simp [ht])]

theorem tsum_zero (l : List Tid) : tsum l (fun _ => 0) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [tsum, List.map_cons, List.foldr_cons] at ih ⊢; rw [ih]; rfl

/-- Changing one member of a list without duplicates by `δ` changes the sum
by `δ`. -/
theorem tsum_update {l : List Tid} (hl : l.Nodup) {t : Tid} (ht : t ∈ l) {f g : Tid → BitVec 32}
    {δ : BitVec 32} (hg : ∀ u ∈ l, u ≠ t → g u = f u) (hgt : g t = f t + δ) :
    tsum l g = tsum l f + δ := by
  induction l with
  | nil => simp at ht
  | cons a l ih =>
    simp only [tsum, List.map_cons, List.foldr_cons] at ih ⊢
    rw [List.nodup_cons] at hl
    by_cases hta : t = a
    · subst hta
      have : tsum l g = tsum l f := tsum_congr fun u hu => hg u (by simp [hu]) fun h => hl.1 (h ▸ hu)
      simp only [tsum] at this
      rw [this, hgt, BitVec.add_assoc, BitVec.add_comm δ, ← BitVec.add_assoc]
    · have hm : t ∈ l := by simp [hta] at ht; exact ht
      rw [ih hl.2 hm (fun u hu hut => hg u (by simp [hu]) hut), hg a (by simp) (Ne.symm hta),
        BitVec.add_assoc]

theorem nodup_map_of_inj {α β : Type} {l : List α} {f : α → β} (hl : l.Nodup)
    (hf : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    refine ⟨fun b hb hab => hl.1 ?_, ih hl.2 fun x hx y hy => hf x (by simp [hx]) y (by simp [hy])⟩
    rw [hf b (by simp [hb]) a (by simp) hab] at hb; exact hb

theorem nodup_flatMap_of {α β : Type} {l : List α} {f : α → List β} (hl : l.Nodup)
    (hf : ∀ a ∈ l, (f a).Nodup) (hd : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → ∀ x ∈ f a, x ∉ f b) :
    (l.flatMap f).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨hf a (by simp), ih hl.2 (fun x hx => hf x (by simp [hx]))
      (fun x hx y hy => hd x (by simp [hx]) y (by simp [hy])), ?_⟩
    intro x hx y hy hxy
    subst hxy
    obtain ⟨b, hb, hyb⟩ := List.mem_flatMap.mp hy
    exact hd a (by simp) b (by simp [hb]) (fun h => hl.1 (h ▸ hb)) x hx hyb

theorem range32_nodup (n : BitVec 32) : (range32 n).Nodup := by
  apply nodup_map_of_inj List.nodup_range
  intro a ha b hb h
  simp only [List.mem_range] at ha hb
  have hab := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at hab
  have := n.isLt
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hab

theorem dims_nodup (v : Dim3) : (dims v).Nodup := by
  unfold dims
  apply nodup_flatMap_of (range32_nodup _)
  · intro z _
    apply nodup_flatMap_of (range32_nodup _)
    · intro y _
      exact nodup_map_of_inj (range32_nodup _) fun a _ b _ h => by cases h; rfl
    · intro a _ b _ hab x hx hx'
      simp only [List.mem_map] at hx hx'
      obtain ⟨_, _, rfl⟩ := hx; obtain ⟨_, _, h⟩ := hx'
      cases h; exact hab rfl
  · intro a _ b _ hab x hx hx'
    simp only [List.mem_flatMap, List.mem_map] at hx hx'
    obtain ⟨_, _, _, _, rfl⟩ := hx; obtain ⟨_, _, _, _, h⟩ := hx'
    cases h; exact hab rfl

theorem threads_nodup (L : Launch) : L.threads.Nodup := by
  unfold Launch.threads
  apply nodup_flatMap_of (dims_nodup _)
  · intro c _
    exact nodup_map_of_inj (dims_nodup _) fun a _ b _ h => by cases h; rfl
  · intro a _ b _ hab x hx hx'
    simp only [List.mem_map] at hx hx'
    obtain ⟨_, _, rfl⟩ := hx; obtain ⟨_, _, h⟩ := hx'
    cases h; exact hab rfl

/-! ## The description of a phased launch -/

structure Phased where
  P : Dim3 → Nat
  F : Tid → Nat → Foot
  T : Tid → Nat → TState → Prop
  N : Tid → Nat → Nat
  M : Dim3 → Nat → Heap
  bpc : Dim3 → Nat → Nat
  Cell : Addr → Prop
  Δ : Tid → Nat → Ghost

namespace Phased
variable (K : Kernel) (L : Launch) (S : Phased)

/-- Where phase `k` of thread `t` ends: it has added `Δ t k`, what it wrote
holds what `M` says after the phase, and it waits at the phase's barrier
(with `T t (k+1)` after it) or, in the last phase, has finished. -/
def J (t : Tid) (k : Nat) (s : TState) (h : Heap) (d : Ghost) : Prop :=
  d = S.Δ t k ∧ (∀ x, (S.F t k).w x → h.get x = (S.M t.ctaid (k + 1)).get x) ∧
  (if k + 1 < S.P t.ctaid then
    action K (L.ctx t) s = .bar ∧ s.pc = S.bpc t.ctaid k ∧ S.T t (k + 1) s.skip
  else action K (L.ctx t) s = .done)

/-- Some thread of CTA `b` touches `x` in some phase. -/
def Tch (b : Dim3) (x : Loc) : Prop :=
  ∃ t ∈ L.threads, t.ctaid = b ∧ ∃ k < S.P b, (S.F t k).touches x

/-- The hypotheses of `phase_sound`. -/
structure Ok (r0 : Tid → String → Val) (p0 : Tid → String → Bool) (m0 : Mem) (sh0 : Dim3 → Mem) :
    Prop where
  pos : ∀ t ∈ L.threads, 0 < S.P t.ctaid
  init : ∀ t ∈ L.threads, S.T t 0 ⟨0, r0 t, p0 t⟩
  initMem : ∀ b x, S.Tch L b x → (S.M b 0).get x = (Heap.mk m0 (sh0 b)).get x
  phase : ∀ t ∈ L.threads, ∀ k < S.P t.ctaid, ∀ s, S.T t k s →
    Run K (L.allocs K) (L.ctx t) (S.F t k) S.Cell (S.J K L t k) (S.N t k) s (S.M t.ctaid k)
      (fun _ => 0)
  compose : ∀ b k x, (∃ t ∈ L.threads, t.ctaid = b) → k < S.P b →
    (∀ t ∈ L.threads, t.ctaid = b → ¬ (S.F t k).w x) → (S.M b (k + 1)).get x = (S.M b k).get x
  sameCta : ∀ t ∈ L.threads, ∀ u ∈ L.threads, t ≠ u → t.ctaid = u.ctaid → ∀ k x,
    (S.F t k).w x → ¬ (S.F u k).touches x
  crossCta : ∀ t ∈ L.threads, ∀ u ∈ L.threads, t.ctaid ≠ u.ctaid → ∀ k j a,
    (S.F t k).w (.global, a) → ¬ (S.F u j).touches (.global, a)
  cellsOut : ∀ t ∈ L.threads, ∀ k, CellsOut (S.F t k) S.Cell
  cellsDisj : ∀ a b, S.Cell a → S.Cell b → a ≠ b → ∀ y, covers a 4 y → ¬ covers b 4 y

/-- What `phase_sound` proves about every execution from `c₀`. -/
structure Result (c₀ : Cfg) (m0 : Mem) : Prop where
  noFault : ∀ c, Reach K L c₀ c → ¬ Faults K L c
  progress : ∀ c, Reach K L c₀ c → Done K L c ∨ ∃ c', Step K L c c'
  bounded : ∃ bound, ∀ j c, Steps K L j c₀ c → j ≤ bound
  raceFree : RaceFree K L c₀
  final : ∀ c, Reach K L c₀ c → Done K L c →
    (∀ t ∈ L.threads, ∀ k < S.P t.ctaid, ∀ a, (S.F t k).w (.global, a) →
      c.mem a = (S.M t.ctaid (S.P t.ctaid)).g a) ∧
    (∀ a, (∀ t ∈ L.threads, ∀ k < S.P t.ctaid, ¬ (S.F t k).w (.global, a)) →
      (∀ b, S.Cell b → ¬ covers b 4 a) → c.mem a = m0 a) ∧
    (∀ b, S.Cell b → rd32 c.mem b =
      rd32 m0 b + tsum L.threads fun t => accUpTo (fun k => S.Δ t k b) (S.P t.ctaid))

/-- The steps still allowed after phase `p` of thread `t`. -/
def fut (t : Tid) (p : Nat) : Nat :=
  ((List.range (S.P t.ctaid - (p + 1))).map fun i => S.N t (p + 1 + i) + 1).sum

theorem fut_succ {t : Tid} {p : Nat} (h : p + 1 < S.P t.ctaid) :
    S.fut t p = S.N t (p + 1) + 1 + S.fut t (p + 1) := by
  unfold fut
  rw [show S.P t.ctaid - (p + 1) = (S.P t.ctaid - (p + 1 + 1)) + 1 by omega, List.range_succ_eq_map]
  simp only [List.map_cons, List.sum_cons, List.map_map, Nat.add_zero]
  congr 2
  congr 1
  funext i; simp only [Function.comp, Nat.succ_eq_add_one]; congr 2; omega

/-- The invariant of reachable configurations: remaining derivations `n`,
ghosts `d`. -/
structure Inv (m0 : Mem) (c : Cfg) (n : Tid → Nat) (d : Tid → Ghost) : Prop where
  ph : ∀ t ∈ L.threads, c.ph t.ctaid < S.P t.ctaid
  run : ∀ t ∈ L.threads, Run K (L.allocs K) (L.ctx t) (S.F t (c.ph t.ctaid)) S.Cell
    (S.J K L t (c.ph t.ctaid)) (n t) (c.ts t) (c.heap t.ctaid) (d t)
  mem : ∀ b x, S.Tch L b x → (∀ t ∈ L.threads, t.ctaid = b → ¬ (S.F t (c.ph b)).w x) →
    (c.heap b).get x = (S.M b (c.ph b)).get x
  untouched : ∀ a, (∀ t ∈ L.threads, ∀ k < S.P t.ctaid, ¬ (S.F t k).w (.global, a)) →
    (∀ b, S.Cell b → ¬ covers b 4 a) → c.mem a = m0 a
  cells : ∀ b, S.Cell b → rd32 c.mem b =
    rd32 m0 b + tsum L.threads fun t => accUpTo (fun k => S.Δ t k b) (c.ph t.ctaid) + d t b

def μ (c : Cfg) (n : Tid → Nat) : Nat := (L.threads.map fun t => n t + S.fut t (c.ph t.ctaid)).sum

end Phased

/-! ## The proof -/

namespace Phased
variable {K : Kernel} {L : Launch} {S : Phased} {r0 : Tid → String → Val} {p0 : Tid → String → Bool}
  {m0 : Mem} {sh0 : Dim3 → Mem}

theorem J_end {t k s h d} (hj : S.J K L t k s h d) :
    action K (L.ctx t) s = .bar ∨ action K (L.ctx t) s = .done := by
  obtain ⟨-, -, h3⟩ := hj
  split at h3
  · exact .inl h3.1
  · exact .inr h3

theorem J_frame {t k s h h' d} (hj : S.J K L t k s h d) (hg : Heap.Agree (S.F t k).touches h h') :
    S.J K L t k s h' d := by
  obtain ⟨h1, h2, h3⟩ := hj
  exact ⟨h1, fun x hx => by rw [← hg x (.inr hx)]; exact h2 x hx, h3⟩

theorem frameJ {t k n s h h' d}
    (hr : Run K (L.allocs K) (L.ctx t) (S.F t k) S.Cell (S.J K L t k) n s h d)
    (hg : Heap.Agree (S.F t k).touches h h') :
    Run K (L.allocs K) (L.ctx t) (S.F t k) S.Cell (S.J K L t k) n s h' d :=
  Run.frame (J := S.J K L t k) (fun _ _ _ _ hj hg => J_frame hj hg) hr hg

theorem stepJ {t k n s h d s' h'}
    (hr : Run K (L.allocs K) (L.ctx t) (S.F t k) S.Cell (S.J K L t k) n s h d)
    (hco : CellsOut (S.F t k) S.Cell) (hs : tstep K (L.allocs K) (L.ctx t) s h = .ok s' h') :
    ∃ n' < n, ∃ d', Run K (L.allocs K) (L.ctx t) (S.F t k) S.Cell (S.J K L t k) n' s' h' d' ∧
      Effect (S.F t k) S.Cell h d h' d' :=
  Run.step (J := S.J K L t k) (fun _ _ _ hj => J_end hj) (fun _ _ _ _ hj hg => J_frame hj hg) hco hr hs

theorem notFaultJ {t k n s h d}
    (hr : Run K (L.allocs K) (L.ctx t) (S.F t k) S.Cell (S.J K L t k) n s h d) :
    tstep K (L.allocs K) (L.ctx t) s h ≠ .fault :=
  Run.not_fault (J := S.J K L t k) (fun _ _ _ hj => J_end hj) hr

theorem pendJ {t k n s h d}
    (hr : Run K (L.allocs K) (L.ctx t) (S.F t k) S.Cell (S.J K L t k) n s h d) {x : Ptx.Acc}
    (hx : (action K (L.ctx t) s).acc = some x) :
    (x.kind = .read ∧ ∀ b, covers x.a x.sz.bytes b → (S.F t k).touches (x.sp, b)) ∨
    (x.kind = .write ∧ ∀ b, covers x.a x.sz.bytes b → (S.F t k).w (x.sp, b)) ∨
    (x.kind = .atomic ∧ x.sp = .global ∧ x.sz = .b4 ∧ S.Cell x.a) :=
  Run.pending (J := S.J K L t k) hr (fun _ _ _ hj => J_end hj) hx

theorem J_wait {t k s h d} (hj : S.J K L t k s h d) (hb : action K (L.ctx t) s = .bar) :
    k + 1 < S.P t.ctaid ∧ s.pc = S.bpc t.ctaid k ∧ S.T t (k + 1) s.skip := by
  obtain ⟨-, -, h3⟩ := hj
  split at h3
  · next hk => exact ⟨hk, h3.2⟩
  · rw [hb] at h3; cases h3

theorem J_done {t k s h d} (hj : S.J K L t k s h d) (hb : action K (L.ctx t) s = .done) :
    ¬ k + 1 < S.P t.ctaid := by
  obtain ⟨-, -, h3⟩ := hj
  split at h3
  · rw [hb] at h3; cases h3.1
  · assumption

variable (hS : S.Ok K L r0 p0 m0 sh0)
include hS

theorem cellsOut' {a y} (ha : S.Cell a) (hy : covers a 4 y) :
    ∀ t ∈ L.threads, ∀ k, ¬ (S.F t k).touches (.global, y) :=
  fun t ht k => hS.cellsOut t ht k a ha y hy

/-- When every thread of CTA `b` waits at its barrier, the CTA's view agrees
with `M b (k+1)` on everything the CTA touches. -/
theorem agree_after {c : Cfg} {n d} (hI : S.Inv K L m0 c n d) {b : Dim3}
    (hall : ∀ u ∈ L.threads, u.ctaid = b →
      action K (L.ctx u) (c.ts u) = .bar ∨ action K (L.ctx u) (c.ts u) = .done)
    {x : Loc} (hx : S.Tch L b x) :
    (c.heap b).get x = (S.M b (c.ph b + 1)).get x := by
  classical
  by_cases hW : ∃ u ∈ L.threads, u.ctaid = b ∧ (S.F u (c.ph b)).w x
  · obtain ⟨u, hu, rfl, hwx⟩ := hW
    have hj := (hI.run u hu).stop_of (hall u hu rfl)
    exact hj.2.1 x hwx
  · have hn : ∀ u ∈ L.threads, u.ctaid = b → ¬ (S.F u (c.ph b)).w x :=
      fun u hu hb hw => hW ⟨u, hu, hb, hw⟩
    obtain ⟨t, ht, rfl, hk⟩ := hx
    rw [hI.mem _ x ⟨t, ht, rfl, hk⟩ hn, hS.compose _ _ x ⟨t, ht, rfl⟩ (hI.ph t ht) hn]

/-- The derivation of a thread after its CTA passes a barrier, against the
actual memory. -/
theorem next_phase {c : Cfg} {n d} (hI : S.Inv K L m0 c n d) {t : Tid} (ht : t ∈ L.threads)
    (hall : ∀ u ∈ L.threads, u.ctaid = t.ctaid → c.res K L u = .wait) :
    Run K (L.allocs K) (L.ctx t) (S.F t (c.ph t.ctaid + 1)) S.Cell (S.J K L t (c.ph t.ctaid + 1))
      (S.N t (c.ph t.ctaid + 1)) (c.ts t).skip (c.heap t.ctaid) (fun _ => 0) ∧
    c.ph t.ctaid + 1 < S.P t.ctaid ∧ (c.ts t).pc = S.bpc t.ctaid (c.ph t.ctaid) ∧
    d t = S.Δ t (c.ph t.ctaid) := by
  have hb := action_of_wait (hall t ht rfl)
  have hj := (hI.run t ht).stop_of (.inl hb)
  obtain ⟨hk, hpc, hT⟩ := J_wait hj hb
  refine ⟨?_, hk, hpc, hj.1⟩
  refine frameJ (hS.phase t ht _ hk _ hT) ?_
  intro x hx
  exact (agree_after hS hI (fun u hu hb => .inl (action_of_wait (hall u hu hb)))
    ⟨t, ht, rfl, _, hk, hx⟩).symm

omit hS in
/-- A waiting thread and a finished one are never in the same CTA. -/
theorem wait_halted {c : Cfg} {n d} (hI : S.Inv K L m0 c n d) {t u : Tid} (ht : t ∈ L.threads)
    (hu : u ∈ L.threads) (hc : t.ctaid = u.ctaid) (hw : c.res K L t = .wait)
    (hh : c.res K L u = .halted) : False := by
  have hb := action_of_wait hw
  have hd := action_of_halted hh
  have := (J_wait ((hI.run t ht).stop_of (.inl hb)) hb).1
  have := J_done ((hI.run u hu).stop_of (.inr hd)) hd
  rw [hc] at *; contradiction

omit hS in
/-- Two waiting threads of one CTA wait at the same `bar.sync`. -/
theorem wait_pc {c : Cfg} {n d} (hI : S.Inv K L m0 c n d) {t u : Tid} (ht : t ∈ L.threads)
    (hu : u ∈ L.threads) (hc : t.ctaid = u.ctaid) (hw : c.res K L t = .wait)
    (hw' : c.res K L u = .wait) : (c.ts t).pc = (c.ts u).pc := by
  have hb := action_of_wait hw
  have hb' := action_of_wait hw'
  rw [(J_wait ((hI.run t ht).stop_of (.inl hb)) hb).2.1,
    (J_wait ((hI.run u hu).stop_of (.inl hb')) hb').2.1, hc]

theorem inv_init : S.Inv K L m0 (Cfg.init r0 p0 m0 sh0) (fun t => S.N t 0) (fun _ _ => 0) := by
  refine ⟨fun t ht => hS.pos t ht, ?_, ?_, fun _ _ _ => rfl, ?_⟩
  · intro t ht
    refine frameJ (hS.phase t ht 0 (hS.pos t ht) _ (hS.init t ht)) ?_
    intro x hx
    exact hS.initMem _ x ⟨t, ht, rfl, 0, hS.pos t ht, hx⟩
  · intro b x hx _; exact (hS.initMem b x hx).symm
  · intro b _
    show rd32 m0 b = rd32 m0 b + tsum L.threads fun t => accUpTo _ 0 + 0
    rw [tsum_congr (g := fun _ => 0) (fun t _ => by simp [accUpTo]), tsum_zero]; simp

omit hS in
/-- What a store or an atomic of thread `t` leaves unchanged in CTA `b'`'s
view. -/
theorem write_get {c : Cfg} {t : Tid} {s' : TState} {sp : Sp} {a : Addr} {sz : Size} {v : Val}
    {b' : Dim3} {x : Loc} (hx : ¬ (x.1 = sp ∧ (sp = .shared → b' = t.ctaid) ∧ covers a sz.bytes x.2)) :
    ((c.write t s' ((c.heap t.ctaid).set sp (wr ((c.heap t.ctaid).at sp) a sz v))).heap b').get x =
      (c.heap b').get x := by
  obtain ⟨sp', y⟩ := x
  simp only [not_and] at hx
  cases sp' <;> cases sp
  · show wr c.mem a sz v y = c.mem y
    exact wr_outside (hx rfl nofun)
  · rfl
  · show updC c.sh t.ctaid (c.sh t.ctaid) b' y = c.sh b' y
    unfold updC; split <;> simp_all
  · show updC c.sh t.ctaid (wr (c.sh t.ctaid) a sz v) b' y = c.sh b' y
    unfold updC; split
    · next hb => subst hb; exact wr_outside (hx rfl fun _ => rfl)
    · rfl

omit hS in
theorem write_none {c : Cfg} {t : Tid} {s' : TState} (b' : Dim3) :
    (c.write t s' (c.heap t.ctaid)).heap b' = c.heap b' := by
  simp only [Cfg.write, Cfg.heap, updC]
  by_cases hb : b' = t.ctaid
  · subst hb; simp
  · simp [hb]

omit hS in
theorem write_self {c : Cfg} {t : Tid} {s' : TState} {h' : Heap} :
    (c.write t s' h').heap t.ctaid = h' := by
  simp [Cfg.write, Cfg.heap, updC]

/-- The invariant after a step of thread `t`, given what the step may have
changed (`Chg`): bytes `t` may write in this phase (shared ones only in its
own CTA), or accumulator cells. -/
theorem inv_of_change {c : Cfg} {n d} (hI : S.Inv K L m0 c n d) {t : Tid} (ht : t ∈ L.threads)
    {s' : TState} {h' : Heap} {m : Nat} {d₁ : Ghost} (Chg : Dim3 → Loc → Prop)
    (hr : Run K (L.allocs K) (L.ctx t) (S.F t (c.ph t.ctaid)) S.Cell (S.J K L t (c.ph t.ctaid)) m
      s' h' d₁)
    (hkeep : ∀ b' x, ¬ Chg b' x → ((c.write t s' h').heap b').get x = (c.heap b').get x)
    (hchg : ∀ b' x, Chg b' x → ((S.F t (c.ph t.ctaid)).w x ∧ (x.1 = .shared → b' = t.ctaid)) ∨
      (x.1 = .global ∧ ∃ a, S.Cell a ∧ covers a 4 x.2))
    (hcells : ∀ b, S.Cell b → rd32 (c.write t s' h').mem b = rd32 m0 b + tsum L.threads fun u =>
      accUpTo (fun k => S.Δ u k b) (c.ph u.ctaid) + (if u = t then d₁ else d u) b) :
    S.Inv K L m0 (c.write t s' h') (fun u => if u = t then m else n u)
      (fun u => if u = t then d₁ else d u) := by
  classical
  have hph : (c.write t s' h').ph = c.ph := rfl
  refine ⟨fun u hu => hI.ph u hu, ?_, ?_, ?_, ?_⟩
  · intro u hu
    by_cases hut : u = t
    · subst hut; simp only [↓reduceIte, hph]; rw [write_self]
      simpa [Cfg.write, updT] using hr
    · simp only [hut, ↓reduceIte, hph]
      have hts : (c.write t s' h').ts u = c.ts u := by simp [Cfg.write, updT, hut]
      rw [hts]
      refine frameJ (hI.run u hu) fun x hx => (hkeep _ x fun hc => ?_).symm
      rcases hchg _ x hc with ⟨hw, hsh⟩ | ⟨hg, a, ha, hcov⟩
      · by_cases hcu : u.ctaid = t.ctaid
        · rw [hcu] at hx
          exact hS.sameCta t ht u hu (Ne.symm hut) hcu.symm _ x hw hx
        · obtain ⟨sp, y⟩ := x
          cases sp with
          | shared => exact hcu (hsh rfl)
          | global => exact hS.crossCta t ht u hu (Ne.symm hcu) _ _ y hw hx
      · obtain ⟨sp, y⟩ := x
        simp only at hg; subst hg
        exact cellsOut' hS ha hcov u hu _ hx
  · intro b' x hx hno
    rw [hph] at hno ⊢
    rw [hkeep b' x fun hc => ?_]
    · exact hI.mem b' x hx hno
    rcases hchg b' x hc with ⟨hw, hsh⟩ | ⟨hg, a, ha, hcov⟩
    · by_cases hb : b' = t.ctaid
      · subst hb; exact hno t ht rfl hw
      · obtain ⟨u, hu, rfl, j, -, hux⟩ := hx
        obtain ⟨sp, y⟩ := x
        cases sp with
        | shared => exact hb (hsh rfl)
        | global => exact hS.crossCta t ht u hu (Ne.symm hb) _ j y hw hux
    · obtain ⟨u, hu, -, j, -, hux⟩ := hx
      obtain ⟨sp, y⟩ := x
      simp only at hg; subst hg
      exact cellsOut' hS ha hcov u hu j hux
  · intro a hno hcell
    have := hkeep t.ctaid (.global, a) fun hc => by
      rcases hchg _ _ hc with ⟨hw, -⟩ | ⟨-, b, hb, hcov⟩
      · exact hno t ht _ (hI.ph t ht) hw
      · exact hcell b hb hcov
    exact this.trans (hI.untouched a hno hcell)
  · intro b hb; rw [hcells b hb]; rfl

theorem inv_thread {c : Cfg} {n d} (hI : S.Inv K L m0 c n d) {t : Tid} (ht : t ∈ L.threads)
    {s' : TState} {h' : Heap} (hres : c.res K L t = .ok s' h') :
    ∃ n' d', S.Inv K L m0 (c.write t s' h') n' d' ∧ n' t < n t ∧ ∀ u, u ≠ t → n' u = n u := by
  classical
  obtain ⟨m, hm, d₁, hr, heff⟩ := stepJ (hI.run t ht) (hS.cellsOut t ht _) hres
  refine ⟨fun u => if u = t then m else n u, fun u => if u = t then d₁ else d u, ?_,
    by simp [hm], fun u hu => by simp [hu]⟩
  have same : ∀ b, (tsum L.threads fun u => accUpTo (fun k => S.Δ u k b) (c.ph u.ctaid) +
      (if u = t then d t else d u) b) =
      tsum L.threads fun u => accUpTo (fun k => S.Δ u k b) (c.ph u.ctaid) + d u b :=
    fun b => tsum_congr fun u _ => by by_cases h : u = t <;> simp [h]
  cases heff with
  | none =>
    refine inv_of_change hS hI ht (fun _ _ => False) hr (fun b' x _ => by rw [write_none]) nofun ?_
    intro b hb
    rw [same b]; exact hI.cells b hb
  | @store sp a sz v hf =>
    have hkeep : ∀ b' x, ¬ (x.1 = sp ∧ (sp = .shared → b' = t.ctaid) ∧ covers a sz.bytes x.2) →
        ((c.write t s' ((c.heap t.ctaid).set sp (wr ((c.heap t.ctaid).at sp) a sz v))).heap b').get x =
          (c.heap b').get x := fun b' x hx => write_get hx
    refine inv_of_change hS hI ht _ hr hkeep ?_ ?_
    · rintro b' ⟨sp', y⟩ ⟨rfl, hsh, hcov⟩; exact .inl ⟨hf y hcov, hsh⟩
    · intro b hb
      rw [same b, ← hI.cells b hb]
      apply rd32_congr; intro y hy
      have := hkeep t.ctaid (.global, y) fun ⟨hsp, _, hcov⟩ => by
        subst hsp; exact hS.cellsOut t ht _ b hb y hy (.inr (hf y hcov))
      exact this
  | @atom a g δ hcell hval =>
    have hkeep : ∀ b' x, ¬ (x.1 = .global ∧ (Sp.global = .shared → b' = t.ctaid) ∧
        covers a Size.b4.bytes x.2) →
        ((c.write t s' ((c.heap t.ctaid).set .global (wr (c.heap t.ctaid).g a .b4 g))).heap b').get x =
          (c.heap b').get x := fun b' x hx => write_get (sp := .global) hx
    refine inv_of_change hS hI ht _ hr hkeep ?_ ?_
    · rintro b' ⟨sp', y⟩ ⟨rfl, -, hcov⟩; exact .inr ⟨rfl, a, hcell, hcov⟩
    · intro b hb
      show rd32 (wr c.mem a .b4 g) b = _
      by_cases hab : b = a
      · subst hab
        rw [rd32_wr_same, hval]
        show rd32 c.mem b + δ = _
        rw [hI.cells b hb, BitVec.add_assoc]
        congr 1
        refine (tsum_update (threads_nodup L) ht (fun u _ hut => by simp [hut]) ?_).symm
        simp [Ghost.add]; rw [BitVec.add_assoc]
      · rw [rd32_congr (m₂ := c.mem) fun y hy => wr_outside (hS.cellsDisj b a hb hcell hab y hy ∘ id),
          hI.cells b hb]
        congr 1
        exact tsum_congr fun u _ => by by_cases hut : u = t <;> simp [hut, Ghost.add, hab]

theorem inv_bar {c : Cfg} {n d} (hI : S.Inv K L m0 c n d) {b : Dim3} (hb : BarReady K L c b) :
    ∃ n' d', S.Inv K L m0 (c.release b) n' d' ∧ S.μ L (c.release b) n' + 1 ≤ S.μ L c n := by
  classical
  obtain ⟨⟨t₀, ht₀, hb₀⟩, pc, hall⟩ := hb
  have hwait : ∀ u ∈ L.threads, u.ctaid = b → c.res K L u = .wait := fun u hu h => (hall u hu h).1
  have np : ∀ u ∈ L.threads, u.ctaid = b → _ := fun u hu (h : u.ctaid = b) =>
    next_phase hS hI hu fun v hv hvb => hwait v hv (hvb.trans h)
  have hph : ∀ b', (c.release b).ph b' = if b' = b then c.ph b + 1 else c.ph b' := fun b' => by
    simp only [Cfg.release]; split <;> simp_all
  have hts : ∀ u, (c.release b).ts u = if u.ctaid = b then (c.ts u).skip else c.ts u := fun _ => rfl
  have hheap : ∀ b', (c.release b).heap b' = c.heap b' := fun _ => rfl
  refine ⟨fun u => if u.ctaid = b then S.N u (c.ph b + 1) else n u,
    fun u => if u.ctaid = b then (fun _ => 0) else d u, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro u hu
    rw [hph]; split
    · next h => have := (np u hu h).2.1; rw [h] at this ⊢; exact this
    · exact hI.ph u hu
  · intro u hu
    rw [hph, hts, hheap]
    by_cases h : u.ctaid = b
    · have := (np u hu h).1
      simp only [h, ↓reduceIte] at this ⊢
      exact this
    · simp only [h, ↓reduceIte]; exact hI.run u hu
  · intro b' x hx _
    rw [hph, hheap]
    by_cases h : b' = b
    · subst h; simp only [↓reduceIte]
      exact agree_after hS hI (fun u hu hb => .inl (action_of_wait (hwait u hu hb))) hx
    · simp only [h, ↓reduceIte]
      exact hI.mem b' x hx fun u hu hub => by
        have := ‹∀ t ∈ L.threads, t.ctaid = b' → ¬ (S.F t ((c.release b).ph b')).w x› u hu hub
        simp only [hph, h, ↓reduceIte] at this; exact this
  · exact hI.untouched
  · intro cell hc
    rw [show (c.release b).mem = c.mem from rfl, hI.cells cell hc]
    congr 1
    refine tsum_congr fun u hu => ?_
    rw [hph]
    by_cases h : u.ctaid = b
    · simp only [h, ↓reduceIte, accUpTo]
      rw [(np u hu h).2.2.2, h]; simp
    · simp [h]
  · unfold μ
    apply sum_lt_of_dec ht₀
    · simp only [hph, hb₀, ↓reduceIte]
      have h1 := (np t₀ ht₀ hb₀).2.1
      rw [hb₀] at h1
      rw [S.fut_succ (t := t₀) (p := c.ph b) (by rw [hb₀]; exact h1)]
      omega
    · intro u hu
      by_cases h : u.ctaid = b
      · simp only [hph, h, ↓reduceIte]
        have h1 := (np u hu h).2.1
        rw [h] at h1
        rw [S.fut_succ (t := u) (p := c.ph b) (by rw [h]; exact h1)]
        omega
      · simp [hph, h]

theorem inv_reach : ∀ j c, Steps K L j (Cfg.init r0 p0 m0 sh0) c → ∃ n d, S.Inv K L m0 c n d ∧
    j + S.μ L c n ≤ S.μ L (Cfg.init r0 p0 m0 sh0) (fun t => S.N t 0) := by
  intro j c h
  generalize hc0 : Cfg.init r0 p0 m0 sh0 = c0 at h
  induction h with
  | refl => subst hc0; exact ⟨_, _, inv_init hS, by omega⟩
  | @tail j c₁ c₂ c₃ _ hstep ih =>
    obtain ⟨n, d, hI, hsum⟩ := ih hc0
    rcases hstep with ⟨t, ht, s', h', hres, rfl⟩ | ⟨b, hb, rfl⟩
    · obtain ⟨n', d', hI', hlt, heq⟩ := inv_thread hS hI ht hres
      refine ⟨n', d', hI', ?_⟩
      have : S.μ L (c₂.write t s' h') n' + 1 ≤ S.μ L c₂ n := by
        unfold μ
        apply sum_lt_of_dec ht
        · show n' t + S.fut t (c₂.ph t.ctaid) < n t + S.fut t (c₂.ph t.ctaid); omega
        · intro u _
          show n' u + S.fut u (c₂.ph u.ctaid) ≤ n u + S.fut u (c₂.ph u.ctaid)
          by_cases h : u = t
          · subst h; omega
          · exact Nat.le_of_eq (by rw [heq u h])
      omega
    · obtain ⟨n', d', hI', hlt⟩ := inv_bar hS hI hb
      exact ⟨n', d', hI', by omega⟩

theorem reach_inv {c : Cfg} (hc : Reach K L (Cfg.init r0 p0 m0 sh0) c) : ∃ n d, S.Inv K L m0 c n d := by
  obtain ⟨j, hj⟩ := hc.steps
  obtain ⟨n, d, hI, -⟩ := inv_reach hS j c hj
  exact ⟨n, d, hI⟩

omit hS in
/-- An execution that never faults, always progresses and is bounded has a
finished configuration. -/
theorem exists_done_of {c₀ : Cfg} (hp : ∀ c, Reach K L c₀ c → Done K L c ∨ ∃ c', Step K L c c')
    (hb : ∃ bound, ∀ j c, Steps K L j c₀ c → j ≤ bound) : ∃ c, Reach K L c₀ c ∧ Done K L c := by
  obtain ⟨bound, hb⟩ := hb
  have key : ∀ d j c, bound - j = d → Steps K L j c₀ c → ∃ c', Reach K L c₀ c' ∧ Done K L c' := by
    intro d
    induction d using Nat.strongRecOn with
    | _ d ih =>
      intro j c hd hs
      rcases hp c (Reach.of_steps hs) with hdone | ⟨c', hc'⟩
      · exact ⟨c, Reach.of_steps hs, hdone⟩
      · have hs' := Steps.tail hs hc'
        have := hb _ _ hs'
        exact ih (bound - (j + 1)) (by omega) (j + 1) c' rfl hs'
  exact key _ 0 c₀ rfl (.refl _)

/-- The phase theorem: per-thread, per-phase derivations and the
disjointness conditions of `Phased.Ok` give no fault, progress, bounded
executions, phase-relative race freedom and the final memory, for every
execution of the launch. -/
theorem phase_sound : S.Result K L (Cfg.init r0 p0 m0 sh0) m0 := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c hc hf
    obtain ⟨n, d, hI⟩ := reach_inv hS hc
    rcases hf with ⟨t, ht, hf⟩ | ⟨t, ht, u, hu, hcu, hw, hh | ⟨hw', hpc⟩⟩
    · exact notFaultJ (hI.run t ht) hf
    · exact wait_halted hI ht hu hcu hw hh
    · exact hpc (wait_pc hI ht hu hcu hw hw').symm
  · intro c hc
    obtain ⟨n, d, hI⟩ := reach_inv hS hc
    by_cases hok : ∃ t ∈ L.threads, ∃ s' h', c.res K L t = .ok s' h'
    · obtain ⟨t, ht, s', h', h⟩ := hok
      exact .inr ⟨_, .inl ⟨t, ht, s', h', h, rfl⟩⟩
    by_cases hd : Done K L c
    · exact .inl hd
    right
    have nok : ∀ t ∈ L.threads, c.res K L t = .wait ∨ c.res K L t = .halted := by
      intro t ht
      have := notFaultJ (hI.run t ht)
      cases hr : c.res K L t with
      | ok s' h' => exact absurd ⟨t, ht, s', h', hr⟩ hok
      | wait => exact .inl rfl
      | halted => exact .inr rfl
      | fault => exact absurd hr this
    have : ∃ t ∈ L.threads, c.res K L t ≠ .halted :=
      Classical.byContradiction fun h' => hd fun t ht =>
        Classical.byContradiction fun h'' => h' ⟨t, ht, h''⟩
    obtain ⟨t, ht, hnh⟩ := this
    have hw : c.res K L t = .wait := (nok t ht).resolve_right hnh
    refine ⟨_, .inr ⟨t.ctaid, ⟨⟨t, ht, rfl⟩, (c.ts t).pc, fun u hu hcu => ?_⟩, rfl⟩⟩
    have hwu : c.res K L u = .wait :=
      (nok u hu).resolve_right fun hh => wait_halted hI ht hu hcu.symm hw hh
    exact ⟨hwu, wait_pc hI hu ht hcu hwu hw⟩
  · exact ⟨S.μ L (Cfg.init r0 p0 m0 sh0) (fun t => S.N t 0),
      fun j c hj => by obtain ⟨n, d, _, h⟩ := inv_reach hS j c hj; omega⟩
  · intro c₁ c₂ h₁ h₂ t ht u hu htu x y hx hy ⟨hsp, hsh, hkind, byte, hbx, hby⟩
    obtain ⟨n₁, d₁, hI₁⟩ := reach_inv hS h₁
    obtain ⟨n₂, d₂, hI₂⟩ := reach_inv hS h₂
    by_cases hcp : t.ctaid = u.ctaid ∧ c₁.ph t.ctaid ≠ c₂.ph u.ctaid
    · exact .inr hcp
    have same : t.ctaid = u.ctaid → c₁.ph t.ctaid = c₂.ph u.ctaid :=
      fun h => Classical.byContradiction fun h' => hcp ⟨h, h'⟩
    have px := pendJ (hI₁.run t ht) hx
    have py := pendJ (hI₂.run u hu) hy
    -- a write of one thread against a touch of the other
    have clash : ∀ {v w : Tid} (hv : v ∈ L.threads) (hw : w ∈ L.threads), v ≠ w →
        ∀ kv kw sp, (v.ctaid = w.ctaid → kv = kw) → (sp = .shared → v.ctaid = w.ctaid) →
        (S.F v kv).w (sp, byte) → (S.F w kw).touches (sp, byte) → False := by
      intro v w hv hw hvw kv kw sp hk hshv hwv htw
      by_cases hc : v.ctaid = w.ctaid
      · rw [hk hc] at hwv; exact hS.sameCta v hv w hw hvw hc _ _ hwv htw
      · cases sp with
        | shared => exact hc (hshv rfl)
        | global => exact hS.crossCta v hv w hw hc _ _ byte hwv htw
    -- each pending access as a touch, a write, or a cell
    have tx : x.kind ≠ .atomic → (S.F t (c₁.ph t.ctaid)).touches (x.sp, byte) := fun ha => by
      rcases px with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, -⟩
      · exact h byte hbx
      · exact .inr (h byte hbx)
      · exact absurd h ha
    have ty : y.kind ≠ .atomic → (S.F u (c₂.ph u.ctaid)).touches (y.sp, byte) := fun ha => by
      rcases py with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, -⟩
      · exact h byte hby
      · exact .inr (h byte hby)
      · exact absurd h ha
    have wx : x.kind = .write → (S.F t (c₁.ph t.ctaid)).w (x.sp, byte) := fun hk => by
      rcases px with ⟨h, -⟩ | ⟨_, h⟩ | ⟨h, -⟩
      · rw [hk] at h; cases h
      · exact h byte hbx
      · rw [hk] at h; cases h
    have wy : y.kind = .write → (S.F u (c₂.ph u.ctaid)).w (y.sp, byte) := fun hk => by
      rcases py with ⟨h, -⟩ | ⟨_, h⟩ | ⟨h, -⟩
      · rw [hk] at h; cases h
      · exact h byte hby
      · rw [hk] at h; cases h
    have cx : x.kind = .atomic → x.sp = .global ∧ x.sz = .b4 ∧ S.Cell x.a := fun hk => by
      rcases px with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
      · rw [hk] at h; cases h
      · rw [hk] at h; cases h
      · exact h
    have cy : y.kind = .atomic → y.sp = .global ∧ y.sz = .b4 ∧ S.Cell y.a := fun hk => by
      rcases py with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
      · rw [hk] at h; cases h
      · rw [hk] at h; cases h
      · exact h
    cases hxk : x.kind <;> cases hyk : y.kind
    · rw [hxk, hyk] at hkind; rcases hkind with h | h <;> exact absurd rfl h
    · exact (clash hu ht (Ne.symm htu) _ _ y.sp (fun h => (same h.symm).symm)
        (fun h => (hsh (hsp ▸ h)).symm) (wy hyk) (hsp ▸ tx (by rw [hxk]; exact nofun))).elim
    · obtain ⟨hg, hs4, hc⟩ := cy hyk
      rw [hs4] at hby
      exact (cellsOut' hS hc hby t ht _ (hg ▸ hsp ▸ tx (by rw [hxk]; exact nofun))).elim
    · exact (clash ht hu htu _ _ x.sp same hsh (wx hxk) (hsp ▸ ty (by rw [hyk]; exact nofun))).elim
    · exact (clash ht hu htu _ _ x.sp same hsh (wx hxk) (hsp ▸ ty (by rw [hyk]; exact nofun))).elim
    · obtain ⟨hg, hs4, hc⟩ := cy hyk
      rw [hs4] at hby
      exact (cellsOut' hS hc hby t ht _ (hg ▸ hsp ▸ tx (by rw [hxk]; exact nofun))).elim
    · obtain ⟨hg, hs4, hc⟩ := cx hxk
      rw [hs4] at hbx
      exact (cellsOut' hS hc hbx u hu _ (hg ▸ hsp.symm ▸ ty (by rw [hyk]; exact nofun))).elim
    · obtain ⟨hg, hs4, hc⟩ := cx hxk
      rw [hs4] at hbx
      exact (cellsOut' hS hc hbx u hu _ (hg ▸ hsp.symm ▸ ty (by rw [hyk]; exact nofun))).elim
    · obtain ⟨-, hxs, hxc⟩ := cx hxk
      obtain ⟨-, hys, hyc⟩ := cy hyk
      refine .inl ⟨rfl, rfl, ?_, hxs.trans hys.symm⟩
      rw [hxs] at hbx; rw [hys] at hby
      exact Classical.byContradiction fun h => hS.cellsDisj _ _ hxc hyc h byte hbx hby
  · intro c hc hd
    obtain ⟨n, d, hI⟩ := reach_inv hS hc
    have hend : ∀ t ∈ L.threads, action K (L.ctx t) (c.ts t) = .done :=
      fun t ht => action_of_halted (hd t ht)
    have hJ : ∀ t ∈ L.threads, S.J K L t (c.ph t.ctaid) (c.ts t) (c.heap t.ctaid) (d t) :=
      fun t ht => (hI.run t ht).stop_of (.inr (hend t ht))
    have hlast : ∀ t ∈ L.threads, c.ph t.ctaid + 1 = S.P t.ctaid := fun t ht => by
      have := J_done (hJ t ht) (hend t ht); have := hI.ph t ht; omega
    refine ⟨?_, hI.untouched, ?_⟩
    · intro t ht k hk a hw
      have := agree_after hS hI (b := t.ctaid) (fun u hu _ => .inr (hend u hu))
        ⟨t, ht, rfl, k, hk, .inr hw⟩
      rw [hlast t ht] at this
      exact this
    · intro cell hcell
      rw [hI.cells cell hcell]
      congr 1
      refine tsum_congr fun t ht => ?_
      rw [← hlast t ht, (hJ t ht).1]; rfl

end Phased

end Ptx
