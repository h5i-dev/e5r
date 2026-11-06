/- Full-mask aligned warp synchronization for the original PTX Kernel AST.
The legacy SIMT model deliberately refuses these additional forms. This module
preserves ordinary memory steps but distinguishes warp and CTA release groups.
Noncoherent reads use initial data only under the proved ReadOnlyNC property
required in Total; this is a readonly-kernel subset, not mutable cache behavior.
-/
import Ptx.Semantics.SIMT

namespace Ptx.Warp

structure Id where
  ctaid : Dim3
  index : Nat
  deriving Repr, DecidableEq, Inhabited

def id (L : Launch) (t : Tid) : Id :=
  ⟨t.ctaid, (t.tid.x.toNat + L.block.x.toNat * (t.tid.y.toNat + L.block.y.toNat * t.tid.z.toNat))/32⟩

structure State where
  cfg : Cfg
  initial : Mem
  phase : Id → Nat

def State.init (r : Tid → String → Val) (p : Tid → String → Bool) (m : Mem) (sh : Dim3 → Mem) : State :=
  ⟨Cfg.init r p m sh, m, fun _ => 0⟩

/-- Whether this thread is executing the full-mask warp barrier now. -/
def atWarp (K : Kernel) (s : TState) : Bool :=
  match K.body[s.pc]? with
  | some st => guardHolds s st.guard && match st.instr with | .warpBar => true | _ => false
  | none => false

def atNC (K : Kernel) (s : TState) : Bool :=
  match K.body[s.pc]? with
  | some st => guardHolds s st.guard && match st.instr with | .ldGlobalNCF32 .. => true | _ => false
  | none => false

/-- Same source instructions; no barrier or qualifier is rewritten in the AST. -/
def action (K : Kernel) (c : Ctx) (s : TState) : Action :=
  match K.body[s.pc]? with
  | some st =>
    if guardHolds s st.guard then
      match st.instr with
      | .warpBar => .bar
      | .ldGlobalNCF32 d a =>
        match dataAddr c s .global a with
        | some (.global, x) => .load .global x .b4 (fun v => s.set d v)
        | _ => .fault
      | _ => Ptx.action K c s
    else Ptx.action K c s
  | none => Ptx.action K c s

/-- Global NC load data is frozen at launch. Total also proves that no thread
writes any byte an NC load observes, so cache coherence is never assumed. -/
def res (K : Kernel) (L : Launch) (c : State) (t : Tid) : TRes :=
  let s := c.cfg.ts t
  let h := c.cfg.heap t.ctaid
  match action K (L.ctx t) s with
  | .next s' => .ok s' h
  | .load sp a sz k =>
    if accessOk (L.allocs K sp) a sz then
      .ok (k (rd (if decide (sp = .global) && atNC K s then c.initial else h.at sp) a sz)) h
    else .fault
  | .store sp a sz v s' =>
    if accessOk (L.allocs K sp) a sz then .ok s' (h.set sp (wr (h.at sp) a sz v)) else .fault
  | .atom sp a sz f k =>
    if accessOk (L.allocs K sp) a sz then
      let old := rd (h.at sp) a sz
      .ok (k old) (h.set sp (wr (h.at sp) a sz (f old)))
    else .fault
  | .bar => .wait
  | .done => .halted
  | .fault => .fault

def releaseWarp (L : Launch) (c : State) (w : Id) : State :=
  let cfg := c.cfg
  { c with cfg := { cfg with ts := fun t => if id L t = w then (c.cfg.ts t).skip else c.cfg.ts t }
           phase := fun v => if v = w then c.phase v + 1 else c.phase v }

def releaseCta (c : State) (b : Dim3) : State := { c with cfg := c.cfg.release b }

def CtaReady (K : Kernel) (L : Launch) (c : State) (b : Dim3) : Prop :=
  (∃ t ∈ L.threads, t.ctaid = b) ∧
  ∃ pc, ∀ t ∈ L.threads, t.ctaid = b →
    res K L c t = .wait ∧ (c.cfg.ts t).pc = pc ∧ atWarp K (c.cfg.ts t) = false

/-- Exactly32 actual members are required for the supported full-mask form.
This intentionally excludes partially populated full-mask warps. -/
def WarpReady (K : Kernel) (L : Launch) (c : State) (w : Id) : Prop :=
  (L.threads.filter (fun t => decide (id L t = w))).length = 32 ∧
  ∃ pc, ∀ t ∈ L.threads, id L t = w →
    res K L c t = .wait ∧ (c.cfg.ts t).pc = pc ∧ atWarp K (c.cfg.ts t) = true

def Step (K : Kernel) (L : Launch) (c d : State) : Prop :=
  (∃ t ∈ L.threads, ∃ s h, res K L c t = .ok s h ∧ d = {c with cfg := c.cfg.write t s h}) ∨
  (∃ b, CtaReady K L c b ∧ d = releaseCta c b) ∨
  (∃ w, WarpReady K L c w ∧ d = releaseWarp L c w)

inductive Reach (K : Kernel) (L : Launch) : State → State → Prop
  | refl (c : State) : Reach K L c c
  | tail {a b c} : Reach K L a b → Step K L b c → Reach K L a c

inductive Steps (K : Kernel) (L : Launch) : Nat → State → State → Prop
  | refl (c : State) : Steps K L 0 c c
  | tail {n a b c} : Steps K L n a b → Step K L b c → Steps K L (n+1) a c

def Done (K : Kernel) (L : Launch) (c : State) : Prop := ∀ t ∈ L.threads, res K L c t = .halted

/-- Only same-scope waits are compared for divergent PCs. A fast warp may
legally wait at a CTA barrier while a different warp is still locally waiting. -/
def Diverged (K : Kernel) (L : Launch) (c : State) : Prop :=
  ∃ t ∈ L.threads, ∃ u ∈ L.threads, t.ctaid = u.ctaid ∧ res K L c t = .wait ∧
    ((atWarp K (c.cfg.ts t) = false ∧
       (res K L c u = .halted ∨ (res K L c u = .wait ∧ atWarp K (c.cfg.ts u) = false ∧
         (c.cfg.ts t).pc ≠ (c.cfg.ts u).pc))) ∨
     (atWarp K (c.cfg.ts t) = true ∧ id L t = id L u ∧
       (res K L c u = .halted ∨ (res K L c u = .wait ∧ atWarp K (c.cfg.ts u) = true ∧
         (c.cfg.ts t).pc ≠ (c.cfg.ts u).pc))))

def Faults (K : Kernel) (L : Launch) (c : State) : Prop :=
  (∃ t ∈ L.threads, res K L c t = .fault) ∨ Diverged K L c ∨
  (∃ t ∈ L.threads, atWarp K (c.cfg.ts t) = true ∧
    (L.threads.filter (fun u => decide (id L u = id L t))).length ≠ 32)

def pending (K : Kernel) (L : Launch) (c : State) (t : Tid) : Option Acc :=
  (action K (L.ctx t) (c.cfg.ts t)).acc

/-- The whole-kernel certificate must prove readonly NC footprints against
all executed writes, including writes of the very same thread. -/
def ReadOnlyNC (K : Kernel) (L : Launch) (initial : State) : Prop :=
  ∀ c d, Reach K L initial c → Reach K L initial d →
    ∀ t ∈ L.threads, ∀ u ∈ L.threads, atNC K (c.cfg.ts t) = true →
    ∀ a b, pending K L c t = some a → pending K L d u = some b →
    b.sp = .global → b.kind ≠ .read →
      ∀ x, covers a.a a.sz.bytes x → ¬ covers b.a b.sz.bytes x

def RaceFree (K : Kernel) (L : Launch) (initial : State) : Prop :=
  ∀ c d, Reach K L initial c → Reach K L initial d →
    ∀ t ∈ L.threads, ∀ u ∈ L.threads, t ≠ u → ∀ a b,
    pending K L c t = some a → pending K L d u = some b → Conflict t a u b →
    (a.kind = .atomic ∧ b.kind = .atomic ∧ a.a = b.a ∧ a.sz = b.sz) ∨
    (t.ctaid = u.ctaid ∧ (c.cfg.ph t.ctaid ≠ d.cfg.ph u.ctaid ∨
      (id L t = id L u ∧ c.phase (id L t) ≠ d.phase (id L u))))

def Total (K : Kernel) (L : Launch) (initial : State) : Prop :=
  initial.initial = initial.cfg.mem ∧
  (∀ c, Reach K L initial c → ¬ Faults K L c) ∧
  (∀ c, Reach K L initial c → Done K L c ∨ ∃ d, Step K L c d) ∧
  (∃ bound, ∀ n c, Steps K L n initial c → n ≤ bound) ∧
  RaceFree K L initial ∧ ReadOnlyNC K L initial ∧
  ∃ c, Reach K L initial c ∧ Done K L c

/-- The target contract compares all final global bytes and frames outputs;
none of its clauses is replaced by an assumed operator specification. -/
def Equivalent (K₀ K₁ : Kernel) (L : Launch) (initial : State) (output : Addr → Prop) : Prop :=
  Total K₀ L initial ∧ Total K₁ L initial ∧
  (∀ c d, Reach K₀ L initial c → Done K₀ L c → Reach K₁ L initial d → Done K₁ L d →
    c.cfg.mem = d.cfg.mem) ∧
  (∀ c, Reach K₀ L initial c → Done K₀ L c → ∀ a, ¬ output a → c.cfg.mem a = initial.cfg.mem a) ∧
  (∀ d, Reach K₁ L initial d → Done K₁ L d → ∀ a, ¬ output a → d.cfg.mem a = initial.cfg.mem a)

theorem releaseWarp_global_frame (L : Launch) (c : State) (w : Id) :
    (releaseWarp L c w).cfg.mem = c.cfg.mem := rfl

theorem releaseWarp_shared_frame (L : Launch) (c : State) (w : Id) :
    (releaseWarp L c w).cfg.sh = c.cfg.sh := rfl

theorem releaseWarp_cta_phase (L : Launch) (c : State) (w : Id) :
    (releaseWarp L c w).cfg.ph = c.cfg.ph := rfl

theorem releaseWarp_other_thread (L : Launch) (c : State) (w : Id) (t : Tid)
    (outside : id L t ≠ w) : (releaseWarp L c w).cfg.ts t = c.cfg.ts t := by
  simp only [releaseWarp, outside, ↓reduceIte]

theorem releaseWarp_member (L : Launch) (c : State) (w : Id) (t : Tid)
    (inside : id L t = w) : (releaseWarp L c w).cfg.ts t = (c.cfg.ts t).skip := by
  simp only [releaseWarp, inside, ↓reduceIte]

/-- One actual memory action preserves every byte outside its pending write.
This includes atomics and all ordinary and volatile stores. -/
theorem res_global_frame (K : Kernel) (L : Launch) (c : State) (t : Tid)
    (s : TState) (h : Heap) (x : Addr)
    (outside : ∀ a, pending K L c t = some a → a.sp = .global → a.kind ≠ .read →
      ¬ covers a.a a.sz.bytes x)
    (ok : res K L c t = .ok s h) : h.g x = c.cfg.mem x := by
  cases ha : action K (L.ctx t) (c.cfg.ts t) with
  | next s' => simp only [res, ha] at ok; cases ok; rfl
  | load sp a sz k =>
    simp only [res, ha] at ok
    split at ok <;> cases ok
    rfl
  | store sp a sz v s' =>
    have ho := outside ⟨sp, a, sz, .write⟩ (by simp [pending, ha, Action.acc])
    simp only [res, ha] at ok
    split at ok <;> cases ok
    cases sp with
    | shared => rfl
    | global => exact wr_outside (ho rfl (by simp))
  | atom sp a sz f k =>
    have ho := outside ⟨sp, a, sz, .atomic⟩ (by simp [pending, ha, Action.acc])
    simp only [res, ha] at ok
    split at ok <;> cases ok
    cases sp with
    | shared => rfl
    | global => exact wr_outside (ho rfl (by simp))
  | bar => simp [res, ha] at ok
  | done => simp [res, ha] at ok
  | fault => simp [res, ha] at ok

/-- Reachable global-memory frame, quantified over actual grid executions. -/
theorem reach_global_frame (K : Kernel) (L : Launch) (initial : State) (S : Addr → Prop)
    (outside : ∀ c, Reach K L initial c → ∀ t ∈ L.threads, ∀ a,
      pending K L c t = some a → a.sp = .global → a.kind ≠ .read →
      ∀ x, S x → ¬ covers a.a a.sz.bytes x)
    {c : State} (hc : Reach K L initial c) :
    ∀ x, S x → c.cfg.mem x = initial.cfg.mem x := by
  induction hc with
  | refl => intro x _; rfl
  | @tail b c hb hstep ih =>
    intro x hx
    rcases hstep with ⟨t, ht, s, h, ok, rfl⟩ | ⟨b, _, rfl⟩ | ⟨w, _, rfl⟩
    · exact (res_global_frame K L _ t s h x
        (fun a ha hs hk => outside _ hb t ht a ha hs hk x hx) ok).trans (ih x hx)
    · exact ih x hx
    · exact ih x hx

/-- The readonly requirement is sufficient to justify reading the initial
bytes at every reachable NC load. It is an obligation, not an oracle coupling
or a silently assumed cache-coherence property. -/
theorem nc_read_current_eq_initial (K : Kernel) (L : Launch) (initial c : State)
    (ro : ReadOnlyNC K L initial) (hc : Reach K L initial c)
    (t : Tid) (ht : t ∈ L.threads) (nc : atNC K (c.cfg.ts t) = true)
    (a : Acc) (ha : pending K L c t = some a) :
    rd c.cfg.mem a.a a.sz = rd initial.cfg.mem a.a a.sz := by
  apply rd_congr
  apply reach_global_frame K L initial (covers a.a a.sz.bytes) ?_ hc
  intro d hd u hu b hb hs hk x hx
  exact ro c d hc hd t ht u hu nc a b ha hb hs hk x hx

#print axioms res_global_frame
#print axioms reach_global_frame
#print axioms nc_read_current_eq_initial

/-- Every transition preserves the launch's initial-memory snapshot. -/
theorem step_snapshot (K : Kernel) (L : Launch) {c d : State}
    (h : Step K L c d) : d.initial = c.initial := by
  rcases h with ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl

theorem reach_snapshot (K : Kernel) (L : Launch) {initial c : State}
    (h : Reach K L initial c) : c.initial = initial.initial := by
  induction h with
  | refl => rfl
  | tail _ step ih => exact (step_snapshot K L step).trans ih

/-- The NC operational read and a coherent read coincide under the certified
readonly property and the explicit initial-snapshot invariant. -/
theorem nc_snapshot_eq_current (K : Kernel) (L : Launch) (initial c : State)
    (snapshot : initial.initial = initial.cfg.mem)
    (ro : ReadOnlyNC K L initial) (hc : Reach K L initial c)
    (t : Tid) (ht : t ∈ L.threads) (nc : atNC K (c.cfg.ts t) = true)
    (a : Acc) (ha : pending K L c t = some a) :
    rd c.initial a.a a.sz = rd c.cfg.mem a.a a.sz := by
  rw [reach_snapshot K L hc, snapshot]
  exact (nc_read_current_eq_initial K L initial c ro hc t ht nc a ha).symm

/-- Instructions outside the new forms retain exactly the old action. -/
theorem action_ordinary (K : Kernel) (ctx : Ctx) (s : TState)
    (hw : atWarp K s = false) (hn : atNC K s = false) :
    action K ctx s = Ptx.action K ctx s := by
  cases hb : K.body[s.pc]? with
  | none => simp [action, Ptx.action, hb]
  | some st =>
    by_cases hg : guardHolds s st.guard = true
    · cases hi : st.instr <;> simp_all [action, Ptx.action, atWarp, atNC]
    · have hg' : guardHolds s st.guard = false := by cases h : guardHolds s st.guard <;> simp_all
      simp [action, Ptx.action, hb, hg']

theorem res_ordinary (K : Kernel) (L : Launch) (c : State) (t : Tid)
    (hw : atWarp K (c.cfg.ts t) = false) (hn : atNC K (c.cfg.ts t) = false) :
    res K L c t = c.cfg.res K L t := by
  unfold res Cfg.res tstep
  dsimp only
  rw [action_ordinary K (L.ctx t) (c.cfg.ts t) hw hn]
  cases Ptx.action K (L.ctx t) (c.cfg.ts t) <;> simp [hn]

#print axioms nc_snapshot_eq_current
#print axioms action_ordinary
#print axioms res_ordinary

end Ptx.Warp
