/- Checked concrete schedules for Ptx.Warp. Successful execution gives actual
Reach, not a replacement numeric specification. Useful for model regressions
and future semantic negatives; it is not a universal Total certificate. -/
import Ptx.Semantics.Warp

namespace Ptx.Warp

def waitB : TRes → Bool | .wait => true | _ => false
def haltB : TRes → Bool | .halted => true | _ => false

theorem waitB_spec {r : TRes} (h : waitB r = true) : r = .wait := by
  cases r <;> simp_all [waitB]

theorem haltB_spec {r : TRes} (h : haltB r = true) : r = .halted := by
  cases r <;> simp_all [haltB]

def warpReadyB (K : Kernel) (L : Launch) (c : State) (w : Id) : Bool :=
  let members := L.threads.filter (fun t => decide (id L t = w))
  members.length == 32 && match members with
    | [] => false
    | t₀ :: rest => (t₀ :: rest).all fun t =>
      waitB (res K L c t) && ((c.cfg.ts t).pc == (c.cfg.ts t₀).pc) && atWarp K (c.cfg.ts t)

def ctaReadyB (K : Kernel) (L : Launch) (c : State) (b : Dim3) : Bool :=
  match L.threads.filter (fun t => decide (t.ctaid = b)) with
  | [] => false
  | t₀ :: rest => (t₀ :: rest).all fun t =>
    waitB (res K L c t) && ((c.cfg.ts t).pc == (c.cfg.ts t₀).pc) && !atWarp K (c.cfg.ts t)

theorem warpReadyB_spec {K : Kernel} {L : Launch} {c : State} {w : Id}
    (h : warpReadyB K L c w = true) : WarpReady K L c w := by
  simp only [warpReadyB, Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, ?_⟩
  split at h
  · simp_all
  · next t₀ rest hf =>
    refine ⟨(c.cfg.ts t₀).pc, fun t ht hw => ?_⟩
    have hm : t ∈ L.threads.filter (fun t => decide (id L t = w)) :=
      List.mem_filter.2 ⟨ht, by simpa using hw⟩
    rw [hf] at hm
    have ht := List.all_eq_true.1 h.2 t hm
    simp only [Bool.and_eq_true, beq_iff_eq] at ht
    exact ⟨waitB_spec ht.1.1, ht.1.2, ht.2⟩

theorem ctaReadyB_spec {K : Kernel} {L : Launch} {c : State} {b : Dim3}
    (h : ctaReadyB K L c b = true) : CtaReady K L c b := by
  unfold ctaReadyB at h
  split at h
  · simp_all
  · next t₀ rest hf =>
    have hm : t₀ ∈ L.threads.filter (fun t => decide (t.ctaid = b)) := by
      rw [hf]; exact List.mem_cons_self
    rw [List.mem_filter] at hm
    refine ⟨⟨t₀, hm.1, by simpa using hm.2⟩, (c.cfg.ts t₀).pc, fun t ht hb => ?_⟩
    have htf : t ∈ L.threads.filter (fun t => decide (t.ctaid = b)) :=
      List.mem_filter.2 ⟨ht, by simpa using hb⟩
    rw [hf] at htf
    have ht := List.all_eq_true.1 h t htf
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at ht
    exact ⟨waitB_spec ht.1.1, ht.1.2, ht.2⟩

inductive Choice where
  | run (t : Tid) (n : Nat)
  | warp (w : Id)
  | cta (b : Dim3)

def runT (K : Kernel) (L : Launch) : State → Tid → Nat → Option State
  | c, _, 0 => some c
  | c, t, n+1 => match res K L c t with
    | .ok s h => runT K L { c with cfg := c.cfg.write t s h } t n
    | _ => none

def execute (K : Kernel) (L : Launch) : State → List Choice → Option State
  | c, [] => some c
  | c, .run t n :: rest =>
    if t ∈ L.threads then (runT K L c t n).bind (execute K L · rest) else none
  | c, .warp w :: rest => if warpReadyB K L c w then execute K L (releaseWarp L c w) rest else none
  | c, .cta b :: rest => if ctaReadyB K L c b then execute K L (releaseCta c b) rest else none

def doneB (K : Kernel) (L : Launch) (c : State) : Bool :=
  L.threads.all (fun t => haltB (res K L c t))

theorem doneB_spec {K : Kernel} {L : Launch} {c : State}
    (h : doneB K L c = true) : Done K L c :=
  fun t ht => haltB_spec (List.all_eq_true.1 h t ht)

theorem Reach.trans {K : Kernel} {L : Launch} {a b c : State}
    (hab : Reach K L a b) (hbc : Reach K L b c) : Reach K L a c := by
  induction hbc with
  | refl => exact hab
  | tail _ h ih => exact .tail ih h

theorem runT_reach {K : Kernel} {L : Launch} {t : Tid} (ht : t ∈ L.threads) :
    ∀ n {c d : State}, runT K L c t n = some d → Reach K L c d := by
  intro n
  induction n with
  | zero => intro c d h; simp only [runT, Option.some.injEq] at h; subst d; exact .refl _
  | succ n ih =>
    intro c d h
    simp only [runT] at h
    split at h
    · next s heap hr =>
      exact Reach.trans (.tail (.refl _) (.inl ⟨t, ht, s, heap, hr, rfl⟩)) (ih h)
    all_goals exact absurd h nofun

theorem execute_reach {K : Kernel} {L : Launch} :
    ∀ cs {c d : State}, execute K L c cs = some d → Reach K L c d := by
  intro cs
  induction cs with
  | nil => intro c d h; simp only [execute, Option.some.injEq] at h; subst d; exact .refl _
  | cons choice cs ih =>
    intro c d h
    cases choice with
    | run t n =>
      simp only [execute] at h
      split at h
      · next ht =>
        cases hr : runT K L c t n with
        | none => simp [hr] at h
        | some mid =>
          simp only [hr, Option.bind_some] at h
          exact Reach.trans (runT_reach ht n hr) (ih h)
      · exact absurd h nofun
    | warp w =>
      simp only [execute] at h
      split at h
      · next hw => exact Reach.trans (.tail (.refl _) (.inr (.inr ⟨w, warpReadyB_spec hw, rfl⟩))) (ih h)
      · exact absurd h nofun
    | cta b =>
      simp only [execute] at h
      split at h
      · next hb => exact Reach.trans (.tail (.refl _) (.inr (.inl ⟨b, ctaReadyB_spec hb, rfl⟩))) (ih h)
      · exact absurd h nofun

#print axioms warpReadyB_spec
#print axioms ctaReadyB_spec
#print axioms execute_reach
end Ptx.Warp
