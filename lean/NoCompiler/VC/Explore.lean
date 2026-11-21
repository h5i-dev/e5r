import NoCompiler.VC.Seg

/-
Paths between cut points (docs/isa/vcgen.md on next-a, item 5): from a cut
point, `explore` follows the code through every branch until each path
reaches a cut point or a return. A path's end is data: the symbolic state
there and the branch conditions taken on the way (`PEnd`). Straight-line code
is followed word by word, as `runW` does; only a taken branch or a jump looks
its target up afresh. `Reach.of_explore` is its soundness, proved once.
-/
namespace NoCompiler.VC.M

/-- A branch condition along a path: `evalBr op a b` came out `val`. -/
structure Cond where
  /-- The branch's address, for naming its hypothesis. -/
  pc : Word
  op : BrOp
  a : Sym
  b : Sym
  val : Bool

def Cond.den (ρ : Nat → Word) (μ : Word → Byte) (x : Cond) : Prop :=
  evalBr x.op (x.a.den ρ μ) (x.b.den ρ μ) = x.val

/-- Where a path ends: at a cut point, or at `jalr zero, 0(ra)` (the state before it). -/
inductive PEnd
  | cut (S : SState) (cs : List Cond)
  | ret (S : SState) (cs : List Cond)

/-- What a path's end must satisfy, under its conditions. -/
def PEnd.Next (ρ : Nat → Word) (μ : Word → Byte) (Q : State → Prop) : PEnd → Prop
  | .cut S cs => (∀ x ∈ cs, x.den ρ μ) → ∀ s', Matches ρ μ S s' → s'.exit = none → Q s'
  | .ret S cs => (∀ x ∈ cs, x.den ρ μ) → ∀ s', Matches ρ μ S s' → s'.exit = none →
      aligned ((S.reg 1).den ρ μ &&& ~~~1) 4 ∧ Q (s'.setPc ((S.reg 1).den ρ μ &&& ~~~1))

theorem PEnd.Next.weaken {ρ : Nat → Word} {μ : Word → Byte} {Q : State → Prop} {H : State → Prop}
    {e : PEnd} (h : e.Next ρ μ Q) : e.Next ρ μ (fun s' => H s' → Q s') := by
  cases e with
  | cut S cs => exact fun hc s' hm hx _ => h hc s' hm hx
  | ret S cs => exact fun hc s' hm hx => ⟨(h hc s' hm hx).1, fun _ => (h hc s' hm hx).2⟩

/-- The index of the word at `p`, when `p` is at a word boundary. -/
def wordIdx (c : Code) (p : Word) : Option Nat :=
  if (p - c.base).toNat % 4 = 0 then some ((p - c.base).toNat / 4) else none

theorem wordIdx_sound {c : Code} {p : Word} {k : Nat} (h : wordIdx c p = some k) :
    p = c.base + BitVec.ofNat 64 (4 * k) := by
  unfold wordIdx at h
  split at h
  · rename_i h4
    simp only [Option.some.injEq] at h; subst h
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h4), BitVec.ofNat_toNat, BitVec.setWidth_eq]
    bv_omega
  · simp at h

def both : Option (List PEnd × List Ob) → Option (List PEnd × List Ob) → Option (List PEnd × List Ob)
  | some (e₁, o₁), some (e₂, o₂) => some (e₁ ++ e₂, o₁ ++ o₂)
  | _, _ => none

/-- Every path from `S` (at word `k`, the words from there `ws`) to the next
    cut point or return; `first` skips the cut check where the run starts. -/
def explore (c : Code) (D : Dom) (cuts : List Word) (fetch : Nat → List (BitVec 32)) :
    Nat → Bool → Nat → List (BitVec 32) → SState → List Cond → Option (List PEnd × List Ob)
  | 0, _, _, _, _, _ => none
  | fuel + 1, first, k, ws, S, cs =>
    if !first && cuts.contains S.pc then some ([.cut S cs], []) else
    if D.mem S.pc then
      match ws with
      | [] => none
      | w :: ws' =>
        match decode w with
        | some (.branch op rs1 rs2 off) =>
          let t := S.pc + off.signExtend 64
          if aligned t 4 then
            match wordIdx c t with
            | some k' =>
              both (explore c D cuts fetch fuel false k' (fetch k') { S with pc := t }
                  (⟨S.pc, op, S.reg rs1, S.reg rs2, true⟩ :: cs))
                (explore c D cuts fetch fuel false (k + 1) ws' { S with pc := S.pc + 4 }
                  (⟨S.pc, op, S.reg rs1, S.reg rs2, false⟩ :: cs))
            | none => none
          else none
        | some (.jal rd off) =>
          let t := S.pc + off.signExtend 64
          if aligned t 4 then
            match wordIdx c t with
            | some k' => explore c D cuts fetch fuel false k' (fetch k')
                { S.setReg rd (.const (S.pc + 4)) with pc := t } cs
            | none => none
          else none
        | some (.jalr rd rs1 off) =>
          if rd = 0 ∧ rs1 = 1 ∧ off = 0 then some ([.ret S cs], []) else
          match S.reg rs1 with
          | .const v =>
            let t := (v + off.signExtend 64) &&& ~~~1
            if aligned t 4 then
              match wordIdx c t with
              | some k' => explore c D cuts fetch fuel false k' (fetch k')
                  { S.setReg rd (.const (S.pc + 4)) with pc := t } cs
              | none => none
            else none
          | _ => none
        | some i =>
          match sstep i S with
          | some (S₁, o₁) => (explore c D cuts fetch fuel false (k + 1) ws' S₁ cs).map fun p => (p.1, o₁ ++ p.2)
          | none => none
        | none => none
    else none

theorem matches_setPc {ρ : Nat → Word} {μ : Word → Byte} {S : SState} {s : State} (hm : Matches ρ μ S s)
    (t : Word) : Matches ρ μ { S with pc := t } (s.setPc t) :=
  ⟨hm.1, rfl, fun r => (State.setPc_reg s t r).trans (hm.2.2.1 r), (State.setPc_mem s t).trans hm.2.2.2⟩

/-- A register written and the pc set, in both states. -/
theorem matches_setReg_setPc {ρ : Nat → Word} {μ : Word → Byte} {S : SState} {s : State}
    (hm : Matches ρ μ S s) (rd : Reg) (v : Sym) (w : Word) (hw : w = v.den ρ μ) (p : Word) :
    Matches ρ μ { S.setReg rd v with pc := p } ((s.setReg rd w).setPc p) := by
  obtain ⟨hl, _, hr, hmem⟩ := hm
  have hmS : (S.setReg rd v).mem = S.mem := by unfold SState.setReg; split <;> rfl
  refine ⟨SState.length_setReg hl rd v, rfl, fun q => ?_, by rw [State.setPc_mem, State.setReg_mem, hmem]; show _ = SMem.den ρ μ (S.setReg rd v).mem; rw [hmS]⟩
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

theorem pc_succ {b : Word} {k : Nat} (h : 4 * (k + 1) < 2 ^ 64) :
    b + BitVec.ofNat 64 (4 * k) + 4 = b + BitVec.ofNat 64 (4 * (k + 1)) := by
  rw [BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq
  have h4 : (4 : Word).toNat = 4 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h4]
  omega

/-- `explore`, sound. -/
theorem Reach.of_explore {ρ : Nat → Word} {μ : Word → Byte} {c : Code} {P : Perm} {D : Dom}
    {Q : State → Prop} {cuts : List Word} {τ : List Event} {fetch : Nat → List (BitVec 32)}
    (hb : 4 * c.words.size < 2 ^ 64) (hfe : ∀ k, fetch k = c.words.toList.drop k) :
    ∀ {fuel : Nat} {first : Bool} {k : Nat} {ws : List (BitVec 32)} {S : SState} {cs : List Cond}
      {ends : List PEnd} {obs : List Ob} {s : State},
      explore c D cuts fetch fuel first k ws S cs = some (ends, obs) →
      c.words.toList.drop k = ws → S.pc = c.base + BitVec.ofNat 64 (4 * k) → Matches ρ μ S s →
      s.exit = none → s.trace = τ → (∀ x ∈ cs, x.den ρ μ) → (∀ o ∈ obs, o.den ρ μ P) →
      (∀ e ∈ ends, e.Next ρ μ (fun s' => s'.trace = τ → Q s')) → Reach c P D Q s
  | 0, _, _, _, _, _, _, _, _, h, _, _, _, _, _, _, _, _ => by simp [explore] at h
  | fuel + 1, first, k, ws, S, cs, ends, obs, s, h, hd, hpc, hm, hx, ht, hcs, hob, hN => by
    simp only [explore] at h
    split at h
    · -- a cut point
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact .done (hN _ (List.mem_singleton_self _) hcs s hm hx ht)
    split at h
    case isFalse => simp at h
    rename_i hD
    have hD' : D.mem s.pc := by rw [hm.2.1]; exact hD
    have hpcS : s.pc = S.pc := hm.2.1
    split at h
    · simp at h
    rename_i w ws'
    have hk : k < c.words.toList.length := by
      apply Nat.lt_of_not_le; intro hc
      rw [List.drop_eq_nil_of_le hc] at hd; simp at hd
    have hsz : c.words.toList.length = c.words.size := by simp
    have hk4 : 4 * (k + 1) < 2 ^ 64 := by omega
    have hw : c.words.toList[k]? = some w := by rw [← List.head?_drop, hd]; rfl
    have hfetch : ∀ i, decode w = some i → c.instr s.pc = some i := fun i hi => by
      rw [hpcS, hpc]; unfold Code.instr
      rw [Code.fetch_index c k (by omega), hw]; exact hi
    have hd₁ : c.words.toList.drop (k + 1) = ws' := by rw [← List.drop_drop, hd]; rfl
    have hpc₁ : S.pc + 4 = c.base + BitVec.ofNat 64 (4 * (k + 1)) := by rw [hpc]; exact pc_succ hk4
    split at h
    · -- a conditional branch
      rename_i op rs1 rs2 off hi
      split at h
      case isFalse => simp at h
      rename_i hal
      split at h
      case h_2 => simp at h
      rename_i k' hk'
      unfold both at h
      split at h
      case h_2 => simp at h
      rename_i e₁ o₁ e₂ o₂ h₁ h₂
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      have hra := (hm.2.2.1 rs1).symm
      have hrb := (hm.2.2.1 rs2).symm
      refine Reach.exec_step hD' hx (hfetch _ hi) trivial ?_
      simp only [exec, jumpTo]
      cases hc : evalBr op (s.reg rs1) (s.reg rs2)
      · simp only [Bool.false_eq_true, ite_false, Reach.opt_some]
        rw [hpcS]
        exact Reach.of_explore hb hfe h₂ hd₁ hpc₁ (matches_setPc hm _) (by simpa using hx) (by simpa using ht)
          (fun x hx' => by
            simp only [List.mem_cons] at hx'
            rcases hx' with rfl | hx'
            · simp only [Cond.den]; rw [hra, hrb]; exact hc
            · exact hcs x hx')
          (fun o ho => hob o (List.mem_append_right _ ho))
          (fun e he => hN e (List.mem_append_right _ he))
      · rw [hpcS]
        simp only [ite_true, hal, Reach.opt_some]
        exact Reach.of_explore hb hfe h₁ (hfe _).symm (wordIdx_sound hk') (matches_setPc hm _) (by simpa using hx) (by simpa using ht)
          (fun x hx' => by
            simp only [List.mem_cons] at hx'
            rcases hx' with rfl | hx'
            · simp only [Cond.den]; rw [hra, hrb]; exact hc
            · exact hcs x hx')
          (fun o ho => hob o (List.mem_append_left _ ho))
          (fun e he => hN e (List.mem_append_left _ he))
    · -- jal
      rename_i rd off hi
      split at h
      case isFalse => simp at h
      rename_i hal
      split at h
      case h_2 => simp at h
      rename_i k' hk'
      refine Reach.exec_step hD' hx (hfetch _ hi) trivial ?_
      simp only [exec, jumpTo]
      rw [hpcS]
      simp only [hal, ite_true, Reach.opt_some]
      exact Reach.of_explore hb hfe h (hfe _).symm (wordIdx_sound hk')
        (matches_setReg_setPc hm rd _ _ (by first | rfl | (rw [hpcS]; rfl)) _) (by simpa using hx) (by simpa using ht) hcs hob hN
    · -- jalr: the return, or a jump to a known address
      rename_i rd rs1 off hi
      split at h
      · rename_i hc; obtain ⟨rfl, rfl, rfl⟩ := hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hal, hq⟩ := hN _ (List.mem_singleton_self _) hcs s hm hx
        have h1 := (hm.2.2.1 1).symm
        rw [h1] at hal hq
        refine Reach.exec_step hD' hx (hfetch _ hi) trivial ?_
        have hz : s.reg 1 + BitVec.signExtend 64 (0 : BitVec 12) = s.reg 1 := by
          rw [show BitVec.signExtend 64 (0 : BitVec 12) = 0 by decide]; bv_omega
        simp only [exec, jumpTo, setReg_x0', hz, hal, ite_true, Reach.opt_some]
        exact .done (hq (by simpa using ht))
      · split at h
        case h_2 => simp at h
        rename_i v hv
        split at h
        case isFalse => simp at h
        rename_i hal
        split at h
        case h_2 => simp at h
        rename_i k' hk'
        have hrs : s.reg rs1 = v := by rw [hm.2.2.1 rs1, hv]; rfl
        refine Reach.exec_step hD' hx (hfetch _ hi) trivial ?_
        simp only [exec, jumpTo, hrs]
        simp only [hal, ite_true, Reach.opt_some]
        exact Reach.of_explore hb hfe h (hfe _).symm (wordIdx_sound hk')
          (matches_setReg_setPc hm rd _ _ (by first | rfl | (rw [hpcS]; rfl)) _) (by simpa using hx) (by simpa using ht) hcs hob hN
    · -- a straight-line instruction
      rename_i i _ _ _ hi
      split at h
      case h_2 => simp at h
      rename_i S₁ o₁ hst
      cases hr : explore c D cuts fetch fuel false (k + 1) ws' S₁ cs with
      | none => rw [hr] at h; simp at h
      | some p =>
        obtain ⟨e₂, o₂⟩ := p
        rw [hr] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨s₁, he, hok, hm₁⟩ := sstep_sound (P := P) hm hst
          (fun o ho => hob o (List.mem_append_left _ ho))
        have hS₁ : S₁.pc = c.base + BitVec.ofNat 64 (4 * (k + 1)) := by
          rw [← hpc₁]
          cases i <;> simp only [sstep, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hst <;>
            (try obtain ⟨rfl, rfl⟩ := hst) <;> rfl
        exact NoCompiler.Reach.exec_step hD' hx (hfetch _ hi) hok
          (by rw [he, NoCompiler.Reach.opt_some]
              exact Reach.of_explore hb hfe hr hd₁ hS₁ hm₁ ((exec_exit he).trans hx) ((exec_trace he).trans ht) hcs
                (fun o ho => hob o (List.mem_append_right _ ho)) hN)
    · simp at h

/-- Every end's condition, as one conjunction (so that its goals split by `refine ⟨?_, …⟩`). -/
def allNext (ρ : Nat → Word) (μ : Word → Byte) (Q : State → Prop) : List PEnd → Prop
  | [] => True
  | e :: es => e.Next ρ μ Q ∧ allNext ρ μ Q es

theorem allNext_mem {ρ : Nat → Word} {μ : Word → Byte} {Q : State → Prop} :
    ∀ {es : List PEnd}, allNext ρ μ Q es → ∀ e ∈ es, e.Next ρ μ Q
  | [], _, _, h => by simp at h
  | _ :: _, ⟨h₁, h₂⟩, _, h => by
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact h₁
    · exact allNext_mem h₂ _ h

/-- Every obligation, as one conjunction. -/
def allOb (ρ : Nat → Word) (μ : Word → Byte) (P : Perm) : List Ob → Prop
  | [] => True
  | o :: os => o.den ρ μ P ∧ allOb ρ μ P os

theorem allOb_mem {ρ : Nat → Word} {μ : Word → Byte} {P : Perm} :
    ∀ {os : List Ob}, allOb ρ μ P os → ∀ o ∈ os, o.den ρ μ P
  | [], _, _, h => by simp at h
  | _ :: _, ⟨h₁, h₂⟩, _, h => by
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact h₁
    · exact allOb_mem h₂ _ h

/-- The paths from `p` (word `k`), with the obligations the checker does not
    discharge from `facts`: what is left of them is the caller's. -/
def exploreR (c : Code) (D : Dom) (cuts : List Word) (fetch : Nat → List (BitVec 32)) (fuel k : Nat)
    (p : Word) (facts : List Fact) : Option (List PEnd × List Ob) :=
  (explore c D cuts fetch fuel true k (fetch k) (SState.init p) []).map
    fun r => (r.1, r.2.filter fun o => !o.check facts)

/-- One cut point's verification condition: every path from `p` (word `k`) to
    the next cut points and returns; the obligations the checker leaves; and
    each end's condition. -/
def exploreVC (ρ : Nat → Word) (μ : Word → Byte) (P : Perm) (Q : State → Prop) (facts : List Fact)
    (c : Code) (D : Dom) (cuts : List Word) (fuel k : Nat) (p : Word)
    (fetch : Nat → List (BitVec 32) := fun k => c.words.toList.drop k) : Prop :=
  match exploreR c D cuts fetch fuel k p facts with
  | some (ends, res) => allOb ρ μ P res ∧ allNext ρ μ Q ends
  | none => False

theorem Reach.of_exploreAt {c : Code} {P : Perm} {D : Dom} {Q : State → Prop} {facts : List Fact}
    {cuts : List Word} {fuel k : Nat} {p : Word} {s : State} (hb : 4 * c.words.size < 2 ^ 64)
    (hk : p = c.base + BitVec.ofNat 64 (4 * k)) (hpc : s.pc = p) (hx : s.exit = none)
    (hf : ∀ f ∈ facts, f.den (ρOf s) P) (hvc : exploreVC (ρOf s) s.mem P Q facts c D cuts fuel k p) :
    Reach c P D Q s := by
  unfold exploreVC exploreR at hvc
  cases h : explore c D cuts (fun k => c.words.toList.drop k) fuel true k (c.words.toList.drop k)
      (SState.init p) [] with
  | none => rw [h] at hvc; exact hvc.elim
  | some r =>
    obtain ⟨ends, obs⟩ := r
    rw [h] at hvc
    simp only [Option.map_some] at hvc
    refine Reach.of_explore (τ := s.trace) hb (fun _ => rfl) h rfl hk (matches_init hpc) hx rfl (by simp)
      (fun o ho => ?_) (fun e he => PEnd.Next.weaken (allNext_mem hvc.2 e he))
    cases hc : o.check facts
    · exact allOb_mem hvc.1 o (List.mem_filter.2 ⟨ho, by simp [hc]⟩)
    · exact Ob.check_sound hf hc

/-- As `Reach.of_exploreAt`, with the trace at every end known: the start's
    (a path between cut points makes no syscall). -/
theorem Reach.of_exploreAtT {c : Code} {P : Perm} {D : Dom} {Q : State → Prop} {facts : List Fact}
    {cuts : List Word} {fuel k : Nat} {p : Word} {s : State} {fetch : Nat → List (BitVec 32)}
    (hb : 4 * c.words.size < 2 ^ 64) (hfe : ∀ k, fetch k = c.words.toList.drop k)
    (hk : p = c.base + BitVec.ofNat 64 (4 * k)) (hpc : s.pc = p) (hx : s.exit = none)
    (hf : ∀ f ∈ facts, f.den (ρOf s) P)
    (hvc : exploreVC (ρOf s) s.mem P (fun s' => s'.trace = s.trace → Q s') facts c D cuts fuel k p fetch) :
    Reach c P D Q s := by
  unfold exploreVC exploreR at hvc
  cases h : explore c D cuts fetch fuel true k (fetch k) (SState.init p) [] with
  | none => rw [h] at hvc; exact hvc.elim
  | some r =>
    obtain ⟨ends, obs⟩ := r
    rw [h] at hvc
    simp only [Option.map_some] at hvc
    refine Reach.of_explore (τ := s.trace) hb hfe h (hfe k).symm hk (matches_init hpc) hx rfl (by simp)
      (fun o ho => ?_) (allNext_mem hvc.2)
    cases hc : o.check facts
    · exact allOb_mem hvc.1 o (List.mem_filter.2 ⟨ho, by simp [hc]⟩)
    · exact Ob.check_sound hf hc

end NoCompiler.VC.M
