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
def explore (c : Code) (D : Dom) (cuts : List Word) :
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
              both (explore c D cuts fuel false k' (c.words.toList.drop k') { S with pc := t }
                  (⟨op, S.reg rs1, S.reg rs2, true⟩ :: cs))
                (explore c D cuts fuel false (k + 1) ws' { S with pc := S.pc + 4 }
                  (⟨op, S.reg rs1, S.reg rs2, false⟩ :: cs))
            | none => none
          else none
        | some (.jal rd off) =>
          let t := S.pc + off.signExtend 64
          if rd = 0 ∧ aligned t 4 then
            match wordIdx c t with
            | some k' => explore c D cuts fuel false k' (c.words.toList.drop k') { S with pc := t } cs
            | none => none
          else none
        | some (.jalr rd rs1 off) => if rd = 0 ∧ rs1 = 1 ∧ off = 0 then some ([.ret S cs], []) else none
        | some i =>
          match sstep i S with
          | some (S₁, o₁) => (explore c D cuts fuel false (k + 1) ws' S₁ cs).map fun p => (p.1, o₁ ++ p.2)
          | none => none
        | none => none
    else none

theorem matches_setPc {ρ : Nat → Word} {μ : Word → Byte} {S : SState} {s : State} (hm : Matches ρ μ S s)
    (t : Word) : Matches ρ μ { S with pc := t } (s.setPc t) :=
  ⟨hm.1, rfl, fun r => (State.setPc_reg s t r).trans (hm.2.2.1 r), (State.setPc_mem s t).trans hm.2.2.2⟩

theorem pc_succ {b : Word} {k : Nat} (h : 4 * (k + 1) < 2 ^ 64) :
    b + BitVec.ofNat 64 (4 * k) + 4 = b + BitVec.ofNat 64 (4 * (k + 1)) := by
  rw [BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq
  have h4 : (4 : Word).toNat = 4 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h4]
  omega

/-- `explore`, sound. -/
theorem Reach.of_explore {ρ : Nat → Word} {μ : Word → Byte} {c : Code} {P : Perm} {D : Dom}
    {Q : State → Prop} {cuts : List Word} (hb : 4 * c.words.size < 2 ^ 64) :
    ∀ {fuel : Nat} {first : Bool} {k : Nat} {ws : List (BitVec 32)} {S : SState} {cs : List Cond}
      {ends : List PEnd} {obs : List Ob} {s : State},
      explore c D cuts fuel first k ws S cs = some (ends, obs) →
      c.words.toList.drop k = ws → S.pc = c.base + BitVec.ofNat 64 (4 * k) → Matches ρ μ S s →
      s.exit = none → (∀ x ∈ cs, x.den ρ μ) → (∀ o ∈ obs, o.den ρ μ P) →
      (∀ e ∈ ends, e.Next ρ μ Q) → Reach c P D Q s
  | 0, _, _, _, _, _, _, _, _, h, _, _, _, _, _, _, _ => by simp [explore] at h
  | fuel + 1, first, k, ws, S, cs, ends, obs, s, h, hd, hpc, hm, hx, hcs, hob, hN => by
    simp only [explore] at h
    split at h
    · -- a cut point
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact .done (hN _ (List.mem_singleton_self _) hcs s hm hx)
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
        exact Reach.of_explore hb h₂ hd₁ hpc₁ (matches_setPc hm _) (by simpa using hx)
          (fun x hx' => by
            simp only [List.mem_cons] at hx'
            rcases hx' with rfl | hx'
            · simp only [Cond.den]; rw [hra, hrb]; exact hc
            · exact hcs x hx')
          (fun o ho => hob o (List.mem_append_right _ ho))
          (fun e he => hN e (List.mem_append_right _ he))
      · rw [hpcS]
        simp only [ite_true, hal, Reach.opt_some]
        exact Reach.of_explore hb h₁ rfl (wordIdx_sound hk') (matches_setPc hm _) (by simpa using hx)
          (fun x hx' => by
            simp only [List.mem_cons] at hx'
            rcases hx' with rfl | hx'
            · simp only [Cond.den]; rw [hra, hrb]; exact hc
            · exact hcs x hx')
          (fun o ho => hob o (List.mem_append_left _ ho))
          (fun e he => hN e (List.mem_append_left _ he))
    · -- jal zero
      rename_i rd off hi
      split at h
      case isFalse => simp at h
      rename_i hc; obtain ⟨rfl, hal⟩ := hc
      split at h
      case h_2 => simp at h
      rename_i k' hk'
      refine Reach.exec_step hD' hx (hfetch _ hi) trivial ?_
      simp only [exec, jumpTo, setReg_x0']
      rw [hpcS]
      simp only [hal, ite_true, Reach.opt_some]
      exact Reach.of_explore hb h rfl (wordIdx_sound hk') (matches_setPc hm _) (by simpa using hx) hcs hob hN
    · -- jalr zero, 0(ra)
      rename_i rd rs1 off hi
      split at h
      case isFalse => simp at h
      rename_i hc; obtain ⟨rfl, rfl, rfl⟩ := hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hal, hq⟩ := hN _ (List.mem_singleton_self _) hcs s hm hx
      have h1 := (hm.2.2.1 1).symm
      rw [h1] at hal hq
      refine Reach.exec_step hD' hx (hfetch _ hi) trivial ?_
      have hz : s.reg 1 + BitVec.signExtend 64 (0 : BitVec 12) = s.reg 1 := by
        rw [show BitVec.signExtend 64 (0 : BitVec 12) = 0 by decide]; bv_omega
      simp only [exec, jumpTo, setReg_x0', hz, hal, ite_true, Reach.opt_some]
      exact .done hq
    · -- a straight-line instruction
      rename_i i _ _ _ hi
      split at h
      case h_2 => simp at h
      rename_i S₁ o₁ hst
      cases hr : explore c D cuts fuel false (k + 1) ws' S₁ cs with
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
              exact Reach.of_explore hb hr hd₁ hS₁ hm₁ ((exec_exit he).trans hx) hcs
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

/-- One cut point's verification condition: every path from `p` (word `k`) to
    the next cut points and returns, its obligations checked from the facts,
    and each end's condition. -/
def exploreVC (ρ : Nat → Word) (μ : Word → Byte) (Q : State → Prop) (facts : List Fact) (c : Code)
    (D : Dom) (cuts : List Word) (fuel k : Nat) (p : Word) : Prop :=
  match explore c D cuts fuel true k (c.words.toList.drop k) (SState.init p) [] with
  | some (ends, obs) => obs.all (Ob.check facts) = true ∧ allNext ρ μ Q ends
  | none => False

theorem Reach.of_exploreAt {c : Code} {P : Perm} {D : Dom} {Q : State → Prop} {facts : List Fact}
    {cuts : List Word} {fuel k : Nat} {p : Word} {s : State} (hb : 4 * c.words.size < 2 ^ 64)
    (hk : p = c.base + BitVec.ofNat 64 (4 * k)) (hpc : s.pc = p) (hx : s.exit = none)
    (hf : ∀ f ∈ facts, f.den (ρOf s) P) (hvc : exploreVC (ρOf s) s.mem Q facts c D cuts fuel k p) :
    Reach c P D Q s := by
  unfold exploreVC at hvc
  split at hvc
  · rename_i ends obs h
    exact Reach.of_explore hb h rfl hk (matches_init hpc) hx (by simp)
      (fun o ho => Ob.check_sound hf (List.all_eq_true.1 hvc.1 o ho)) (allNext_mem hvc.2)
  · exact hvc.elim

end NoCompiler.VC.M
