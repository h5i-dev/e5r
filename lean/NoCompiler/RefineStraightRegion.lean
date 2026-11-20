import NoCompiler.RefineStraight
import NoCompiler.RefineRegion
import NoCompiler.Arith

/-
A straight-line region is a region (C's `RRegion.Ok`, NoCompiler/RefineRegion.lean):
item 6 discharges the regions item 5's diff finds when both sides of a
changed interval are runs of register instructions.

`RRegion.ok_of_seqEquiv`: if A's interval holds the sequence `as` from `pa`
(and nothing else: `domA` is exactly those words, `paExit` just past them),
B's holds `bs` likewise, `as` does not write `ra`, and `SeqEquiv liveIn
liveOut as bs`, then the region is Ok, with no entry condition.
-/
namespace NoCompiler

/-- The code holds `is` from `p`. -/
def Code.holds (c : Code) (p : Word) (is : List Instr) : Prop :=
  ∀ k (h : k < is.length), c.instr (p + BitVec.ofNat 64 (4 * k)) = some is[k]

instance (c : Code) (p : Word) (is : List Instr) : Decidable (c.holds p is) :=
  inferInstanceAs (Decidable (∀ k (h : k < is.length), _))

theorem instrOk_of_alu {i : Instr} (hi : i.alu = true) (P : Perm) (s : State) : InstrOk P i s := by
  cases i <;> simp [Instr.alu] at hi <;> trivial

/-- A step at a register instruction is the one `exec` takes. -/
theorem step_alu {c : Code} {P : Perm} {i : Instr} (hi : i.alu = true) {s t : State}
    (hc : c.instr s.pc = some i) (h : Step c P s t) : exec i s = some t := by
  cases h with
  | exec _ hc' _ hx => rw [hc] at hc'; cases hc'; exact hx
  | sys _ hc' _ _ => rw [hc] at hc'; cases hc'; simp [Instr.alu] at hi

/-- Running a sequence of register instructions held by the code, inside `D`:
    there is a run to where `execSeq` ends, and every run gets there. -/
theorem seq_reach {c : Code} {P : Perm} {D : Dom} : ∀ {is : List Instr} {p : Word},
    (∀ i ∈ is, i.alu = true) → c.holds p is →
    (∀ k, k < is.length → D.mem (p + BitVec.ofNat 64 (4 * k))) →
    ∀ s t, s.pc = p → s.exit = none → execSeq is s = some t →
      Run c P D s t ∧ ∀ Q : State → Prop, Q t → Reach c P D Q s
  | [], _, _, _, _, s, t, _, _, he => by
    cases he; exact ⟨.refl _, fun _ hq => .done hq⟩
  | i :: is, p, ha, hc, hD, s, t, hp, hx, he => by
    have hi := ha i List.mem_cons_self
    obtain ⟨rd, v, _, hex⟩ := exec_alu hi s
    have hc0 : c.instr s.pc = some i := by
      have := hc 0 (by simp); simp only [List.getElem_cons_zero] at this; simpa [hp] using this
    have hd0 : D.mem s.pc := by simpa [hp] using hD 0 (by simp)
    have hstep : Step c P s ((s.setReg rd v).setPc (s.pc + 4)) :=
      .exec hx hc0 (instrOk_of_alu hi P s) hex
    rw [execSeq, hex, Option.bind_some] at he
    have hc' : c.holds (p + 4) is := by
      intro k hk
      have := hc (k + 1) (by simp; omega)
      rw [show p + 4 + BitVec.ofNat 64 (4 * k) = p + BitVec.ofNat 64 (4 * (k + 1)) by bv_omega]
      simpa using this
    have hD' : ∀ k, k < is.length → D.mem (p + 4 + BitVec.ofNat 64 (4 * k)) := by
      intro k hk
      rw [show p + 4 + BitVec.ofNat 64 (4 * k) = p + BitVec.ofNat 64 (4 * (k + 1)) by bv_omega]
      exact hD (k + 1) (by simp; omega)
    obtain ⟨hr, hq⟩ := seq_reach (fun j hj => ha j (List.mem_cons_of_mem _ hj)) hc' hD' _ t
      (by simp [hp]) (by simpa using hx) he
    refine ⟨.step hd0 hstep hr, fun Q hQ => .step hd0 ⟨_, hstep⟩ (fun t' ht' => ?_)⟩
    rw [step_alu hi hc0 ht'] at hex
    cases hex
    exact hq Q hQ

/-- The words of a sequence, as a region of code. -/
def seqDom (p : Word) (is : List Instr) : Dom := [(p, 4 * is.length)]

theorem seqDom_mem {p : Word} {is : List Instr} (hn : 4 * is.length < 2 ^ 64) {k : Nat}
    (hk : k < is.length) : (seqDom p is).mem (p + BitVec.ofNat 64 (4 * k)) := by
  simp only [seqDom, Dom.mem, List.any_cons, List.any_nil, Bool.or_false, decide_eq_true_eq]
  rw [add_ofNat_sub_toNat p (by omega)]; omega

theorem seqDom_end {p : Word} {is : List Instr} (hn : 4 * is.length < 2 ^ 64) :
    ¬ (seqDom p is).mem (p + BitVec.ofNat 64 (4 * is.length)) := by
  simp only [seqDom, Dom.mem, List.any_cons, List.any_nil, Bool.or_false, decide_eq_true_eq]
  rw [add_ofNat_sub_toNat p hn]; omega

/-- A register instruction that does not write `ra`. -/
def Instr.keepsRa (i : Instr) : Bool := !(i.defs.contains 1)

theorem runRegs_ra : ∀ {is : List Instr}, (∀ i ∈ is, i.keepsRa = true) → ∀ g : RegFile,
    (runRegs is g).get 1 = g.get 1
  | [], _, _ => rfl
  | i :: is, h, g => by
    simp only [runRegs]
    rw [runRegs_ra (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    have hk := h i List.mem_cons_self
    split
    · rename_i rd v ho
      have : rd ≠ 1 := by
        intro e; subst e
        cases i <;> simp [Instr.aluOut] at ho <;> simp_all [Instr.keepsRa, Instr.defs]
      simp [RegFile.get, RegFile.set, Ne.symm this]
    · rfl

/-- Item 6 for C's regions: a straight-line region whose two sides are
    equivalent sequences is Ok. -/
theorem RRegion.ok_of_seqEquiv {cA cB : Code} {r : RRegion} {as bs : List Instr}
    (hea : ∀ i ∈ as, i.alu = true) (heb : ∀ i ∈ bs, i.alu = true)
    (hra : ∀ i ∈ as, i.keepsRa = true)
    (hna : 4 * as.length < 2 ^ 64) (hnb : 4 * bs.length < 2 ^ 64)
    (hca : cA.holds r.pa as) (hcb : cB.holds r.pb bs)
    (hda : r.domA = seqDom r.pa as) (hdb : r.domB = seqDom r.pb bs)
    (hxa : r.paExit = r.pa + BitVec.ofNat 64 (4 * as.length))
    (hxb : r.pbExit = r.pb + BitVec.ofNat 64 (4 * bs.length))
    (h : SeqEquiv r.liveIn r.liveOut as bs) : r.Ok cA cB := by
  intro P sa sb hx hpa hpb hag _ _
  obtain ⟨ta, tb, ea, eb, hagr, pa, pb⟩ := h.agree hea heb hag
  obtain ⟨ra, -⟩ := seq_reach (P := P) (D := r.domA) hea hca
    (fun k hk => hda ▸ seqDom_mem hna hk) sa ta hpa hx ea
  obtain ⟨-, qb⟩ := seq_reach (P := P) (D := r.domB) heb hcb
    (fun k hk => hdb ▸ seqDom_mem hnb hk) sb tb hpb (by rw [← hag.exit]; exact hx) eb
  -- What execSeq says of A's end state.
  obtain ⟨ta', ea', rra, -, -, xa, -⟩ := execSeq_alu hea sa
  rw [ea] at ea'; cases ea'
  have hfa : ¬ r.domA.mem ta.pc := by rw [pa, hpa, hda]; exact seqDom_end hna
  have hfb : ¬ r.domB.mem tb.pc := by rw [pb, hpb, hdb]; exact seqDom_end hnb
  refine qb _ ⟨.inl hfb, ta, ra, .inl hfa, .inl ⟨by rw [xa, hx], by rw [pa, hpa, hxa], by rw [pb, hpb, hxb],
    ?_, hagr⟩⟩
  rw [rra 1, runRegs_ra hra, RegFile.get_regFile]

end NoCompiler
