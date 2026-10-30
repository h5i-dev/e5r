/-
  **encode_frame, proved**: `encode_spec : EncPre m₀ → Lands B img (EncPost m₀) m₀` for the
  actual code at 0x80008d5c on the pinned RMK image, callees included. It follows from the kernel
  run `enc_check` (Encode.lean) through the executor's soundness (`Sym.check_sound`). Non-vacuity:
  a concrete machine with the observed call-site layout satisfies `EncPre` (`encPre_witness`), and
  some real run from it reaches `EncPost` (`encode_reaches`).

  Original e5r code, Apache-2.0.
-/
import Projects.rmk.Encode.Encode

set_option maxRecDepth 100000

namespace E5R.Rmk.Encode
open E5R E5R.Rmk E5R.Rmk.Sym

/-- The entry registers as a valuation. -/
def valR (m : Machine) : Nat → Word := fun q => if h : q < 32 then m.core.get ⟨q, h⟩ else 0

theorem valR_reg (m : Machine) (q : Reg) : valR m q.val = m.core.get q := by
  simp [valR, q.isLt]

theorem valR_sp (m : Machine) : valR m 2 = m.core.get 2 := valR_reg m 2

theorem mkLin_sp (m : Machine) (o : Word) : (mkLin (some 2, o)).eval (valR m) m.ram = m.core.get 2 + o := by
  rw [mkLin_eval]; simp only [baseVal, valR_sp]

/-- The response byte cell is unchanged by rewriting it with its own value. -/
theorem init_mem (m₀ : Machine) (r : Nat) (hr : (m₀.ram (m₀.core.get 2 + 0x00000140#32)).toNat = r) :
    applyW (valR m₀) m₀.ram [initW r] = m₀.ram := by
  funext x
  simp only [applyW, initW, A140, mkLin_sp, SE.eval, ramWrite, ramPut]
  split
  · rename_i hx; subst hx
    apply BitVec.eq_of_toNat_eq
    rw [byteOf_toNat, BitVec.toNat_ofNat, ← hr]
    have := (m₀.ram (m₀.core.get 2 + 0x00000140#32)).isLt
    omega
  · rfl

theorem rel_init (m₀ : Machine) (h : EncPre m₀) (r : Nat)
    (hr : (m₀.ram (m₀.core.get 2 + 0x00000140#32)).toNat = r) :
    Rel (valR m₀) m₀.ram m₀.core (init r) m₀ := by
  refine ⟨h.pc, fun q => ?_, (init_mem m₀ r hr).symm, Core.sameCsr_refl _⟩
  simp only [AS.get, init, initR]
  by_cases h0 : q.val = 0
  · have : q = 0 := Fin.ext h0
    subst this; simp [SE.eval]
  · rw [if_neg h0]
    by_cases h1 : q.val = 1
    · rw [if_pos h1]; have : q = 1 := Fin.ext h1; subst this; exact h.ra
    rw [if_neg h1]
    by_cases h10 : q.val = 10
    · rw [if_pos h10]; have : q = 10 := Fin.ext h10; subst this; rw [A40, mkLin_sp]; exact h.out
    rw [if_neg h10]
    by_cases h11 : q.val = 11
    · rw [if_pos h11]; have : q = 11 := Fin.ext h11; subst this; exact h.buf
    rw [if_neg h11]
    by_cases h12 : q.val = 12
    · rw [if_pos h12]; have : q = 12 := Fin.ext h12; subst this; exact h.cap
    rw [if_neg h12]
    by_cases h15 : q.val = 15
    · rw [if_pos h15]; have : q = 15 := Fin.ext h15; subst this; rw [A140, mkLin_sp]; exact h.arg
    rw [if_neg h15, SE.eval, valR_reg]

theorem spIn (m₀ : Machine) (h : EncPre m₀) : SpIn encE (valR m₀) := by
  have := h.sp
  simp only [SpIn, encE, valR_sp]
  omega

/-- A write that `inW` accepts lies in `EncW`. -/
theorem inW_sound {m₀ : Machine} (h : EncPre m₀) {a : SE} {w : Width} (hw : inW encE a w = true) :
    ∀ j < w.bytes, EncW (m₀.core.get 2) (a.eval (valR m₀) m₀.ram + BitVec.ofNat 32 j) := by
  intro j hj
  unfold inW at hw
  have hs := spIn m₀ h
  split at hw
  · rename_i k hk
    have e := nform_sound (M := m₀.ram) hs hk j hj
    simp only [ite_true, valR_sp] at e
    simp only [decide_eq_true_eq] at hw
    unfold EncW
    omega
  · rename_i k hk
    have e := nform_sound (M := m₀.ram) hs hk j hj
    simp only [Bool.false_eq_true, ite_false] at e
    simp only [decide_eq_true_eq] at hw
    unfold EncW
    omega
  · simp at hw

theorem applyW_append_other (R : Nat → Word) (M : Word → BitVec 8) (x : Word) :
    ∀ (xs ys : List Wr), (∀ p ∈ xs, ∀ j < p.2.1.bytes, x ≠ p.1.eval R M + BitVec.ofNat 32 j) →
      applyW R M (xs ++ ys) x = applyW R M ys x := by
  intro xs ys h
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    obtain ⟨a, w, v⟩ := p
    simp only [List.cons_append, applyW]
    rw [ramWrite_other _ _ _ _ _ (h _ (List.mem_cons_self ..)), ih fun q hq => h q (List.mem_cons_of_mem _ hq)]

theorem leaf_sound (m₀ : Machine) (h : EncPre m₀) (r : Nat)
    (hr : (m₀.ram (m₀.core.get 2 + 0x00000140#32)).toNat = r) :
    ∀ s m, leafE r s = true → Rel (valR m₀) m₀.ram m₀.core s m → EncPost m₀ m := by
  intro s m hl hR
  simp only [leafE, Bool.and_eq_true, beq_iff_eq] at hl
  obtain ⟨⟨⟨⟨hpc, hsv⟩, hlast⟩, hin⟩, hres⟩ := hl
  have hs := spIn m₀ h
  refine ⟨by rw [hR.pc, hpc], Quiet.of_sameCsr hR.csr h.quiet, fun q hq => ?_, fun x hx => ?_, ?_⟩
  · have := List.all_eq_true.mp hsv q.val hq
    simp only [q.isLt, dite_true, beq_iff_eq] at this
    rw [hR.regs, this, SE.eval, valR_reg]
  · obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hlast
    rw [hys, List.dropLast_concat] at hin
    rw [hR.mem, hys, applyW_append_other _ _ x _ _ ?_, init_mem m₀ r hr]
    intro p hp j hj e
    exact hx (e ▸ inW_sound h (List.all_eq_true.mp hin p hp) j hj)
  · unfold resOK at hres
    split at hres
    · rename_i t ht
      have e40 := rdW_sound (M := m₀.ram) hs _ _ _ _ ht
      rw [← hR.mem, A40, mkLin_sp] at e40
      have t40 : (m.ram (m₀.core.get 2 + 0x00000040#32)).toNat = t.toNat := by
        rw [← ramRead_b, e40]; rfl
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hres
      rcases hres with h1 | ⟨h0, h44⟩
      · exact .inl (t40.trans h1)
      · refine .inr ⟨t40.trans h0, ?_⟩
        split at h44
        · rename_i l hl44
          have e44 := rdW_sound (M := m₀.ram) hs _ _ _ _ hl44
          rw [← hR.mem, A44, mkLin_sp] at e44
          rw [e44]
          simpa [SE.eval] using h44
        · simp at h44
    · simp at hres

/-- **encode_frame meets its contract** (actual code, callees included). -/
theorem encode_spec (m₀ : Machine) (h : EncPre m₀) : Lands B img (EncPost m₀) m₀ := by
  have hr : (m₀.ram (m₀.core.get 2 + 0x00000140#32)).toNat ∈ respVals := by
    have := h.resp
    simp only [respVals, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hc := List.all_eq_true.mp enc_check _ hr
  have hsp : (valR m₀ 2).toNat % 4 = 0 := by rw [valR_sp]; exact h.spAl
  exact check_sound (spIn m₀ h) hsp (tblOK_sound _ encTbl_ok) (rtOK_sound _ encRom_ok) h.quiet
    (leaf_sound m₀ h _ rfl) 600 _ m₀ (rel_init m₀ h _ rfl) hc

/-! ## Non-vacuity -/

/-- The observed call site: sp = 0x80fffe10 (as at the session loop), response byte 8, an
    arbitrary header. -/
def witCore : Core where
  pc := 0x80008d5c
  x := fun r => if r.val = 1 then 0x80003f1e else if r.val = 2 then 0x80fffe10
    else if r.val = 10 then 0x80fffe50 else if r.val = 11 then 0x8002a7b1 else if r.val = 12 then 7
    else if r.val = 13 then 0x0201 else if r.val = 14 then 5 else if r.val = 15 then 0x80ffff50 else 0
  mie_ := false
  mpie := false
  mpp := 3
  mieReg := 0
  mtvec := 0x800000f8
  mepc := 0
  mcause := 0
  mscratch := 0
  resv := false

def witMachine : Machine := ⟨witCore, fun a => if a = 0x80ffff50 then 8 else 0⟩

theorem encPre_witness : EncPre witMachine :=
  ⟨rfl, fun code => by simp [irqEnabled, witMachine, witCore], by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

theorem reach_cons {m m' : Machine} {e : List Event}
    (hs : Step B img m m' e) : ∀ {x evs}, Reach B img (· = m') x evs → Reach B img (· = m) x (e ++ evs) := by
  intro x evs h
  induction h with
  | init h0 => subst h0; simpa using (Reach.step (Reach.init rfl) hs : Reach B img (· = m) _ ([] ++ e))
  | step _ hs' ih => rw [← List.append_assoc]; exact .step ih hs'

theorem lands_hits {P : Machine → Prop} :
    ∀ {m}, Lands B img P m → ∃ x evs, Reach B img (· = m) x evs ∧ P x := by
  intro m h
  induction h with
  | done hp => exact ⟨_, [], .init rfl, hp⟩
  | @step m hq hf _ ih =>
    cases hr : stepInstr B img m (fun _ => 0) with
    | fault f => exact absurd hr (hf _ f)
    | ok c ram evs =>
      obtain ⟨x, evs', hx, hp⟩ := ih ⟨c, ram⟩ evs (.instr _ hr)
      exact ⟨x, _, reach_cons (.instr _ hr) hx, hp⟩

/-- Some real run of encode_frame from the witness returns with its postcondition. -/
theorem encode_reaches : ∃ x evs, Reach B img (· = witMachine) x evs ∧ EncPost witMachine x :=
  lands_hits (encode_spec _ encPre_witness)

end E5R.Rmk.Encode
