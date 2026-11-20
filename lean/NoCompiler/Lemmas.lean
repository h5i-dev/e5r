import NoCompiler.Step

/-! Rewriting lemmas for states, used by every proof and by the step tactics. -/
namespace NoCompiler
namespace State

@[simp] theorem setReg_pc (s : State) (r v) : (s.setReg r v).pc = s.pc := by
  unfold setReg; split <;> rfl
@[simp] theorem setReg_mem (s : State) (r v) : (s.setReg r v).mem = s.mem := by
  unfold setReg; split <;> rfl
@[simp] theorem setReg_trace (s : State) (r v) : (s.setReg r v).trace = s.trace := by
  unfold setReg; split <;> rfl
@[simp] theorem setReg_exit (s : State) (r v) : (s.setReg r v).exit = s.exit := by
  unfold setReg; split <;> rfl

@[simp] theorem setPc_pc (s : State) (p) : (s.setPc p).pc = p := rfl
@[simp] theorem setPc_mem (s : State) (p) : (s.setPc p).mem = s.mem := rfl
@[simp] theorem setPc_trace (s : State) (p) : (s.setPc p).trace = s.trace := rfl
@[simp] theorem setPc_exit (s : State) (p) : (s.setPc p).exit = s.exit := rfl
@[simp] theorem setPc_reg (s : State) (p r) : (s.setPc p).reg r = s.reg r := rfl

@[simp] theorem setMem_pc (s : State) (m) : (s.setMem m).pc = s.pc := rfl
@[simp] theorem setMem_mem (s : State) (m) : (s.setMem m).mem = m := rfl
@[simp] theorem setMem_trace (s : State) (m) : (s.setMem m).trace = s.trace := rfl
@[simp] theorem setMem_exit (s : State) (m) : (s.setMem m).exit = s.exit := rfl
@[simp] theorem setMem_reg (s : State) (m r) : (s.setMem m).reg r = s.reg r := rfl

@[simp] theorem emit_pc (s : State) (e) : (s.emit e).pc = s.pc := rfl
@[simp] theorem emit_mem (s : State) (e) : (s.emit e).mem = s.mem := rfl
@[simp] theorem emit_trace (s : State) (e) : (s.emit e).trace = s.trace ++ [e] := rfl
@[simp] theorem emit_exit (s : State) (e) : (s.emit e).exit = s.exit := rfl
@[simp] theorem emit_reg (s : State) (e r) : (s.emit e).reg r = s.reg r := rfl

@[simp] theorem halt_pc (s : State) (e) : (s.halt e).pc = s.pc := rfl
@[simp] theorem halt_mem (s : State) (e) : (s.halt e).mem = s.mem := rfl
@[simp] theorem halt_trace (s : State) (e) : (s.halt e).trace = s.trace := rfl
@[simp] theorem halt_exit (s : State) (e) : (s.halt e).exit = some e := rfl
@[simp] theorem halt_reg (s : State) (e r) : (s.halt e).reg r = s.reg r := rfl

@[simp] theorem reg_zero (s : State) : s.reg 0 = 0 := rfl

theorem reg_setReg (s : State) (r v q) :
    (s.setReg r v).reg q = if q = 0 then 0 else if q = r then v else s.reg q := by
  unfold setReg reg upd
  by_cases hr : r = 0
  · subst hr; by_cases hq : q = 0 <;> simp [hq]
  · simp only [hr, ite_false]; by_cases hq : q = 0 <;> simp [hq]

/-- The same register, for the step tactics: `q` and `r` are literals there. -/
@[simp] theorem reg_setReg_same (s : State) (r v) (h : r ≠ 0) : (s.setReg r v).reg r = v := by
  simp [reg_setReg, h]

@[simp] theorem reg_setReg_other (s : State) (r v q) (h : q ≠ r) :
    (s.setReg r v).reg q = s.reg q := by
  rw [reg_setReg]; by_cases hq : q = 0
  · simp [hq, reg]
  · simp [hq, h]

end State

@[simp] theorem sysRet_pc (s : State) (r) : (s.sysRet r).pc = s.pc + 4 := by simp [State.sysRet]
@[simp] theorem sysRet_mem (s : State) (r) : (s.sysRet r).mem = s.mem := by simp [State.sysRet]
@[simp] theorem sysRet_trace (s : State) (r) : (s.sysRet r).trace = s.trace := by
  simp [State.sysRet]
@[simp] theorem sysRet_exit (s : State) (r) : (s.sysRet r).exit = s.exit := by simp [State.sysRet]

/-! ## Memory -/

theorem sub_succ_toNat (x a : Word) (h : x ≠ a) : (x - (a + 1)).toNat = (x - a).toNat - 1 := by
  have : x - a ≠ 0 := by intro h'; exact h (by bv_omega)
  have h0 : (x - a).toNat ≠ 0 := fun h' => this (BitVec.eq_of_toNat_eq (by simpa using h'))
  have : x - (a + 1) = (x - a) - 1 := by bv_omega
  rw [this]; bv_omega

theorem writeLE_other (m : Word → Byte) (a : Word) (v n : Nat) (x : Word)
    (h : n ≤ (x - a).toNat) : writeLE m a v n x = m x := by
  induction n generalizing a v with
  | zero => rfl
  | succ n ih =>
    have hxa : x ≠ a := by intro e; subst e; simp at h
    simp only [writeLE, hxa, ite_false]
    exact ih _ _ (by rw [sub_succ_toNat x a hxa]; omega)

theorem writeBytes_other (m : Word → Byte) (a : Word) (bs : List Byte) (x : Word)
    (h : bs.length ≤ (x - a).toNat) : writeBytes m a bs x = m x := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    have hxa : x ≠ a := by intro e; subst e; simp at h
    simp only [writeBytes, hxa, ite_false]
    exact ih _ (by rw [sub_succ_toNat x a hxa]; simp only [List.length_cons] at h; omega)

theorem readLE_congr {m m' : Word → Byte} {a : Word} {n : Nat}
    (h : ∀ k, k < n → m (a + BitVec.ofNat 64 k) = m' (a + BitVec.ofNat 64 k)) :
    readLE m a n = readLE m' a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [readLE]
    have h0 := h 0 (by omega)
    simp only [BitVec.add_zero] at h0
    rw [h0, ih]
    intro k hk
    have := h (k + 1) (by omega)
    have e : a + 1 + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (k + 1) := by
      apply BitVec.eq_of_toNat_eq; simp; omega
    rw [e]; exact this

theorem Region.covers_mem {r : Region} {a x : Word} {n : Nat} (hc : r.covers a n)
    (hx : (x - a).toNat < n) : r.mem x := by
  unfold Region.covers at hc; unfold Region.mem
  have e : x - r.base = (x - a) + (a - r.base) := by bv_omega
  rw [e, BitVec.toNat_add]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)

/-! ## The frame property: a step changes no byte `P` does not let it write -/

theorem exec_frame {i : Instr} {s s' : State} (h : exec i s = some s') :
    s'.mem = s.mem ∨ ∃ op rs1 rs2 off, i = .store op rs1 rs2 off ∧
      s'.mem = writeLE s.mem (ea s rs1 off) (s.reg rs2).toNat op.width := by
  cases i with
  | store op rs1 rs2 off =>
    simp only [exec] at h; split at h
    · cases h; exact Or.inr ⟨op, rs1, rs2, off, rfl, rfl⟩
    · cases h
  | _ =>
    left
    simp only [exec, jumpTo] at h
    repeat' split at h
    all_goals (first | (cases h; simp) | cases h)

theorem exec_exit {i : Instr} {s s' : State} (h : exec i s = some s') :
    s'.exit = s.exit ∧ s'.trace = s.trace := by
  cases i <;> simp only [exec, jumpTo] at h <;>
    (try split at h) <;> (try split at h) <;> (try cases h) <;> simp

theorem LdOp.width_pos (op : LdOp) : 0 < op.width := by cases op <;> decide
theorem StOp.width_pos (op : StOp) : 0 < op.width := by cases op <;> decide

theorem Step.frame {c : Code} {P : Perm} {s s' : State} (h : Step c P s s') (x : Word)
    (hx : ¬ P.writable x) : s'.mem x = s.mem x := by
  cases h with
  | exec _ _ hok hxs =>
    rcases exec_frame hxs with e | ⟨op, rs1, rs2, off, rfl, e⟩
    · rw [e]
    · rw [e]
      apply writeLE_other
      rcases hok with h0 | ⟨r, hr, hc⟩
      · exact absurd h0 (Nat.ne_of_gt (StOp.width_pos op))
      · exact Nat.le_of_not_lt fun hlt => hx ⟨r, hr, Region.covers_mem hc hlt⟩
  | sys _ _ hok hy =>
    cases hy with
    | writeOk => simp
    | writeErr => simp
    | exit => simp
    | readErr => simp
    | readOk ds hn hlen hmax =>
      simp only [State.emit_mem, State.setMem_mem]
      apply writeBytes_other
      rcases hok.2 hn with h0 | ⟨r, hr, hc⟩
      · omega
      · exact Nat.le_of_not_lt fun hlt =>
          hx ⟨r, hr, Region.covers_mem (n := ds.length) (by unfold Region.covers at *; omega) hlt⟩

/-- Memory outside the writable regions of `P` is unchanged when a run ends. -/
theorem Reach.frame {c : Code} {P : Perm} {D : Dom} {Q : State → Prop} {s : State}
    (h : Reach c P D Q s) :
    Reach c P D (fun u => Q u ∧ ∀ x, ¬ P.writable x → u.mem x = s.mem x) s :=
  Reach.inv (I := fun u => ∀ x, ¬ P.writable x → u.mem x = s.mem x)
    (fun _ _ hu hs x hx => (hs.frame x hx).trans (hu x hx)) h (fun _ _ => rfl)

end NoCompiler
