import NoCompiler.Module

/-
Relocating a proof (docs/isa/v1.md, relocation): a function whose code
does not depend on where it is runs the same at every address.

`s.shift δ` moves the pc and the return address `ra` by `δ`. An instruction
is `pcFree` when it neither reads nor writes `ra` (other than the return
`jalr zero, 0(ra)`) and is not `auipc`: such an instruction commutes with
`shift` (`exec_shift`, `Sys.shift`). So a run of pcFree code at one address,
from a state with an aligned `ra`, is a run of the same words `δ` further
on, from the shifted state (`Reach.shift`); and a `VerifiedImg` proof of a
leaf function without relocations at one layout is a proof at every layout
(`VerifiedImg.shift`, then `Verified.of_leaf` in NoCompiler/Relocate.lean),
for a specification that does not look at the pc or `ra` (`Spec.ShiftInv`).
-/
namespace NoCompiler

def State.shift (δ : Word) (s : State) : State :=
  { s with pc := s.pc + δ, regs := State.upd s.regs 1 (s.regs 1 + δ) }

namespace State
variable (δ : Word) (s : State)

@[simp] theorem shift_pc : (s.shift δ).pc = s.pc + δ := rfl
@[simp] theorem shift_mem : (s.shift δ).mem = s.mem := rfl
@[simp] theorem shift_trace : (s.shift δ).trace = s.trace := rfl
@[simp] theorem shift_exit : (s.shift δ).exit = s.exit := rfl

theorem shift_reg {r : Reg} (h : r ≠ 1) : (s.shift δ).reg r = s.reg r := by
  simp [shift, reg, upd, h]

@[simp] theorem shift_reg_one : (s.shift δ).reg 1 = s.reg 1 + δ := by
  simp [shift, reg, upd]

theorem ext' {s t : State} (hr : s.regs = t.regs) (hp : s.pc = t.pc) (hm : s.mem = t.mem)
    (ht : s.trace = t.trace) (he : s.exit = t.exit) : s = t := by
  cases s; cases t; simp_all

@[simp] theorem shift_shift (δ ε : Word) : (s.shift δ).shift ε = s.shift (δ + ε) := by
  apply ext'
  · funext x; simp only [shift, upd]; by_cases h : x = 1 <;> simp [h, BitVec.add_assoc]
  · simp only [shift]; bv_omega
  all_goals rfl

@[simp] theorem shift_zero : s.shift 0 = s := by
  apply ext'
  · funext x; simp only [shift, upd]; by_cases h : x = 1 <;> simp [h]
  · simp [shift]
  all_goals rfl

theorem shift_neg : (s.shift δ).shift (-δ) = s := by
  rw [shift_shift, show δ + -δ = 0 by bv_omega, shift_zero]

theorem neg_shift : (s.shift (-δ)).shift δ = s := by
  rw [shift_shift, show -δ + δ = 0 by bv_omega, shift_zero]

theorem shift_setReg {r : Reg} (h : r ≠ 1) (v : Word) :
    (s.setReg r v).shift δ = (s.shift δ).setReg r v := by
  by_cases h0 : r = 0
  · simp [setReg, h0]
  · apply ext'
    · funext x; simp only [shift, setReg, h0, ite_false, upd]
      by_cases hx : x = 1 <;> by_cases hr : x = r <;> simp_all
    all_goals simp [shift, setReg, h0]

theorem shift_setPc (p : Word) : (s.setPc p).shift δ = (s.shift δ).setPc (p + δ) := rfl
theorem shift_setMem (m : Word → Byte) : (s.setMem m).shift δ = (s.shift δ).setMem m := rfl
theorem shift_emit (e : Event) : (s.emit e).shift δ = (s.shift δ).emit e := rfl
theorem shift_halt (c : Word) : (s.halt c).shift δ = (s.shift δ).halt c := rfl

theorem shift_sysRet (v : Word) : (s.sysRet v).shift δ = (s.shift δ).sysRet v := by
  unfold sysRet
  rw [shift_setPc, shift_setReg _ _ (by decide)]
  congr 1; simp only [shift_pc]; bv_omega

end State

/-! ## Instructions that do not see where they are -/

/-- Neither reads nor writes `ra` (except the return `jalr zero, 0(ra)`), and
    is not `auipc`: the instructions of a leaf function compiled in the
    profile, other than its data-address `auipc`s. -/
def Instr.pcFree : Instr → Bool
  | .lui rd _ => rd != 1
  | .auipc .. => false
  | .jal rd _ => rd == 0
  | .jalr rd rs1 off => rd == 0 && rs1 == 1 && off == 0
  | .branch _ a b _ => a != 1 && b != 1
  | .load _ rd rs1 _ => rd != 1 && rs1 != 1
  | .store _ a b _ => a != 1 && b != 1
  | .iop _ rd rs1 _ | .addiw rd rs1 _ | .shift _ rd rs1 _ | .shiftw _ rd rs1 _ | .uop _ rd rs1 =>
    rd != 1 && rs1 != 1
  | .rop _ rd a b | .rwop _ rd a b => rd != 1 && a != 1 && b != 1
  | .ecall => true

theorem aligned_add_iff {t δ : Word} (hδ : aligned δ 4) : aligned (t + δ) 4 ↔ aligned t 4 := by
  unfold aligned at *
  rw [BitVec.toNat_add, Nat.mod_mod_of_dvd _ (by decide : 4 ∣ 2 ^ 64), Nat.add_mod, hδ]
  simp

theorem jumpTo_shift {δ : Word} (hδ : aligned δ 4) (s : State) (t : Word) :
    jumpTo (s.shift δ) (t + δ) = (jumpTo s t).map (·.shift δ) := by
  unfold jumpTo
  by_cases h : aligned t 4
  · simp [h, (aligned_add_iff hδ).2 h, State.shift_setPc]
  · simp [h, mt (aligned_add_iff hδ).1 h]

/-- `x &&& ~~~1` of a 4-aligned `x` is `x`: the return address keeps its value. -/
theorem and_not_one_aligned {x : Word} (h : aligned x 4) : x &&& ~~~(1 : Word) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  by_cases h0 : i = 0
  · subst h0
    have : x.getLsbD 0 = false := by
      rw [BitVec.getLsbD, Nat.testBit_zero]; unfold aligned at h; simp; omega
    simpa [BitVec.getLsbD_eq_getElem] using this
  · have : (1#64).getLsbD i = false := by simp [BitVec.getLsbD_one, h0]
    simp [this]

theorem shift_reg_of {s : State} {δ : Word} {r : Reg} (h : (r != 1) = true) :
    (s.shift δ).reg r = s.reg r := State.shift_reg _ _ (by simpa using h)

theorem exec_shift {i : Instr} (hi : i.pcFree = true) {δ : Word} (hδ : aligned δ 4) {s : State}
    (hra : aligned (s.reg 1) 4) : exec i (s.shift δ) = (exec i s).map (·.shift δ) := by
  have next : (s.shift δ).pc + 4 = (s.pc + 4) + δ := by simp only [State.shift_pc]; bv_omega
  have rel : ∀ o : Word, (s.shift δ).pc + o = (s.pc + o) + δ := fun o => by
    simp only [State.shift_pc]; bv_omega
  have hc : s.pc + δ + 4#64 = s.pc + 4#64 + δ := by bv_omega
  have hz : BitVec.signExtend 64 (0 : BitVec 12) = 0 := by decide
  cases i with
  | lui rd imm =>
    simp only [Instr.pcFree] at hi
    simp [exec, hc, State.shift_setPc, State.shift_setReg _ _ (by simpa using hi)]
  | auipc => simp [Instr.pcFree] at hi
  | jal rd off =>
    simp only [Instr.pcFree, beq_iff_eq] at hi; subst hi
    simp only [exec]
    have e0 : ∀ (u : State) v, u.setReg 0 v = u := fun u v => by simp [State.setReg]
    rw [e0, e0, rel, jumpTo_shift hδ]
  | jalr rd rs1 off =>
    simp only [Instr.pcFree, Bool.and_eq_true, beq_iff_eq] at hi
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hi
    simp only [exec]
    have e0 : ∀ (u : State) v, u.setReg 0 v = u := fun u v => by simp [State.setReg]
    have h2 : aligned (s.reg 1 + δ) 4 := (aligned_add_iff hδ).2 hra
    have hz1 : ∀ x : Word, x + BitVec.signExtend 64 (0 : BitVec 12) = x := fun x => by rw [hz]; bv_omega
    simp only [e0, State.shift_reg_one, hz1, and_not_one_aligned hra,
      and_not_one_aligned h2, jumpTo_shift hδ]
  | branch op a b off =>
    simp only [Instr.pcFree, Bool.and_eq_true] at hi
    simp only [exec, shift_reg_of hi.1, shift_reg_of hi.2]
    split
    · rw [rel, jumpTo_shift hδ]
    · simp [hc, State.shift_setPc]
  | load op rd rs1 off =>
    simp only [Instr.pcFree, Bool.and_eq_true] at hi
    simp only [exec, ea, shift_reg_of hi.2, State.shift_mem]
    by_cases ha : aligned (s.reg rs1 + BitVec.signExtend 64 off) op.width <;>
      simp [ha, hc, State.shift_setPc, State.shift_setReg _ _ (by simpa using hi.1)]
  | store op a b off =>
    simp only [Instr.pcFree, Bool.and_eq_true] at hi
    simp only [exec, ea, shift_reg_of hi.1, shift_reg_of hi.2, State.shift_mem]
    by_cases ha : aligned (s.reg a + BitVec.signExtend 64 off) op.width <;>
      simp [ha, hc, State.shift_setPc, State.shift_setMem]
  | iop op rd rs1 imm =>
    simp only [Instr.pcFree, Bool.and_eq_true] at hi
    simp [exec, shift_reg_of hi.2, hc, State.shift_setPc, State.shift_setReg _ _ (by simpa using hi.1)]
  | addiw rd rs1 imm =>
    simp only [Instr.pcFree, Bool.and_eq_true] at hi
    simp [exec, shift_reg_of hi.2, hc, State.shift_setPc, State.shift_setReg _ _ (by simpa using hi.1)]
  | shift op rd rs1 sh =>
    simp only [Instr.pcFree, Bool.and_eq_true] at hi
    simp [exec, shift_reg_of hi.2, hc, State.shift_setPc, State.shift_setReg _ _ (by simpa using hi.1)]
  | shiftw op rd rs1 sh =>
    simp only [Instr.pcFree, Bool.and_eq_true] at hi
    simp [exec, shift_reg_of hi.2, hc, State.shift_setPc, State.shift_setReg _ _ (by simpa using hi.1)]
  | rop op rd a b =>
    simp only [Instr.pcFree, Bool.and_eq_true] at hi
    simp [exec, shift_reg_of hi.1.2, shift_reg_of hi.2, hc, State.shift_setPc,
      State.shift_setReg _ _ (by simpa using hi.1.1)]
  | rwop op rd a b =>
    simp only [Instr.pcFree, Bool.and_eq_true] at hi
    simp [exec, shift_reg_of hi.1.2, shift_reg_of hi.2, hc, State.shift_setPc,
      State.shift_setReg _ _ (by simpa using hi.1.1)]
  | uop op rd rs1 =>
    simp only [Instr.pcFree, Bool.and_eq_true] at hi
    simp [exec, shift_reg_of hi.2, hc, State.shift_setPc, State.shift_setReg _ _ (by simpa using hi.1)]
  | ecall => simp [exec_ecall]

/-- A pcFree instruction leaves `ra` alone. -/
theorem exec_reg_one {i : Instr} (hi : i.pcFree = true) {s s' : State} (h : exec i s = some s') :
    s'.reg 1 = s.reg 1 := by
  have hset : ∀ (u : State) (r : Reg) v, (r != 1) = true → (u.setReg r v).reg 1 = u.reg 1 := by
    intro u r v hr
    have : r ≠ 1 := by simpa using hr
    rw [State.reg_setReg]; simp [Ne.symm this]
  cases i <;> simp only [Instr.pcFree, Bool.and_eq_true, beq_iff_eq] at hi <;>
    simp only [exec, jumpTo] at h <;> (repeat' split at h) <;> simp_all <;>
    (try (obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hi)) <;> (try subst_vars) <;>
    simp_all [State.setReg, State.setPc, State.setMem, State.reg]

theorem Sys.shift {s t : State} (h : Sys s t) (δ : Word) : Sys (s.shift δ) (t.shift δ) := by
  have r : ∀ {r : Reg}, r ≠ 1 → (s.shift δ).reg r = s.reg r := fun h => State.shift_reg _ _ h
  cases h with
  | writeOk n h7 hle hmax hpos =>
    rw [State.shift_emit, State.shift_sysRet, ← r (by decide : (10 : Reg) ≠ 1), ← r (by decide : (11 : Reg) ≠ 1),
      ← State.shift_mem δ s]
    exact .writeOk n (by rw [r (by decide)]; exact h7) (by rw [r (by decide)]; exact hle) hmax
      (by rw [r (by decide)]; exact hpos)
  | writeErr e h7 h1 h2 =>
    rw [State.shift_sysRet]; exact .writeErr e (by rw [r (by decide)]; exact h7) h1 h2
  | readOk ds h7 hle hmax =>
    rw [State.shift_emit, State.shift_setMem, State.shift_sysRet, ← r (by decide : (10 : Reg) ≠ 1),
      ← r (by decide : (11 : Reg) ≠ 1), ← State.shift_mem δ s]
    exact .readOk ds (by rw [r (by decide)]; exact h7) (by rw [r (by decide)]; exact hle) hmax
  | readErr e h7 h1 h2 =>
    rw [State.shift_sysRet]; exact .readErr e (by rw [r (by decide)]; exact h7) h1 h2
  | exit h7 =>
    rw [State.shift_emit, State.shift_halt, ← r (by decide : (10 : Reg) ≠ 1)]
    exact .exit (by rw [r (by decide)]; exact h7)

theorem Sys.reg_one {s t : State} (h : Sys s t) : t.reg 1 = s.reg 1 := by
  cases h <;> simp [State.sysRet, show ¬ (1 : Reg) = Reg.a0 by decide]

theorem SysOk_shift {P : Perm} {s : State} (δ : Word) : SysOk P (s.shift δ) ↔ SysOk P s := by
  unfold SysOk
  rw [State.shift_reg _ _ (by decide : (17 : Reg) ≠ 1), State.shift_reg _ _ (by decide : (11 : Reg) ≠ 1),
    State.shift_reg _ _ (by decide : (12 : Reg) ≠ 1)]

theorem InstrOk_shift {P : Perm} {i : Instr} (hi : i.pcFree = true) {s : State} (δ : Word) :
    InstrOk P i (s.shift δ) ↔ InstrOk P i s := by
  cases i <;> simp only [Instr.pcFree, Bool.and_eq_true] at hi <;> simp only [InstrOk]
  · simp only [ea, shift_reg_of hi.2]
  · simp only [ea, shift_reg_of hi.1]
  · exact SysOk_shift δ

/-! ## Runs, shifted -/

def Dom.shift (δ : Word) (D : Dom) : Dom := D.map fun r => (r.1 + δ, r.2)

theorem Dom.mem_shift {D : Dom} {δ x : Word} : (D.shift δ).mem (x + δ) ↔ D.mem x := by
  unfold Dom.mem Dom.shift
  rw [List.any_map]
  have : ∀ r : Word × Nat, (x + δ - (r.1 + δ)) = x - r.1 := fun r => by bv_omega
  simp only [Function.comp_def, this]

theorem Dom.mem_shift' {D : Dom} {δ y : Word} : (D.shift δ).mem y ↔ D.mem (y + -δ) := by
  have := @Dom.mem_shift D δ (y + -δ)
  rwa [show y + -δ + δ = y by bv_omega] at this

theorem aligned_neg {δ : Word} (h : aligned δ 4) : aligned (-δ) 4 := by
  unfold aligned at *
  rw [BitVec.toNat_neg]
  have := BitVec.isLt δ
  by_cases h0 : δ.toNat = 0
  · simp [h0]
  · have e : (2 ^ 64 - δ.toNat) % 2 ^ 64 = 2 ^ 64 - δ.toNat := Nat.mod_eq_of_lt (by omega)
    rw [e]; omega

/-- `c'` holds, `δ` further on, the pcFree instructions `c` holds in `D`. -/
structure CodeShift (c c' : Code) (D : Dom) (δ : Word) : Prop where
  instr : ∀ x, D.mem x → c'.instr (x + δ) = c.instr x
  free : ∀ x i, D.mem x → c.instr x = some i → i.pcFree = true
  aligned : aligned δ 4

variable {c c' : Code} {P : Perm} {D : Dom} {δ : Word}

theorem Step.shift (h : CodeShift c c' D δ) {s s' : State} (hd : D.mem s.pc)
    (hra : aligned (s.reg 1) 4) (st : Step c P s s') : Step c' P (s.shift δ) (s'.shift δ) := by
  cases st with
  | exec he hi hok hx =>
    have hf := h.free _ _ hd hi
    refine .exec he (by rw [State.shift_pc, h.instr _ hd]; exact hi) ((InstrOk_shift hf δ).2 hok) ?_
    rw [exec_shift hf h.aligned hra, hx]; rfl
  | sys he hi hok hy =>
    exact .sys he (by rw [State.shift_pc, h.instr _ hd]; exact hi) ((SysOk_shift δ).2 hok) (hy.shift δ)

theorem Step.unshift (h : CodeShift c c' D δ) {s t : State} (hd : D.mem s.pc)
    (hra : aligned (s.reg 1) 4) (st : Step c' P (s.shift δ) t) :
    ∃ s', t = s'.shift δ ∧ Step c P s s' := by
  cases st with
  | exec he hi hok hx =>
    rw [State.shift_pc, h.instr _ hd] at hi
    have hf := h.free _ _ hd hi
    rw [exec_shift hf h.aligned hra] at hx
    obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.1 hx
    exact ⟨s', rfl, .exec he hi ((InstrOk_shift hf δ).1 hok) hs'⟩
  | sys he hi hok hy =>
    rw [State.shift_pc, h.instr _ hd] at hi
    refine ⟨t.shift (-δ), (State.neg_shift _ _).symm, .sys he hi ((SysOk_shift δ).1 hok) ?_⟩
    have := hy.shift (-δ); rwa [State.shift_neg] at this

theorem Step.reg_one (h : CodeShift c c' D δ) {s s' : State} (hd : D.mem s.pc)
    (st : Step c P s s') : s'.reg 1 = s.reg 1 := by
  cases st with
  | exec _ hi _ hx => exact exec_reg_one (h.free _ _ hd hi) hx
  | sys _ _ _ hy => exact hy.reg_one

/-- A run of pcFree code is a run of the same code `δ` further on. -/
theorem Reach.shift (h : CodeShift c c' D δ) {Q : State → Prop} {s : State}
    (hr : Reach c P D Q s) (hra : aligned (s.reg 1) 4) :
    Reach c' P (D.shift δ) (fun t => Q (t.shift (-δ))) (s.shift δ) := by
  induction hr with
  | done hq => exact .done (by rw [State.shift_neg]; exact hq)
  | @step u hd hex _ ih =>
    obtain ⟨u1, st⟩ := hex
    refine .step (by rw [State.shift_pc]; exact Dom.mem_shift.2 hd) ⟨_, Step.shift h hd hra st⟩ ?_
    intro t st'
    obtain ⟨u', rfl, st''⟩ := Step.unshift h hd hra st'
    exact ih u' st'' (by rw [Step.reg_one h hd st'']; exact hra)

/-! ## Specifications that do not look at the pc or `ra` -/

structure Spec.ShiftInv {α : Type} (sp : Spec α) : Prop where
  pre : ∀ a s δ, sp.pre a (s.shift δ) ↔ sp.pre a s
  post : ∀ a s t δ, sp.post a (s.shift δ) (t.shift δ) ↔ sp.post a s t
  onExit : ∀ a s t δ, sp.onExit a (s.shift δ) (t.shift δ) ↔ sp.onExit a s t
  reads : ∀ a s δ, sp.reads a (s.shift δ) = sp.reads a s
  writes : ∀ a s δ, sp.writes a (s.shift δ) = sp.writes a s

theorem Spec.ShiftInv.perm {α : Type} {sp : Spec α} (hs : sp.ShiftInv) (a : α) (s : State) (δ : Word) :
    sp.perm a (s.shift δ) = sp.perm a s := by
  simp only [Spec.perm, Spec.stackRegion, hs.reads, hs.writes, State.shift_reg _ _ (by decide : (2 : Reg) ≠ 1)]

/-- A proof at one address is a proof `δ` further on. -/
theorem VerifiedImg.shift {α : Type} {e : Word} {sp : Spec α} (h : CodeShift c c' D δ)
    (hs : sp.ShiftInv) (hv : VerifiedImg c D e sp) : VerifiedImg c' (D.shift δ) (e + δ) sp := by
  intro a s' he' hpre'
  have hs' : (s'.shift (-δ)).shift δ = s' := State.neg_shift _ _
  have he : Entry D e (s'.shift (-δ)) :=
    { pc := by rw [State.shift_pc, he'.pc]; bv_omega
      live := by rw [State.shift_exit]; exact he'.live
      ret := by
        rw [State.shift_reg_one]; intro hm; exact he'.ret (Dom.mem_shift'.2 hm)
      retAligned := by
        rw [State.shift_reg_one]; exact (aligned_add_iff (aligned_neg h.aligned)).2 he'.retAligned
      sp := by rw [State.shift_reg _ _ (by decide)]; exact he'.sp }
  have hpre : sp.pre a (s'.shift (-δ)) := (hs.pre a _ δ).1 (by rw [hs']; exact hpre')
  have hr := Reach.shift h (hv a _ he hpre) he.retAligned
  rw [hs', hs.perm] at hr
  refine Reach.mono ?_ hr
  rintro t ⟨hf, hd⟩
  refine ⟨?_, ?_⟩
  · rcases hf with hf | hf
    · exact .inl (fun hm => hf (Dom.mem_shift'.1 hm))
    · exact .inr (by simpa using hf)
  · have hpost := hs.post a (s'.shift (-δ)) (t.shift (-δ)) δ
    have hexit := hs.onExit a (s'.shift (-δ)) (t.shift (-δ)) δ
    rw [hs', State.neg_shift] at hpost hexit
    rcases hd with ⟨hx, hpc, hpres, hp⟩ | ⟨hx, ho⟩
    · refine .inl ⟨by simpa using hx, ?_, ?_, hpost.2 hp⟩
      · show t.pc = s'.reg 1
        simp only [State.shift_pc, State.shift_reg_one] at hpc; bv_omega
      · intro r hr'
        have hne : r ≠ 1 := by
          intro e; subst e; simp [preservedRegs] at hr'
        have := hpres r hr'
        rwa [State.shift_reg _ _ hne, State.shift_reg _ _ hne] at this
    · exact .inr ⟨by simpa using hx, hexit.2 ho⟩

end NoCompiler
