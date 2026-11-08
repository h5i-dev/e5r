import Theories.Logic
import Projects.thermostat.ImageFidelity

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat
open E5R
abbrev img := E5R.ThermostatImage.image.ro

theorem i0 : fetchDecode img 0x80000036#32 = some (.opimm .add 13 0 349, 4) := by decide +kernel
theorem i1 : fetchDecode img 0x8000003a#32 = some (.branch .ge 13 11 8, 4) := by decide +kernel
theorem i2 : fetchDecode img 0x8000003e#32 = some (.opimm .add 10 0 0, 2) := by decide +kernel
theorem i3 : fetchDecode img 0x80000040#32 = some (.jalr 0 1 0, 2) := by decide +kernel
theorem i4 : fetchDecode img 0x80000042#32 = some (.branch .eq 10 0 14, 2) := by decide +kernel
theorem i5 : fetchDecode img 0x80000044#32 = some (.op .add 13 0 10, 2) := by decide +kernel
theorem i6 : fetchDecode img 0x80000046#32 = some (.opimm .add 10 0 1, 2) := by decide +kernel
theorem i7 : fetchDecode img 0x80000048#32 = some (.branch .eq 13 10 8, 4) := by decide +kernel
theorem i8 : fetchDecode img 0x8000004c#32 = some (.op .slt 10 11 12, 4) := by decide +kernel
theorem i9 : fetchDecode img 0x80000050#32 = some (.jalr 0 1 0, 2) := by decide +kernel

/-- Execute exactly n instructions, accepting only pure, aligned steps. -/
def run (image : List Segment) : Nat → Core → Option Core
 | 0, c => some c
 | n+1, c => if c.pc.getLsbD 0 then none else
   match fetchDecode image c.pc with
   | none => none
   | some (i, len) => match exec c len i with
     | .done d => run image n d
     | _ => none

theorem run_sound {image : List Segment} {B : Board} {n : Nat} {c d : Core}
    (h : run image n c = some d) (ram : Word → BitVec 8) :
    DetSteps B image n ⟨c, ram⟩ ⟨d, ram⟩ := by
  induction n generalizing c with
  | zero => simp [run] at h; subst d; exact .refl _
  | succ n ih =>
    simp only [run] at h
    split at h
    · contradiction
    · rename_i ha
      cases hd : fetchDecode image c.pc with
      | none => simp [hd] at h
      | some pair =>
        obtain ⟨i, len⟩ := pair
        simp only [hd] at h
        cases he : exec c len i <;> simp only [he] at h
        case done d' =>
          exact .step (detStep_of (by simpa using ha) hd (fun o => by rw [he]; rfl)) (ih h)
        all_goals contradiction

/-- Off=0, Heat=1, Auto=2. Temperatures use the psABI's signed extension. -/
def spec (mode temp setpoint : Word) : Word :=
  if temp.slt 350#32 then
    if mode = 0#32 then 0 else if mode = 1#32 then 1 else if temp.slt setpoint then 1 else 0
  else 0



theorem cmp (t : Word) : (349#32).slt t = !t.slt 350#32 := by
  change decide ((349 : Int) < t.toInt) = !decide (t.toInt < (350 : Int))
  by_cases h : t.toInt < 350
  · have h' : ¬349 < t.toInt := by omega
    simp [h, h']
  · have h' : 349 < t.toInt := by omega
    simp [h, h']

/-- Every valid mode returns in at most eight instruction steps, with RAM unchanged.
    Inputs may be any signed 32-bit words, including every sign-extended i16 pair.
    Interrupt entries and the HTTP shell are outside this function contract. -/
theorem heater_contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80000036) (hm : c.get 10 = 0#32 ∨ c.get 10 = 1#32 ∨ c.get 10 = 2#32) :
    ∃ n d, n ≤ 8 ∧ DetSteps B img n ⟨c, ram⟩ ⟨d, ram⟩ ∧
      d.pc = c.get 1 &&& ~~~1 ∧ d.get 10 = spec (c.get 10) (c.get 11) (c.get 12) := by
  by_cases ht : (c.get 11).slt 350#32 = true
  · have hc : (349#32).slt (c.get 11) = false := by rw [cmp, ht]; rfl
    rcases hm with hm | hm | hm
    all_goals
      let n : Nat := if c.get 10 = 0#32 then 4 else if c.get 10 = 1#32 then 7 else 8
      have hr : ∃ d, run img n c = some d := by
        simp [n, run, hp, i0, i1, i2, i3, i4, i5, i6, i7, i8, i9,
          exec_opimm, exec_op, exec_branch, exec_jalr, alu, taken, jump,
          Core.wr, Core.goto, Core.get_set, Core.get_zero, hm, hc]
      obtain ⟨d, hr⟩ := hr
      refine ⟨n, d, by simp [n, hm], run_sound hr ram, ?_⟩
      simp [n, run, hp, i0, i1, i2, i3, i4, i5, i6, i7, i8, i9,
        exec_opimm, exec_op, exec_branch, exec_jalr, alu, taken, jump,
        Core.wr, Core.goto, Core.get_set, Core.get_zero, hm, hc] at hr
      subst d
      simp [Core.get_set, hm, spec, ht]
  · have ht' : (c.get 11).slt 350#32 = false := Bool.eq_false_iff.mpr ht
    have hc : (349#32).slt (c.get 11) = true := by rw [cmp, ht']; rfl
    have hr : ∃ d, run img 4 c = some d := by
      simp [run, hp, i0, i1, i2, i3, i4, i5, i6, i7, i8, i9,
        exec_opimm, exec_op, exec_branch, exec_jalr, alu, taken, jump,
        Core.wr, Core.goto, Core.get_set, Core.get_zero, hc]
    obtain ⟨d, hr⟩ := hr
    refine ⟨4, d, by decide, run_sound hr ram, ?_⟩
    simp [run, hp, i0, i1, i2, i3, i4, i5, i6, i7, i8, i9,
      exec_opimm, exec_op, exec_branch, exec_jalr, alu, taken, jump,
      Core.wr, Core.goto, Core.get_set, Core.get_zero, hc] at hr
    subst d
    simp [Core.get_set, spec, ht']

/-- Relate the register specification to the original Rust i16 control rule. -/
theorem spec_i16 (mode : Word) (hm : mode = 0#32 ∨ mode = 1#32 ∨ mode = 2#32)
    (temp setpoint : BitVec 16) :
    spec mode (temp.signExtend 32) (setpoint.signExtend 32) =
      if temp.toInt < 350 ∧ (mode = 1#32 ∨ (mode = 2#32 ∧ temp.toInt < setpoint.toInt))
      then 1 else 0 := by
  rcases hm with hm | hm | hm
  all_goals
    simp [spec, hm, BitVec.slt, BitVec.toInt_signExtend_of_le (by decide : 16 ≤ 32)]
    all_goals split <;> simp_all <;> omega

/-- A result of one implies the safety interlock, for the actual emitted code. -/
theorem heater_interlock (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80000036) (hm : c.get 10 = 0#32 ∨ c.get 10 = 1#32 ∨ c.get 10 = 2#32)
    (ht : ¬(c.get 11).slt 350#32 = true) :
    ∃ n d, n ≤ 8 ∧ DetSteps B img n ⟨c, ram⟩ ⟨d, ram⟩ ∧
      d.pc = c.get 1 &&& ~~~1 ∧ d.get 10 = 0 := by
  obtain ⟨n, d, hn, hs, hp, hv⟩ := heater_contract B c ram hp hm
  exact ⟨n, d, hn, hs, hp, by simpa [spec, ht] using hv⟩

end E5R.Thermostat
