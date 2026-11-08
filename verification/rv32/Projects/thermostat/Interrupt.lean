import Projects.thermostat.ControlFetch
import Projects.thermostat.ControlSites
import Projects.thermostat.Trace
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.Interrupt
open E5R E5R.Thermostat

/-- Every successfully decoded instruction at every aligned image address
    preserves the global IRQ mask. Includes interior halfword boundaries. -/
theorem decoded_safe (pc : Word) (i : Instr) (len : Word)
    (ha : pc.getLsbD 0 = false) (hd : fetchDecode img pc = some (i,len)) : Control.Safe i := by
  by_cases hs : Control.IsSystem i = true
  · have hal : pc.toNat%2 = 0 := by
      apply Nat.mod_two_eq_zero_iff_testBit_zero.mpr
      simpa only [BitVec.getLsbD] using ha
    have hsite := Control.system_site hal hd hs
    rw [Control.sites_checked] at hsite
    have hc := List.all_eq_true.mp Control.candidates_checked pc.toNat hsite
    change (match fetchDecode img (BitVec.ofNat 32 pc.toNat) with
      | none => true | some (i,_) => decide (Control.Safe i)) = true at hc
    simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq] at hc
    rw [hd] at hc
    exact of_decide_eq_true hc
  · apply Control.non_system_safe
    cases h : Control.IsSystem i with
    | false => rfl
    | true => exact False.elim (hs h)

/-- Successful platform steps preserve MIE=false. Unsupported/fault escapes
    remain a separate proof obligation; this is solely interrupt exclusion. -/
theorem step_masked {B m d evs} (hm : m.core.mie_ = false) (h : Step B img m d evs) :
    d.core.mie_ = false := by
  cases h with
  | instr o he =>
    obtain ⟨ha,i,len,hd,he⟩ := Control.ok_decoded he
    exact Control.interp_masked (Control.exec_masked m.core len i hm (decoded_safe _ _ _ ha hd))
      o m.ram 0 [] _ _ _ he
  | irq code hen _ => simp [irqEnabled,hm] at hen

/-- IRQs are disabled throughout every actual platform Reach execution from
    any globally masked initial state, including reset under the board assumptions. -/
theorem reach_masked {B Init m evs}
    (hinit : ∀ m, Init m → m.core.mie_ = false) (h : Reach B img Init m evs) :
    m.core.mie_ = false := by
  induction h with
  | init hi => exact hinit _ hi
  | step _ hs ih => exact step_masked ih hs

theorem no_irq {B Init m evs}
    (hinit : ∀ m, Init m → m.core.mie_ = false) (h : Reach B img Init m evs) (code : Nat) :
    irqEnabled m.core code = false := by
  simp [irqEnabled,reach_masked hinit h]

/-- Every deterministic instruction contract on this image lifts to a closed
    IRQ-masked certificate, from any globally masked starting state. -/
theorem close {B n m d} (h : DetSteps B img n m d) (hm : m.core.mie_ = false) :
    Trace.Closed B img n m d := by
  induction h with
  | refl => exact .done hm
  | step hs _ ih => exact .next hm hs (ih (step_masked hm hs.toStep))
end E5R.Thermostat.Interrupt
