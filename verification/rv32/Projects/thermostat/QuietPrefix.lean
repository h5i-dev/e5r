import Projects.thermostat.Quiet
import Projects.thermostat.Interrupt
namespace E5R.Thermostat.QuietPrefix
open E5R E5R.Thermostat

theorem unique_step {B m d e reads evs} (hs : Quiet.Step B img m d)
    (hm : m.core.mie_=false) (actual : Observed.Step B img m e reads evs) :
    e=d ∧ reads=[] ∧ evs=[] := by
  cases actual with
  | instr o he =>
    rw [hs o] at he
    cases he
    simp [hs o]
  | irq code enabled _ => simp [irqEnabled,hm] at enabled

/-- Every executed prefix follows the certificate and retains its exact
    suffix. The global image theorem excludes IRQs at all its boundaries. -/
theorem suffix {B n m d} (cert : Quiet.Steps B img n m d) (hm : m.core.mie_=false)
    {k e reads evs} (hk : k≤n) (actual : Observed.Steps B img k m e reads evs) :
    reads=[] ∧ evs=[] ∧ Quiet.Steps B img (n-k) e d ∧ e.core.mie_=false := by
  induction cert generalizing k e reads evs with
  | refl m =>
    have hz : k=0 := by omega
    subst k
    cases actual
    exact ⟨rfl,rfl,.refl _,hm⟩
  | @step n a mid d hs tail ih =>
    cases k with
    | zero =>
      cases actual
      exact ⟨rfl,rfl,by simpa using Quiet.Steps.step hs tail,hm⟩
    | succ k =>
      cases actual with
      | step first rest =>
        obtain ⟨rfl,rfl,rfl⟩ := unique_step hs hm first
        have hmm := Interrupt.step_masked hm hs.det.toStep
        obtain ⟨hr,he,hq,hmask⟩ := ih hmm (by omega) rest
        exact ⟨by simpa using hr,by simpa using he,by simpa using hq,hmask⟩

/-- The final boundary belongs to the caller. Safety is asserted only before
    the certified RET has completed. -/
theorem safe {B n m d} (cert : Quiet.Steps B img n m d) (hm : m.core.mie_=false)
    {k e reads evs} (hk : k<n) (actual : Observed.Steps B img k m e reads evs) :
    reads=[] ∧ evs=[] ∧ ¬Escapes B img e := by
  obtain ⟨hr,he,tail,hmask⟩ := suffix cert hm (by omega) actual
  have hp : 0<n-k := by omega
  refine ⟨hr,he,?_⟩
  cases heq : n-k with
  | zero => omega
  | succ j =>
    rw [heq] at tail
    cases tail with
    | step hs _ => exact Trace.no_escape hs.det hmask

theorem complete {B n m d} (cert : Quiet.Steps B img n m d) (hm : m.core.mie_=false)
    {e reads evs} (actual : Observed.Steps B img n m e reads evs) :
    e=d ∧ reads=[] ∧ evs=[] := by
  obtain ⟨hr,he,tail,_⟩ := suffix cert hm (by omega) actual
  rw [Nat.sub_self] at tail
  cases tail
  exact ⟨rfl,hr,he⟩

end E5R.Thermostat.QuietPrefix
