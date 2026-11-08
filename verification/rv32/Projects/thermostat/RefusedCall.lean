import Projects.thermostat.Call
import Projects.thermostat.Unauthorized

set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.RefusedCall
open E5R E5R.Thermostat

/-- Full unauthorized transition refinement against the independent source spec.
    Tag equality and the protected-command condition are discharged in each
    SetSetpoint/SetRelay/SetMode case of the final kernel theorem. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot) (cmd : Spec.Command)
    (kind : Fin 3) (h : Call.Pre B c ram false s cmd)
    (hTag : Encoding.tagFin cmd = Unauthorized.tag kind)
    (hProtected : Spec.configurable cmd = true) :
    ∃ n m, n ≤ 30 ∧ DetSteps B img n ⟨c,ram⟩ m ∧ Call.Post c ram m (Spec.transition false s cmd) := by
  obtain ⟨ne,cd,hne,heRun,he⟩ := Call.enter B c ram false s cmd h
  let r0 := Stack.save c ram
  have hActor : r0 (cd.get 11) = 0#8 := by rw [he.actorPtr];exact he.actorAt
  have hActorRam : B.inRam (cd.get 11) 1 = true := by
    rw [he.actorPtr]
    simpa using Memory.block_access (B := B) (p := c.get 11) (n := 1) (off := 0) (width := 1)
      h.actorRam (by decide) (by decide)
  have hp : cd.pc = Unauthorized.entry kind := by
    have hx := he.pc
    rw [hTag,Unauthorized.dispatch_entry] at hx
    exact hx
  obtain ⟨ca,haRun,haPc,haRegs,haCsr⟩ := Unauthorized.enter B cd r0 kind hp hActorRam hActor
  have hOut : ca.get 10 = c.get 10 := (haRegs 10 (by decide)).trans he.outPtr
  have h0 : B.inRam (ca.get 10) 1 = true := by
    rw [hOut]
    simpa using Memory.block_access (B := B) (p := c.get 10) (n := 20) (off := 0) (width := 1)
      h.outRam (by decide) (by decide)
  have h10 : B.inRam (ca.get 10+10#32) 1 = true := by
    rw [hOut]
    exact Memory.block_access (B := B) (p := c.get 10) (n := 20) (off := 10) (width := 1)
      h.outRam (by decide) (by decide)
  obtain ⟨cb,hbRun,hbPc,hbSp,hbCsr,hbUpper⟩ := Errors.forbidden_full B ca r0 haPc h0 h10
  rw [hOut] at hbRun
  let r' := Errors.result r0 (c.get 10) .forbidden
  have hOutcome : Outcome.At r' (c.get 10) (Spec.transition false s cmd) := by
    rw [Spec.unauthorized s cmd hProtected]
    exact Outcome.error _ _ _
  have hSp : cb.get 2 = Stack.base c := hbSp.trans ((haRegs 2 (by decide)).trans he.sp)
  have hCsr : cb.sameCsr c := hbCsr.trans (haCsr.trans he.csr)
  have hFrame : ∀ x, (∀ i : Fin 20, x ≠ c.get 10+BitVec.ofNat 32 i.val) → r' x = r0 x := by
    intro x hx
    exact Errors.result_frame r0 (c.get 10) x .forbidden (by simpa using hx ⟨0,by decide⟩) (hx ⟨10,by decide⟩)
  obtain ⟨d,hrun,hpost⟩ := Call.finish B c cd cb ram r' false s cmd (Spec.transition false s cmd)
    ne 6 h heRun (haRun.trans hbRun) hbPc hSp hCsr (Upper.trans (Upper.trans he.upper (fun r hr => haRegs r (Upper.ne_low r hr 11 (by decide)))) hbUpper) hOutcome hFrame
  exact ⟨ne+6+9,⟨d,r'⟩,by omega,hrun,hpost⟩

end E5R.Thermostat.RefusedCall
