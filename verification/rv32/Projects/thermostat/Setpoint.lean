import Projects.thermostat.SetMode
import Projects.thermostat.SetpointCheck

set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.Setpoint
open E5R E5R.Thermostat

/-- Complete authorized SetSetpoint: every i16 value, including all refusals. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot) (dc : BitVec 16)
    (h : Call.Pre B c ram true s (.setpoint dc)) :
    ∃ n m, n ≤ 65 ∧ DetSteps B img n ⟨c,ram⟩ m ∧ Call.Post c ram m (Spec.transition true s (.setpoint dc)) := by
  obtain ⟨ne,cd,hne,heRun,he⟩ := Call.enter B c ram true s (.setpoint dc) h
  let r0 := Stack.save c ram
  have hActor : r0 (cd.get 11) = 1#8 := by rw [he.actorPtr];exact he.actorAt
  have hActorRam : B.inRam (cd.get 11) 1 = true := by
    rw [he.actorPtr]
    simpa using Memory.block_access (B := B) (p := c.get 11) (n := 1) (off := 0) (width := 1)
      h.actorRam (by decide) (by decide)
  obtain ⟨ca,haRun,haPc,haRegs,haCsr⟩ := Authorize.contract B cd r0 ⟨0,by decide⟩
    (by exact he.pc) hActorRam hActor
  have haCommand : ca.get 13 = c.get 13 := (haRegs 13 (by decide)).trans he.commandPtr
  have hlo := he.commandAt ⟨2,by decide⟩ (Encoding.shortByte dc false) rfl
  have hhi := he.commandAt ⟨3,by decide⟩ (Encoding.shortByte dc true) rfl
  change r0 (c.get 13+2#32) = Encoding.shortByte dc false at hlo
  change r0 (c.get 13+3#32) = Encoding.shortByte dc true at hhi
  let cl := ca.wr 8 (dc.signExtend 32) 0x800000e0
  have hl : DetStep B img ⟨ca,r0⟩ ⟨cl,r0⟩ := by
    refine detStep_of (by rw [haPc];decide) (by rw [haPc];exact d2147483868) fun o => ?_
    have hm : B.inRam (c.get 13+2#32) 2 = true :=
      Memory.block_access (B := B) (p := c.get 13) (n := 4) (off := 2) (width := 2) h.commandRam (by decide) (by decide)
    rw [exec_load,haCommand,interp_load_ram (B := B) (img := img) (w := .h) (a := c.get 13+2#32)
      o (Memory.half_aligned (c.get 13) 1 h.commandAlign) hm]
    rw [Fields.short_load r0 (c.get 13+2#32) dc hlo (by simpa [BitVec.add_assoc] using hhi),haPc]
    rfl
  obtain ⟨cc,hcRun,hcPc,hcDecision,hcRegs,hcCsr⟩ := SetpointCheck.contract B cl r0 dc rfl
    (by simp [cl,Core.wr_get])
  let cg := cc.goto (if 50 ≤ dc.toInt ∧ dc.toInt ≤ 300 then 0x8000027a else 0x800000f2)
  have hg : DetStep B img ⟨cc,r0⟩ ⟨cg,r0⟩ := SetpointCheck.branch B cc r0 dc hcPc hcDecision
  have hgRun : DetSteps B img 9 ⟨cd,r0⟩ ⟨cg,r0⟩ :=
    ((haRun.trans (.single hl)).trans hcRun).trans (.single hg)
  have hgOut : cg.get 10 = c.get 10 := by
    exact (hcRegs 10 (by decide) (by decide)).trans
      ((Core.wr_get_ne ca 8 10 (dc.signExtend 32) 0x800000e0 (by decide)).trans
      ((haRegs 10 (by decide)).trans he.outPtr))
  have hgState : cg.get 12 = c.get 12 := by
    exact (hcRegs 12 (by decide) (by decide)).trans
      ((Core.wr_get_ne ca 8 12 (dc.signExtend 32) 0x800000e0 (by decide)).trans
      ((haRegs 12 (by decide)).trans he.statePtr))
  have hgSp : cg.get 2 = Stack.base c := by
    exact (hcRegs 2 (by decide) (by decide)).trans
      ((Core.wr_get_ne ca 8 2 (dc.signExtend 32) 0x800000e0 (by decide)).trans
      ((haRegs 2 (by decide)).trans he.sp))
  have hgCsr : cg.sameCsr c := (Core.sameCsr_goto _ _).trans
    (hcCsr.trans ((Core.sameCsr_wr _ _ _ _).trans (haCsr.trans he.csr)))
  have hgUpper : Upper.Frame c cg := by
    intro r hr
    exact (hcRegs r (Upper.ne_low r hr 11 (by decide)) (Upper.ne_low r hr 13 (by decide))).trans
      ((Core.wr_get_ne ca 8 r (dc.signExtend 32) 0x800000e0 (Upper.ne_low r hr 8 (by decide))).trans
        ((haRegs r (Upper.ne_low r hr 11 (by decide))).trans (he.upper r hr)))
  by_cases hRange : 50 ≤ dc.toInt ∧ dc.toInt ≤ 300
  · have hInput : Prepare.Input B cg r0 ⟨2,by decide⟩ s.mode dc := by
      change cg.get 8 = dc.signExtend 32
      exact (hcRegs 8 (by decide) (by decide)).trans (by simp [cl,Core.wr_get])
    obtain ⟨np,ch,hnp,hpRun,hReady,hpSp,hpCsr,hpUpper⟩ := Prepare.contract_full B cg r0 ⟨2,by decide⟩ s s.mode dc
      (by simp [cg,Prepare.start,hRange])
      (by simpa only [hgState] using he.stateAt)
      (by simpa only [hgState] using h.stateRam)
      (by simpa only [hgState] using h.stateAlign) hInput
    have hReady' : HeaterReady.Ready ch (Prepare.next ⟨2,by decide⟩ s s.mode dc) ⟨2,by decide⟩ (c.get 10) := by
      simpa only [hgOut] using hReady
    obtain ⟨nh,cb,r',hnh,hhRun,hhPc,hhOutcome,hhSp,hhCsr,hhFrame,hhUpper⟩ := HeaterReady.contract_full B ch r0
      (Prepare.next ⟨2,by decide⟩ s s.mode dc) ⟨2,by decide⟩ (c.get 10) hReady' h.outRam h.outAlign
    have hOutcome : Outcome.At r' (c.get 10) (Spec.transition true s (.setpoint dc)) := by
      have hn : ¬(dc.toInt < 50 ∨ 300 < dc.toInt) := by omega
      simpa [Spec.transition,Spec.changed,Prepare.next,hn] using hhOutcome
    obtain ⟨d,hrun,hpost⟩ := Call.finish B c cd cb ram r' true s (.setpoint dc)
      (Spec.transition true s (.setpoint dc)) ne (9+np+nh) h heRun ((hgRun.trans hpRun).trans hhRun)
      hhPc (hhSp.trans (hpSp.trans hgSp)) (hhCsr.trans (hpCsr.trans hgCsr)) (Upper.trans (Upper.trans hgUpper hpUpper) hhUpper) hOutcome hhFrame
    exact ⟨ne+(9+np+nh)+9,⟨d,r'⟩,by omega,hrun,hpost⟩
  · have h0 : B.inRam (cg.get 10) 1 = true := by
      rw [hgOut]
      simpa using Memory.block_access (B := B) (p := c.get 10) (n := 20) (off := 0) (width := 1)
        h.outRam (by decide) (by decide)
    have h10 : B.inRam (cg.get 10+10#32) 1 = true := by
      rw [hgOut]
      exact Memory.block_access (B := B) (p := c.get 10) (n := 20) (off := 10) (width := 1)
        h.outRam (by decide) (by decide)
    obtain ⟨cb,hbRun,hbPc,hbSp,hbCsr,hbUpper⟩ := Errors.setpoint_range_full B cg r0 (by simp [cg,hRange]) h0 h10
    rw [hgOut] at hbRun
    let r' := Errors.result r0 (c.get 10) .setpointOutOfRange
    have hOutcome : Outcome.At r' (c.get 10) (Spec.transition true s (.setpoint dc)) := by
      have hb : dc.toInt < 50 ∨ 300 < dc.toInt := by omega
      simp only [Spec.transition,Bool.not_true,ite_false,ite_eq_left hb]
      exact Outcome.error _ _ _
    have hFrame : ∀ x, (∀ i : Fin 20, x ≠ c.get 10+BitVec.ofNat 32 i.val) → r' x = r0 x := by
      intro x hx
      exact Errors.result_frame r0 (c.get 10) x .setpointOutOfRange
        (by simpa using hx ⟨0,by decide⟩) (hx ⟨10,by decide⟩)
    obtain ⟨d,hrun,hpost⟩ := Call.finish B c cd cb ram r' true s (.setpoint dc)
      (Spec.transition true s (.setpoint dc)) ne 13 h heRun (hgRun.trans hbRun)
      hbPc (hbSp.trans hgSp) (hbCsr.trans hgCsr) (Upper.trans hgUpper hbUpper) hOutcome hFrame
    exact ⟨ne+13+9,⟨d,r'⟩,by omega,hrun,hpost⟩

end E5R.Thermostat.Setpoint
