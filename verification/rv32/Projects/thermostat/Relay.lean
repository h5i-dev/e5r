import Projects.thermostat.RelayBody
import Projects.thermostat.RelayCheck
import Projects.thermostat.Setpoint
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.Relay
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot) (idx : BitVec 8) (on : Bool)
    (h : Call.Pre B c ram true s (.relay idx on)) :
    ∃ n m, n ≤ 81 ∧ DetSteps B img n ⟨c,ram⟩ m ∧ Call.Post c ram m (Spec.transition true s (.relay idx on)) := by
  obtain ⟨ne,cd,hne,heRun,he⟩ := Call.enter B c ram true s (.relay idx on) h
  let r0 := Stack.save c ram
  have hActor : r0 (cd.get 11) = 1#8 := by rw [he.actorPtr];exact he.actorAt
  have hActorRam : B.inRam (cd.get 11) 1 = true := by
    rw [he.actorPtr]
    simpa using Memory.block_access (B := B) (p := c.get 11) (n := 1) (off := 0) (width := 1) h.actorRam (by decide) (by decide)
  obtain ⟨ca,haRun,haPc,haRegs,haCsr⟩ := Authorize.contract B cd r0 ⟨1,by decide⟩ (by exact he.pc) hActorRam hActor
  have haCommand : ca.get 13 = c.get 13 := (haRegs 13 (by decide)).trans he.commandPtr
  have hIdx : r0 (ca.get 13+1#32) = idx := by
    rw [haCommand]
    exact he.commandAt ⟨1,by decide⟩ idx rfl
  have hIdxRam : B.inRam (ca.get 13+1#32) 1 = true := by
    rw [haCommand]
    exact Memory.block_access (B := B) (p := c.get 13) (n := 4) (off := 1) (width := 1) h.commandRam (by decide) (by decide)
  obtain ⟨cg,hgRun,hgPc,hgIdx,hgRegs,hgCsr⟩ := RelayCheck.contract B ca r0 idx haPc hIdxRam hIdx
  have hgOut : cg.get 10 = c.get 10 := (hgRegs 10 (by decide) (by decide)).trans ((haRegs 10 (by decide)).trans he.outPtr)
  have hgState : cg.get 12 = c.get 12 := (hgRegs 12 (by decide) (by decide)).trans ((haRegs 12 (by decide)).trans he.statePtr)
  have hgCommand : cg.get 13 = c.get 13 := (hgRegs 13 (by decide) (by decide)).trans haCommand
  have hgSp : cg.get 2 = Stack.base c := (hgRegs 2 (by decide) (by decide)).trans ((haRegs 2 (by decide)).trans he.sp)
  have hgCsr' : cg.sameCsr c := hgCsr.trans (haCsr.trans he.csr)
  have hgUpper : Upper.Frame c cg := (Upper.trans (Upper.trans he.upper (fun r hr => haRegs r (Upper.ne_low r hr 11 (by decide)))) (fun r hr => hgRegs r (Upper.ne_low r hr 11 (by decide)) (Upper.ne_low r hr 14 (by decide))))
  by_cases hi : idx.toNat < 4
  · have honRam : B.inRam (cg.get 13+2#32) 1 = true := by
      rw [hgCommand]
      exact Memory.block_access (B := B) (p := c.get 13) (n := 4) (off := 2) (width := 1) h.commandRam (by decide) (by decide)
    have hon : r0 (cg.get 13+2#32) = Encoding.boolByte on := by
      rw [hgCommand]
      exact he.commandAt ⟨2,by decide⟩ (Encoding.boolByte on) rfl
    obtain ⟨cb,r',hbRun,hbPc,hbSp,hbCsr,hbOutcome,hbFrame,hbUpper⟩ := RelayBody.contract B cg r0 s idx on
      (by simpa [hi] using hgPc) hgIdx hi
      (by simpa only [hgState] using he.stateAt) (by simpa only [hgState] using h.stateRam)
      (by simpa only [hgState] using h.stateAlign) (by simpa only [hgSp] using h.stackRam)
      (by simpa only [hgSp] using h.stackAlign) honRam hon
      (by simpa only [hgOut] using h.outRam) (by simpa only [hgOut] using h.outAlign)
      (by simpa only [hgOut,hgSp,Call.Separate] using h.outSep)
    have hOutcome : Outcome.At r' (c.get 10) (Spec.transition true s (.relay idx on)) := by
      simpa [hgOut,Spec.transition,Spec.changed,Scratch.patched,hi] using hbOutcome
    have hFrame : ∀ x, (∀ i : Fin 20, x ≠ c.get 10+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 36, x ≠ Stack.base c+BitVec.ofNat 32 i.val) → r' x = r0 x := by
      simpa only [hgOut,hgSp] using hbFrame
    obtain ⟨d,hrun,hpost⟩ := Call.finish_local B c cd cb ram r' true s (.relay idx on)
      (Spec.transition true s (.relay idx on)) ne 57 h heRun ((haRun.trans hgRun).trans hbRun)
      hbPc (hbSp.trans hgSp) (hbCsr.trans hgCsr') (Upper.trans hgUpper hbUpper) hOutcome hFrame
    exact ⟨ne+57+9,⟨d,r'⟩,by omega,hrun,hpost⟩
  · have h0 : B.inRam (cg.get 10) 1 = true := by
      rw [hgOut]
      simpa using Memory.block_access (B := B) (p := c.get 10) (n := 20) (off := 0) (width := 1) h.outRam (by decide) (by decide)
    have h10 : B.inRam (cg.get 10+10#32) 1 = true := by
      rw [hgOut]
      exact Memory.block_access (B := B) (p := c.get 10) (n := 20) (off := 10) (width := 1) h.outRam (by decide) (by decide)
    obtain ⟨cb,hbRun,hbPc,hbSp,hbCsr,hbUpper⟩ := Errors.relay_range_full B cg r0 (by simpa [hi] using hgPc) h0 h10
    rw [hgOut] at hbRun
    let r' := Errors.result r0 (c.get 10) .noSuchRelay
    have hOutcome : Outcome.At r' (c.get 10) (Spec.transition true s (.relay idx on)) := by
      simp only [Spec.transition,Bool.not_true,ite_false,hi]
      exact Outcome.error _ _ _
    have hFrame : ∀ x, (∀ i : Fin 20, x ≠ c.get 10+BitVec.ofNat 32 i.val) → r' x = r0 x := by
      intro x hx
      exact Errors.result_frame r0 (c.get 10) x .noSuchRelay (by simpa using hx ⟨0,by decide⟩) (hx ⟨10,by decide⟩)
    obtain ⟨d,hrun,hpost⟩ := Call.finish B c cd cb ram r' true s (.relay idx on)
      (Spec.transition true s (.relay idx on)) ne 10 h heRun ((haRun.trans hgRun).trans hbRun)
      hbPc (hbSp.trans hgSp) (hbCsr.trans hgCsr') (Upper.trans hgUpper hbUpper) hOutcome hFrame
    exact ⟨ne+10+9,⟨d,r'⟩,by omega,hrun,hpost⟩
end E5R.Thermostat.Relay
