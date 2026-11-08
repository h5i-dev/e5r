-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.SetMode
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.AuthorizeQuiet
import Projects.thermostat.CallQuiet
import Projects.thermostat.HeaterReadyQuiet
import Projects.thermostat.PrepareQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.SetMode
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot) (mode : Spec.Mode)
    (h : Call.Pre B c ram true s (.mode mode)) :
    ∃ n m, n ≤ 58 ∧ Quiet.Steps B img n ⟨c,ram⟩ m ∧ Call.Post c ram m (Spec.transition true s (.mode mode)) := by
  obtain ⟨ne,cd,hne,heRun,he⟩ := E5R.Thermostat.Call.enter_quiet B c ram true s (.mode mode) h
  let r0 := Stack.save c ram
  have hActor : r0 (cd.get 11) = 1#8 := by
    rw [he.actorPtr]
    exact he.actorAt
  have hActorRam : B.inRam (cd.get 11) 1 = true := by
    rw [he.actorPtr]
    simpa using Memory.block_access (B := B) (p := c.get 11) (n := 1) (off := 0) (width := 1)
      h.actorRam (by decide) (by decide)
  obtain ⟨ca,haRun,haPc,haRegs,haCsr⟩ := E5R.Thermostat.Authorize.contract_quiet B cd r0 ⟨2,by decide⟩
    (by exact he.pc) hActorRam hActor
  have hCommand : ca.get 13 = c.get 13 := (haRegs 13 (by decide)).trans he.commandPtr
  have hState : ca.get 12 = c.get 12 := (haRegs 12 (by decide)).trans he.statePtr
  have hOut : ca.get 10 = c.get 10 := (haRegs 10 (by decide)).trans he.outPtr
  have hInput : Prepare.Input B ca r0 ⟨0,by decide⟩ mode 0#16 := by
    change B.inRam (ca.get 13+1#32) 1 = true ∧ r0 (ca.get 13+1#32) = Encoding.modeByte mode
    rw [hCommand]
    refine ⟨Memory.block_access (B := B) (p := c.get 13) (n := 4) (off := 1) (width := 1)
      h.commandRam (by decide) (by decide),?_⟩
    exact he.commandAt ⟨1,by decide⟩ (Encoding.modeByte mode) rfl
  obtain ⟨np,ch,hnp,hpRun,hReady,hpSp,hpCsr,hpUpper⟩ := E5R.Thermostat.Prepare.contract_full_quiet B ca r0 ⟨0,by decide⟩ s mode 0#16
    (by simpa [Authorize.next,Prepare.start] using haPc)
    (by simpa only [hState] using he.stateAt)
    (by simpa only [hState] using h.stateRam)
    (by simpa only [hState] using h.stateAlign) hInput
  have hReady' : HeaterReady.Ready ch (Prepare.next ⟨0,by decide⟩ s mode 0#16) ⟨0,by decide⟩ (c.get 10) := by
    simpa only [hOut] using hReady
  obtain ⟨nh,cb,r',hnh,hhRun,hhPc,hhOutcome,hhSp,hhCsr,hhFrame,hhUpper⟩ := E5R.Thermostat.HeaterReady.contract_full_quiet B ch r0
    (Prepare.next ⟨0,by decide⟩ s mode 0#16) ⟨0,by decide⟩ (c.get 10) hReady' h.outRam h.outAlign
  have hOutcome : Outcome.At r' (c.get 10) (Spec.transition true s (.mode mode)) := by
    simpa [Spec.transition,Spec.changed,Prepare.next] using hhOutcome
  have hSp : cb.get 2 = Stack.base c := hhSp.trans (hpSp.trans ((haRegs 2 (by decide)).trans he.sp))
  have hCsr : cb.sameCsr c := hhCsr.trans (hpCsr.trans (haCsr.trans he.csr))
  obtain ⟨d,hrun,hpost⟩ := E5R.Thermostat.Call.finish_quiet B c cd cb ram r' true s (.mode mode)
    (Spec.transition true s (.mode mode)) ne (2+np+nh) h heRun ((haRun.trans hpRun).trans hhRun)
    hhPc hSp hCsr (Upper.trans (Upper.trans (Upper.trans he.upper (fun r hr => haRegs r (Upper.ne_low r hr 11 (by decide)))) hpUpper) hhUpper) hOutcome hhFrame
  exact ⟨ne+(2+np+nh)+9,⟨d,r'⟩,by omega,hrun,hpost⟩

end E5R.Thermostat.SetMode
