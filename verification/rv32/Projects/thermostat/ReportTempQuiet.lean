-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ReportTemp
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.CallQuiet
import Projects.thermostat.HeaterReadyQuiet
import Projects.thermostat.PrepareQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.ReportTemp
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (admin : Bool) (s : Spec.Snapshot) (dc : BitVec 16)
    (h : Call.Pre B c ram admin s (.reportTemp dc)) :
    ∃ n m, n ≤ 56 ∧ Quiet.Steps B img n ⟨c,ram⟩ m ∧
      Call.Post c ram m (Spec.transition admin s (.reportTemp dc)) := by
  obtain ⟨ne,cd,hne,heRun,he⟩ := E5R.Thermostat.Call.enter_quiet B c ram admin s (.reportTemp dc) h
  let r0 := Stack.save c ram
  have hlo := he.commandAt ⟨2,by decide⟩ (Encoding.shortByte dc false) rfl
  have hhi := he.commandAt ⟨3,by decide⟩ (Encoding.shortByte dc true) rfl
  change r0 (c.get 13+2#32) = Encoding.shortByte dc false at hlo
  change r0 (c.get 13+3#32) = Encoding.shortByte dc true at hhi
  have hInput : Prepare.Input B cd r0 ⟨1,by decide⟩ s.mode dc := by
    change (cd.get 13+2#32).toNat % 2 = 0 ∧ B.inRam (cd.get 13+2#32) 2 = true ∧
      extend .h true (ramRead r0 (cd.get 13+2#32) .h) = dc.signExtend 32
    rw [he.commandPtr]
    refine ⟨Memory.half_aligned (c.get 13) 1 h.commandAlign,
      Memory.block_access (B := B) (p := c.get 13) (n := 4) (off := 2) (width := 2) h.commandRam (by decide) (by decide),?_⟩
    exact Fields.short_load r0 (c.get 13+2#32) dc hlo (by simpa [BitVec.add_assoc] using hhi)
  obtain ⟨np,ch,hnp,hpRun,hReady,hpSp,hpCsr,hpUpper⟩ := E5R.Thermostat.Prepare.contract_full_quiet B cd r0 ⟨1,by decide⟩ s s.mode dc
    (by simpa [Dispatch.entry,Encoding.tagFin,Prepare.start] using he.pc)
    (by simpa only [he.statePtr] using he.stateAt)
    (by simpa only [he.statePtr] using h.stateRam)
    (by simpa only [he.statePtr] using h.stateAlign) hInput
  have hReady' : HeaterReady.Ready ch (Prepare.next ⟨1,by decide⟩ s s.mode dc) ⟨1,by decide⟩ (c.get 10) := by
    simpa only [he.outPtr] using hReady
  obtain ⟨nh,cb,r',hnh,hhRun,hhPc,hhOutcome,hhSp,hhCsr,hhFrame,hhUpper⟩ := E5R.Thermostat.HeaterReady.contract_full_quiet B ch r0
    (Prepare.next ⟨1,by decide⟩ s s.mode dc) ⟨1,by decide⟩ (c.get 10) hReady' h.outRam h.outAlign
  have hOut : Outcome.At r' (c.get 10) (Spec.transition admin s (.reportTemp dc)) := by
    simpa [Spec.transition,Spec.changed,Prepare.next] using hhOutcome
  obtain ⟨d,hrun,hpost⟩ := E5R.Thermostat.Call.finish_quiet B c cd cb ram r' admin s (.reportTemp dc)
    (Spec.transition admin s (.reportTemp dc)) ne (np+nh) h heRun (hpRun.trans hhRun)
    hhPc (hhSp.trans (hpSp.trans he.sp)) (hhCsr.trans (hpCsr.trans he.csr)) (Upper.trans (Upper.trans he.upper hpUpper) hhUpper) hOut hhFrame
  exact ⟨ne+(np+nh)+9,⟨d,r'⟩,by omega,hrun,hpost⟩

end E5R.Thermostat.ReportTemp
