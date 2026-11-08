-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.HeaterReady
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.HeaterFrameQuiet
import Projects.thermostat.WriteTwoQuiet
set_option maxRecDepth 2000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.HeaterReady
theorem contract_full_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot)
    (kind : Fin 3) (out : Word) (h : Ready c s kind out)
    (hmem : Memory.Block B out 20) (hal : out.toNat % 2 = 0) :
    ∃ n d ram', n ≤ 21 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram'⟩ ∧ d.pc = 0x800001ac ∧
      Outcome.At ram' out (.ok ⟨some s,s⟩) ∧ d.get 2 = c.get 2 ∧ d.sameCsr c ∧
      (∀ x, (∀ i : Fin 20, x ≠ out+BitVec.ofNat 32 i.val) → ram' x = ram x) ∧ Upper.Frame c d := by
  have hm : c.get 10 = 0#32 ∨ c.get 10 = 1#32 ∨ c.get 10 = 2#32 := by
    rw [h.modeArg]
    exact Fields.mode_valid s.mode
  obtain ⟨n,d,hn,hrun,hpc,hval,hframe,hcsr⟩ := E5R.Thermostat.heater_full_contract_quiet B c ram h.pc hm
  have hdPc : d.pc = WriteTwo.start kind := by rw [hpc,h.ret,start_clear]
  have hdOut : d.get 21 = out := (hframe 21 (by decide) (by decide)).trans h.outPtr
  have hv : d.get 10 = if s.heater then 1 else 0 := by
    rw [h.modeArg,h.tempArg,h.setpointArg,Fields.heater,← h.settled] at hval
    exact hval
  have hslots : ∀ i : Fin 10, WriteTwo.byte (WriteTwo.regs d kind) i = Encoding.snapshotByte s i := by
    intro i
    by_cases hi : i.val = 8
    · have he : i = ⟨8,by decide⟩ := Fin.ext hi
      subst i
      rw [heater_slot,hv,Fields.bool_byte]
      rfl
    · exact (slots_frame c d kind i hi hframe).trans (h.slots i hi)
  have hb := E5R.Thermostat.WriteTwo.contract_quiet B d ram kind hdPc
    (by simpa only [hdOut] using hmem) (by simpa only [hdOut] using hal)
  rw [hdOut] at hb
  refine ⟨n+WriteTwo.steps kind,d.goto 0x800001ac,WriteTwo.write ram out (WriteTwo.regs d kind),
    by have := WriteTwo.steps_le kind;omega,hrun.trans hb,rfl,?_,?_,?_,?_,?_⟩
  · exact WriteTwo.source ram out (WriteTwo.regs d kind) s hslots
  · exact hframe 2 (by decide) (by decide)
  · exact (Core.sameCsr_goto _ _).trans hcsr
  · intro x hx;exact WriteTwo.frame ram out x (WriteTwo.regs d kind) hx

  · intro r hr
    exact hframe r (Upper.ne_low r hr 10 (by decide)) (Upper.ne_low r hr 13 (by decide))

end E5R.Thermostat.HeaterReady
