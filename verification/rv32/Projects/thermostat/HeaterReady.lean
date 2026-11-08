import Projects.thermostat.Upper
import Projects.thermostat.Fields
import Projects.thermostat.WriteTwo

set_option maxRecDepth 2000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeaterReady
open E5R E5R.Thermostat

/-- Exact live-register requirements for the original heater call and success tail. -/
structure Ready (c : Core) (s : Spec.Snapshot) (kind : Fin 3) (out : Word) : Prop where
  pc : c.pc = 0x80000036
  ret : c.get 1 = WriteTwo.start kind
  modeArg : c.get 10 = Fields.modeWord s.mode
  tempArg : c.get 11 = s.temp.signExtend 32
  setpointArg : c.get 12 = s.setpoint.signExtend 32
  outPtr : c.get 21 = out
  settled : s.heater = Spec.heater s.mode s.temp s.setpoint
  slots : ∀ i : Fin 10, i.val ≠ 8 → WriteTwo.byte (WriteTwo.regs c kind) i = Encoding.snapshotByte s i

theorem start_clear (kind : Fin 3) : WriteTwo.start kind &&& ~~~1 = WriteTwo.start kind := by
  have hi := kind.isLt
  have hc : kind.val = 0 ∨ kind.val = 1 ∨ kind.val = 2 := by omega
  rcases hc with h|h|h <;> simp [WriteTwo.start,h]

theorem slots_frame (c d : Core) (kind : Fin 3) (i : Fin 10) (hi : i.val ≠ 8)
    (hf : ∀ r : Reg, r ≠ 10 → r ≠ 13 → d.get r = c.get r) :
    WriteTwo.byte (WriteTwo.regs d kind) i = WriteTwo.byte (WriteTwo.regs c kind) i := by
  have hk := kind.isLt
  have hc : kind.val = 0 ∨ kind.val = 1 ∨ kind.val = 2 := by omega
  have hx := i.isLt
  have hd : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨
    i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 := by omega
  rcases hc with hk|hk|hk
  all_goals
    rcases hd with hx|hx|hx|hx|hx|hx|hx|hx|hx|hx
    all_goals first
    | exact False.elim (hi hx)
    | simp [WriteTwo.byte,WriteTwo.regs,hk,hx,hf]

theorem heater_slot (c : Core) (kind : Fin 3) :
    WriteTwo.byte (WriteTwo.regs c kind) ⟨8,by decide⟩ = byteOf (c.get 10) 0 := by
  have hk := kind.isLt
  have hc : kind.val = 0 ∨ kind.val = 1 ∨ kind.val = 2 := by omega
  rcases hc with h|h|h <;> simp [WriteTwo.byte,WriteTwo.regs,h]

/-- Compose the machine-code heater theorem with each actual success tail.
    Ready is discharged by the instruction-level argument-loading prefixes. -/
theorem contract_full (B : Board) (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot)
    (kind : Fin 3) (out : Word) (h : Ready c s kind out)
    (hmem : Memory.Block B out 20) (hal : out.toNat % 2 = 0) :
    ∃ n d ram', n ≤ 21 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram'⟩ ∧ d.pc = 0x800001ac ∧
      Outcome.At ram' out (.ok ⟨some s,s⟩) ∧ d.get 2 = c.get 2 ∧ d.sameCsr c ∧
      (∀ x, (∀ i : Fin 20, x ≠ out+BitVec.ofNat 32 i.val) → ram' x = ram x) ∧ Upper.Frame c d := by
  have hm : c.get 10 = 0#32 ∨ c.get 10 = 1#32 ∨ c.get 10 = 2#32 := by
    rw [h.modeArg]
    exact Fields.mode_valid s.mode
  obtain ⟨n,d,hn,hrun,hpc,hval,hframe,hcsr⟩ := heater_full_contract B c ram h.pc hm
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
  have hb := WriteTwo.contract B d ram kind hdPc
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

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (s : Spec.Snapshot)
    (kind : Fin 3) (out : Word) (h : Ready c s kind out)
    (hmem : Memory.Block B out 20) (hal : out.toNat % 2 = 0) :
    ∃ n d ram', n ≤ 21 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram'⟩ ∧ d.pc = 0x800001ac ∧
      Outcome.At ram' out (.ok ⟨some s,s⟩) ∧ d.get 2 = c.get 2 ∧ d.sameCsr c ∧
      (∀ x, (∀ i : Fin 20, x ≠ out+BitVec.ofNat 32 i.val) → ram' x = ram x) := by
  obtain ⟨n,d,ramx,hn,hr,hpc,hout,hsp,hcsr,hmemframe,_⟩ := contract_full B c ram s kind out h hmem hal
  exact ⟨n,d,ramx,hn,hr,hpc,hout,hsp,hcsr,hmemframe⟩

end E5R.Thermostat.HeaterReady
