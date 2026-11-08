import Projects.thermostat.ObservedDet
import Projects.thermostat.Quiet
import Projects.thermostat.ObservedWitness
namespace E5R.Thermostat.ObservedDetRegression
open E5R E5R.Thermostat
abbrev B := ObservedWitness.board

def image : List Segment := [⟨0,[3,192,0,0],true⟩]
def core : Core := ⟨0,(fun r => if r=1 then 0x10000000#32 else 0#32),false,false,3,0,0,0,0,0,false⟩
def ram : Word → BitVec 8 := fun _ => 0#8

/-- A hand-encoded LBU x0,0(x1) regression, separate from the firmware image. -/
theorem decoded : fetchDecode image 0#32=some (.load .b false 0 1 0#32,4#32) := by decide +kernel

theorem observed (o : Oracle) : Observed.stepInstr B image ⟨core,ram⟩ o=
    ⟨.ok (core.goto 4#32) ram [],[⟨0x10000000#32,.b,devVal .b (o 0),0⟩]⟩ := by
  rw [Observed.stepInstr_of (by decide) decoded,exec_load,show core.get 1=0x10000000#32 by rfl,BitVec.add_zero]
  unfold Observed.interp
  rw [ite_eq_right (by decide),show B.inRam 0x10000000#32 Width.b.bytes=false by decide,
    ite_eq_right (by decide),show romRead? image (0x10000000#32).toNat Width.b.bytes false=none by decide +kernel]
  rfl

theorem deterministic : DetStep B image ⟨core,ram⟩ ⟨core.goto 4#32,ram⟩ := by
  intro o
  rw [←Observed.erase_step B image ⟨core,ram⟩ o,observed]

theorem complete : ∃ reads, Observed.Steps B image 1 ⟨core,ram⟩ ⟨core.goto 4#32,ram⟩ reads [] :=
  ObservedDet.complete (DetSteps.single deterministic)

theorem not_quiet : ¬Quiet.Step B image ⟨core,ram⟩ ⟨core.goto 4#32,ram⟩ := by
  intro h
  have hh := h (fun _ => 0#32)
  rw [observed] at hh
  have hr := congrArg Observed.Result.reads hh
  cases hr
end E5R.Thermostat.ObservedDetRegression
