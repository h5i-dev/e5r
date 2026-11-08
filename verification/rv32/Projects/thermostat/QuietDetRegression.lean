import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.ObservedDetRegression
namespace E5R.Thermostat.QuietDetRegression
open E5R E5R.Thermostat
abbrev B := ObservedDetRegression.B

def image : List Segment := [⟨0,[3,193,0,0],true⟩]
abbrev core := ObservedDetRegression.core
abbrev ram := ObservedDetRegression.ram

theorem decoded : fetchDecode image 0#32=some (.load .b false 2 1 0#32,4#32) := by decide +kernel

theorem used_good : QuietDet.Good (.load .b false 2 1 0#32)=true := by decide +kernel
theorem discarded_bad : QuietDet.Good (.load .b false 0 1 0#32)=false := by decide +kernel

/-- A used device read is not deterministic for any proposed final machine. -/
theorem used_mmio_not_deterministic (d : Machine) : ¬DetStep B image ⟨core,ram⟩ d := by
  intro h
  have source := QuietLoad.source B image core d.core ram d.ram .b false 2 0x10000000#32 4#32 (by decide) (by
    intro o
    have hs := stepInstr_of (B := B) (img := image) (m := (⟨core,ram⟩ : Machine)) (o := o) (by decide) decoded
    have he := hs.symm.trans (h o)
    simpa only [exec_load,show core.get 1=0x10000000#32 by rfl,BitVec.add_zero,show core.pc+4#32=4#32 by rfl] using he)
  rcases source with hr|⟨v,hv⟩
  · have noRam : B.inRam 0x10000000#32 Width.b.bytes=false := by decide +kernel
    rw [noRam] at hr;cases hr
  · have noRom : romRead? image (0x10000000#32).toNat Width.b.bytes false=none := by decide +kernel
    rw [noRom] at hv;cases hv

/-- Discarding a device value can be deterministic, but remains observable
    and fails the promotion side condition. -/
theorem discarded_deterministic : DetStep B ObservedDetRegression.image ⟨core,ram⟩ ⟨core.goto 4#32,ram⟩ :=
  ObservedDetRegression.deterministic

theorem discarded_not_quiet : ¬Quiet.Step B ObservedDetRegression.image ⟨core,ram⟩ ⟨core.goto 4#32,ram⟩ :=
  ObservedDetRegression.not_quiet

/-- The existing RAM evaluator refuses even a discarded MMIO load. -/
theorem evaluator_refuses_mmio : RamRun.run B ObservedDetRegression.image 1 ⟨core,ram⟩=none := by decide +kernel
end E5R.Thermostat.QuietDetRegression
