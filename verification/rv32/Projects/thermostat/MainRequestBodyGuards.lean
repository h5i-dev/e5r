import Projects.thermostat.MainRequestBuildCode
import Projects.thermostat.MainMethodGuards
import Projects.thermostat.QuietBranch
namespace E5R.Thermostat.MainRequestBodyGuards
open E5R E5R.Thermostat

/-- Actual slice guards. Ordered method spans and availability imply both
    branches avoid the real panic path; no success-branch assumption is added. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (start finish used : Nat)
    (hp : c.pc=0x80001160#32) (h20 : c.get 20=BitVec.ofNat 32 start)
    (h25 : c.get 25=BitVec.ofNat 32 finish) (h24 : c.get 24=BitVec.ofNat 32 used)
    (ordered : start≤finish) (available : finish≤used) (bound : used≤2048) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001168#32 ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,t0,pa,ar,ac⟩ := QuietBranch.contract B img c ram 0x80001160#32 4#32 0xb40#32 .ltu 25 20 false hp (by decide) (by decide) re2147488096 (by rw [h25,h20];exact MainMethodGuards.below finish start (by omega) (by omega) ordered)
  have pa' : a.pc=0x80001164#32 := pa
  obtain ⟨d,t1,pd,dr,dc⟩ := QuietBranch.contract B img a ram 0x80001164#32 4#32 0xb3c#32 .ltu 24 25 false pa' (by decide) (by decide) re2147488100 (by rw [ar 24,ar 25,h24,h25];exact MainMethodGuards.below used finish bound (by omega) available)
  exact ⟨d,t0.trans t1,pd,fun r => (dr r).trans (ar r),dc.trans ac⟩
end E5R.Thermostat.MainRequestBodyGuards
