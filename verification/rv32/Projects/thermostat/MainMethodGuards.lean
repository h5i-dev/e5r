import Projects.thermostat.MainMethodDecodeCode
import Projects.thermostat.QuietBranch
namespace E5R.Thermostat.MainMethodGuards
open E5R E5R.Thermostat

theorem below (a b : Nat) (ha : a≤2048) (hb : b≤2048) (order : b≤a) :
    taken .ltu (BitVec.ofNat 32 a) (BitVec.ofNat 32 b)=false := by
  simp only [taken,BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : a<2^32),Nat.mod_eq_of_lt (by omega : b<2^32)]
  exact decide_eq_false (by omega)

/-- Actual slice guards. Ordered method spans and availability imply both
    branches avoid the real panic path; no success-branch assumption is added. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (start finish used : Nat)
    (hp : c.pc=0x80000d50#32) (h7 : c.get 7=BitVec.ofNat 32 start)
    (h11 : c.get 11=BitVec.ofNat 32 finish) (h24 : c.get 24=BitVec.ofNat 32 used)
    (ordered : start≤finish) (available : finish≤used) (bound : used≤2048) :
    ∃ d, Quiet.Steps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80000d58#32 ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,t0,pa,ar,ac⟩ := QuietBranch.contract B img c ram 0x80000d50#32 4#32 0xf3c#32 .ltu 11 7 false hp (by decide) (by decide) re2147487056 (by rw [h11,h7];exact below finish start (by omega) (by omega) ordered)
  have pa' : a.pc=0x80000d54#32 := pa
  obtain ⟨d,t1,pd,dr,dc⟩ := QuietBranch.contract B img a ram 0x80000d54#32 4#32 0xf38#32 .ltu 24 11 false pa' (by decide) (by decide) re2147487060 (by rw [ar 24,ar 11,h24,h11];exact below used finish bound (by omega) available)
  exact ⟨d,t0.trans t1,pd,fun r => (dr r).trans (ar r),dc.trans ac⟩
end E5R.Thermostat.MainMethodGuards
