import Projects.thermostat.MainCloseCode
import Projects.thermostat.QuietBranch
import Projects.thermostat.HeadTargetMath
set_option autoImplicit false
namespace E5R.Thermostat.MainCloseCountBranch
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (served : Nat) (bound : served≤100)
    (hp : c.pc=0x80001262#32) (h18 : c.get 18=BitVec.ofNat 32 served) (h11 : c.get 11=100#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=(if 100≤served then 0x8000128c#32 else 0x80001266#32) ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨d,trace,pc,regs,csr⟩ := QuietBranch.contract B img c ram 0x80001262#32 4#32 0x2a#32 .geu 18 11 (decide (100≤served)) hp (by decide) (by decide) re2147488354
    (by rw [h18,h11];exact HeadTargetMath.geu served 100 (by omega) (by decide))
  refine ⟨d,trace,?_,regs,csr⟩
  simpa only [decide_eq_true_eq,show 0x80001262#32+0x2a#32=0x8000128c#32 by decide +kernel,show 0x80001262#32+4#32=0x80001266#32 by decide +kernel] using pc
end E5R.Thermostat.MainCloseCountBranch
