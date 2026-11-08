import Projects.thermostat.MainCloseCode
import Projects.thermostat.QuietBranch
import Projects.thermostat.MainCloseTokenMath
set_option autoImplicit false
namespace E5R.Thermostat.MainCloseTokenLength
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (n : Nat) (bound : n<2^32)
    (hp : c.pc=0x80002608#32) (h24 : c.get 24=BitVec.ofNat 32 n) (h18 : c.get 18=5#32) :
    ∃ d, Quiet.Steps B img 1 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if n=5 then 0x8000260c#32 else 0x800025d4#32) ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨d,trace,pc,regs,csr⟩ := QuietBranch.contract B img c ram 0x80002608#32 4#32 0xffffffcc#32 .ne 24 18
    (decide (n≠5)) hp (by decide) (by decide) re2147493384 (by rw [h24,h18];exact MainCloseTokenMath.notFive n bound)
  refine ⟨d,trace,?_,regs,csr⟩
  by_cases equal : n=5 <;> simpa [equal] using pc
end E5R.Thermostat.MainCloseTokenLength
