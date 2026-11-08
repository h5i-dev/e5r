import Projects.thermostat.HeadClNumberMath
import Projects.thermostat.HeadClMulRaw
import Projects.thermostat.HeadClLowRaw
import Projects.thermostat.HeadClCarryRaw
namespace E5R.Thermostat.HeadClAccumulate
open E5R E5R.Thermostat

/-- Thirteen actual RV32 multiply/shift/add/carry instructions, specialized to
    the previous accepted body limit. The zero high word follows from bounds. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (acc : Nat) (byte : BitVec 8)
    (hp : c.pc=0x8000321e#32) (h14 : c.get 14=BitVec.ofNat 32 acc) (h13 : c.get 13=0#32)
    (h16 : c.get 16=10#32) (h30 : c.get 30=BitVec.ofNat 32 byte.toNat)
    (bound : acc≤1024) (digit : DecimalSpec.digit byte=true) :
    ∃ d, Quiet.Steps B img 13 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80003244#32 ∧
      d.get 14=BitVec.ofNat 32 (HeadClNumberMath.next acc byte) ∧ d.get 13=0#32 ∧
      (∀ r : Reg, r≠12 → r≠29 → r≠14 → r≠30 → r≠13 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,t0,p0,upper,product,shifted,fa,sa⟩ := HeadClMulRaw.contract B c ram _ _ h14 h16 hp
  rw [HeadClNumberMath.mulhu_zero acc bound] at upper
  rw [HeadClNumberMath.product] at product
  obtain ⟨b,t1,p1,low,highShift,highSum,fb,sb⟩ := HeadClLowRaw.contract B a ram _ 0#32 _
    ((fa 30 (by decide) (by decide) (by decide)).trans h30)
    ((fa 13 (by decide) (by decide) (by decide)).trans h13) product p0
  rw [HeadClNumberMath.low acc byte digit] at low
  have zeroHigh : b.get 13=0#32 := highSum.trans (by decide +kernel)
  have productAt : b.get 29=BitVec.ofNat 32 (10*acc) := (fb 29 (by decide) (by decide) (by decide)).trans product
  have upperAt : b.get 12=0#32 := (fb 12 (by decide) (by decide) (by decide)).trans upper
  obtain ⟨d,t2,p2,carry,high,fd,sd⟩ := HeadClCarryRaw.contract B b ram _ _ 0#32 0#32 low productAt zeroHigh upperAt p1
  rw [HeadClNumberMath.carry_zero acc byte bound digit] at high
  refine ⟨d,by simpa using (t0.trans t1).trans t2,p2,(fd 14 (by decide) (by decide)).trans low,
    high.trans (by decide +kernel),?_,sd.trans (sb.trans sa)⟩
  intro r h12 h29 h14 h30 h13
  exact (fd r h29 h13).trans ((fb r h14 h30 h13).trans (fa r h12 h29 h14))
end E5R.Thermostat.HeadClAccumulate
