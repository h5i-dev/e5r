import Projects.thermostat.NumericCall
import Projects.thermostat.NumericResult
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.NumericDecode
open E5R E5R.Thermostat

/-- The actual caller, universal byte parser, Option dispatch and enum packing
    for both numeric commands. This starts before the real call, with bytes. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8)) (report : Bool)
    (hs : Bytes.Span B ram p xs) (hp : c.pc = NumericCall.start report)
    (h8 : c.get 8 = p) (h9 : c.get 9 = BitVec.ofNat 32 xs.length) :
    ∃ d n, n ≤ 116 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002212#32 ∧
      WireSpec.ResultWord (d.get 10) (WireSpec.number (if report then Spec.Command.reportTemp else Spec.Command.setpoint) xs) ∧
      (∀ r : Reg, r ≠ 1 → r.val < 10 ∨ 16 < r.val → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,n,hn,ht,hpc,hparsed,hra,hregs,hcsr⟩ := NumericCall.contract B c ram p xs report hs hp h8 h9
  obtain ⟨d,k,hk,hafter,dpc,dresult,dregs,dcsr⟩ := NumericResult.contract B a ram report (DecimalSpec.parse xs)
    (by simpa only [NumericCall.ret] using hpc) hparsed
  refine ⟨d,n+k,by omega,ht.trans hafter,dpc,?_,?_,dcsr.trans hcsr⟩
  · rw [←NumericResult.as_number report xs]
    exact dresult
  · intro r h1 hr
    exact (dregs r (Decimal.outside r hr 10 (by decide)) (Decimal.outside r hr 11 (by decide))
      (Decimal.outside r hr 12 (by decide))).trans (hregs r h1 hr)

theorem closed_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8)) (report : Bool)
    (hs : Bytes.Span B ram p xs) (hp : c.pc = NumericCall.start report)
    (h8 : c.get 8 = p) (h9 : c.get 9 = BitVec.ofNat 32 xs.length) (hm : c.mie_ = false) :
    ∃ d n, n ≤ 116 ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002212#32 ∧
      WireSpec.ResultWord (d.get 10) (WireSpec.number (if report then Spec.Command.reportTemp else Spec.Command.setpoint) xs) ∧
      (∀ r : Reg, r ≠ 1 → r.val < 10 ∨ 16 < r.val → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨d,n,hn,ht,hpc,hresult,hframe,hcsr⟩ := contract B c ram p xs report hs hp h8 h9
  exact ⟨d,n,hn,Interrupt.close ht hm,hpc,hresult,hframe,hcsr⟩

end E5R.Thermostat.NumericDecode
