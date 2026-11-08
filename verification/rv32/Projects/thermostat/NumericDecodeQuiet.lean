-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.NumericDecode
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.NumericCallQuiet
import Projects.thermostat.NumericResultQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.NumericDecode
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8)) (report : Bool)
    (hs : Bytes.Span B ram p xs) (hp : c.pc = NumericCall.start report)
    (h8 : c.get 8 = p) (h9 : c.get 9 = BitVec.ofNat 32 xs.length) :
    ∃ d n, n ≤ 116 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002212#32 ∧
      WireSpec.ResultWord (d.get 10) (WireSpec.number (if report then Spec.Command.reportTemp else Spec.Command.setpoint) xs) ∧
      (∀ r : Reg, r ≠ 1 → r.val < 10 ∨ 16 < r.val → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,n,hn,ht,hpc,hparsed,hra,hregs,hcsr⟩ := E5R.Thermostat.NumericCall.contract_quiet B c ram p xs report hs hp h8 h9
  obtain ⟨d,k,hk,hafter,dpc,dresult,dregs,dcsr⟩ := E5R.Thermostat.NumericResult.contract_quiet B a ram report (DecimalSpec.parse xs)
    (by simpa only [NumericCall.ret] using hpc) hparsed
  refine ⟨d,n+k,by omega,ht.trans hafter,dpc,?_,?_,dcsr.trans hcsr⟩
  · rw [←NumericResult.as_number report xs]
    exact dresult
  · intro r h1 hr
    exact (dregs r (Decimal.outside r hr 10 (by decide)) (Decimal.outside r hr 11 (by decide))
      (Decimal.outside r hr 12 (by decide))).trans (hregs r h1 hr)

end E5R.Thermostat.NumericDecode
