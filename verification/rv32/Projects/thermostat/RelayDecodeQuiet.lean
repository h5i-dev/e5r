-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.RelayDecode
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.RelayCallQuiet
import Projects.thermostat.RelayResultQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.RelayDecode
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (req p : Word)
    (first : Option (List (BitVec 8))) (xs : List (BitVec 8))
    (h : Param.Pre B ram req first) (hs : Bytes.Span B ram p xs)
    (hp : c.pc = 0x80002194#32) (hreq : c.get 10 = req)
    (h8 : c.get 8 = p) (h9 : c.get 9 = BitVec.ofNat 32 xs.length) :
    ∃ d n, n ≤ 232 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002212#32 ∧
      WireSpec.ResultWord (d.get 10) (WireSpec.relay first xs) ∧
      (∀ r : Reg, r ≠ 1 → r ≠ 5 → r.val < 10 ∨ 17 < r.val → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨c1,n,hn,ht,hpc,hval,hregs,hcsr⟩ := E5R.Thermostat.RelayCall.contract_quiet B c ram req first h hp hreq
  obtain ⟨d,k,hk,td,pcd,vd,rd,cd⟩ := E5R.Thermostat.RelayResult.contract_quiet B c1 ram p xs (first.bind WireSpec.parseU32) hs hpc
    ((hregs 8 (by decide) (by decide) (by decide)).trans h8)
    ((hregs 9 (by decide) (by decide) (by decide)).trans h9) hval
  refine ⟨d,n+k,by omega,ht.trans td,pcd,?_,?_,cd.trans hcsr⟩
  · rw [←RelayResult.as_relay];exact vd
  · intro r h1 h5 hr
    exact (rd r (RelayCall.outside r 10 hr (by decide)) (RelayCall.outside r 11 hr (by decide))
      (RelayCall.outside r 12 hr (by decide)) (RelayCall.outside r 13 hr (by decide))
      (RelayCall.outside r 14 hr (by decide)) (RelayCall.outside r 15 hr (by decide))).trans (hregs r h1 h5 hr)

end E5R.Thermostat.RelayDecode
