import Projects.thermostat.RelayCall
import Projects.thermostat.RelayResult
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.RelayDecode
open E5R E5R.Thermostat

/-- Request capture bytes are parsed by the real param_u32, checked for u8 range,
    and combined with the actual body literals and packed enum construction. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (req p : Word)
    (first : Option (List (BitVec 8))) (xs : List (BitVec 8))
    (h : Param.Pre B ram req first) (hs : Bytes.Span B ram p xs)
    (hp : c.pc = 0x80002194#32) (hreq : c.get 10 = req)
    (h8 : c.get 8 = p) (h9 : c.get 9 = BitVec.ofNat 32 xs.length) :
    ∃ d n, n ≤ 232 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002212#32 ∧
      WireSpec.ResultWord (d.get 10) (WireSpec.relay first xs) ∧
      (∀ r : Reg, r ≠ 1 → r ≠ 5 → r.val < 10 ∨ 17 < r.val → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨c1,n,hn,ht,hpc,hval,hregs,hcsr⟩ := RelayCall.contract B c ram req first h hp hreq
  obtain ⟨d,k,hk,td,pcd,vd,rd,cd⟩ := RelayResult.contract B c1 ram p xs (first.bind WireSpec.parseU32) hs hpc
    ((hregs 8 (by decide) (by decide) (by decide)).trans h8)
    ((hregs 9 (by decide) (by decide) (by decide)).trans h9) hval
  refine ⟨d,n+k,by omega,ht.trans td,pcd,?_,?_,cd.trans hcsr⟩
  · rw [←RelayResult.as_relay];exact vd
  · intro r h1 h5 hr
    exact (rd r (RelayCall.outside r 10 hr (by decide)) (RelayCall.outside r 11 hr (by decide))
      (RelayCall.outside r 12 hr (by decide)) (RelayCall.outside r 13 hr (by decide))
      (RelayCall.outside r 14 hr (by decide)) (RelayCall.outside r 15 hr (by decide))).trans (hregs r h1 h5 hr)

theorem closed_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (req p : Word)
    (first : Option (List (BitVec 8))) (xs : List (BitVec 8))
    (h : Param.Pre B ram req first) (hs : Bytes.Span B ram p xs)
    (hp : c.pc = 0x80002194#32) (hreq : c.get 10 = req)
    (h8 : c.get 8 = p) (h9 : c.get 9 = BitVec.ofNat 32 xs.length) (hm : c.mie_ = false) :
    ∃ d n, n ≤ 232 ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002212#32 ∧
      WireSpec.ResultWord (d.get 10) (WireSpec.relay first xs) ∧
      (∀ r : Reg, r ≠ 1 → r ≠ 5 → r.val < 10 ∨ 17 < r.val → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨d,n,hn,ht,hpc,hval,hregs,hcsr⟩ := contract B c ram req p first xs h hs hp hreq h8 h9
  exact ⟨d,n,hn,Interrupt.close ht hm,hpc,hval,hregs,hcsr⟩
end E5R.Thermostat.RelayDecode
