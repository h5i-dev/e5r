import Projects.thermostat.CommandSpec
import Projects.thermostat.ReadPack
import Projects.thermostat.NumericDecode
import Projects.thermostat.ModeDecode
import Projects.thermostat.RelayDecode
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.CommandBody
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (req pathPtr bodyPtr : Word)
    (path body : List (BitVec 8)) (first : Option (List (BitVec 8)))
    (hpath : PathDispatch.PathAt B ram req pathPtr path) (hparam : Param.Pre B ram req first)
    (hbody : Bytes.Span B ram bodyPtr body) (hp : c.pc = 0x80001fb4#32) (hreq : c.get 10 = req)
    (h8 : c.get 8 = bodyPtr) (h9 : c.get 9 = BitVec.ofNat 32 body.length) :
    ∃ d n, n ≤ 267 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002212#32 ∧
      WireSpec.ResultWord (d.get 10) (CommandSpec.value path body first) ∧
      (∀ r : Reg, r ≠ 1 → r ≠ 5 → r.val < 10 ∨ 17 < r.val → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,n,hn,ht,hpc,hregs,hcsr⟩ := PathSelect.contract B c ram req pathPtr path hpath hp hreq
  rw [CommandSpec.target] at hpc
  have a8 : a.get 8 = bodyPtr := (hregs 8 (by decide) (by decide) (by decide)).trans h8
  have a9 : a.get 9 = BitVec.ofNat 32 body.length := (hregs 9 (by decide) (by decide) (by decide)).trans h9
  have a10 : a.get 10 = req := (hregs 10 (by decide) (by decide) (by decide)).trans hreq
  by_cases hs : path = WireSpec.ascii "/state"
  · have apc : a.pc = 0x80002016#32 := by simpa only [ite_eq_left hs] using hpc
    obtain ⟨d,td,pcd,vd,rd,cd⟩ := ReadPack.contract B a ram apc
    refine ⟨d,n+6,by omega,ht.trans td,pcd,?_,?_,cd.trans hcsr⟩
    · simpa only [CommandSpec.value,ite_eq_left hs] using vd
    · intro r h1 h5 hr
      exact (rd r (RelayCall.outside r 10 hr (by decide)) (RelayCall.outside r 11 hr (by decide)) (RelayCall.outside r 12 hr (by decide))).trans (hregs r (RelayCall.outside r 11 hr (by decide)) (RelayCall.outside r 12 hr (by decide)) (RelayCall.outside r 13 hr (by decide)))
  ·
    by_cases hpnt : path = WireSpec.ascii "/setpoint"
    · have apc : a.pc = 0x8000208c#32 := by simpa only [ite_eq_right hs,ite_eq_left hpnt] using hpc
      obtain ⟨d,k,hk,td,pcd,vd,rd,cd⟩ := NumericDecode.contract B a ram bodyPtr body false hbody apc a8 a9
      refine ⟨d,n+k,by omega,ht.trans td,pcd,?_,?_,cd.trans hcsr⟩
      · simpa only [CommandSpec.value,ite_eq_right hs,ite_eq_left hpnt,Bool.false_eq_true,ite_false,ite_true] using vd
      · intro r h1 h5 hr
        exact (rd r h1 (by omega)).trans (hregs r (RelayCall.outside r 11 hr (by decide)) (RelayCall.outside r 12 hr (by decide)) (RelayCall.outside r 13 hr (by decide)))
    ·
      by_cases htmp : path = WireSpec.ascii "/temp"
      · have apc : a.pc = 0x800020f2#32 := by simpa only [ite_eq_right hs,ite_eq_right hpnt,ite_eq_left htmp] using hpc
        obtain ⟨d,k,hk,td,pcd,vd,rd,cd⟩ := NumericDecode.contract B a ram bodyPtr body true hbody apc a8 a9
        refine ⟨d,n+k,by omega,ht.trans td,pcd,?_,?_,cd.trans hcsr⟩
        · simpa only [CommandSpec.value,ite_eq_right hs,ite_eq_right hpnt,ite_eq_left htmp,Bool.false_eq_true,ite_false,ite_true] using vd
        · intro r h1 h5 hr
          exact (rd r h1 (by omega)).trans (hregs r (RelayCall.outside r 11 hr (by decide)) (RelayCall.outside r 12 hr (by decide)) (RelayCall.outside r 13 hr (by decide)))
      ·
        by_cases hmod : path = WireSpec.ascii "/mode"
        · have apc : a.pc = 0x8000215a#32 := by simpa only [ite_eq_right hs,ite_eq_right hpnt,ite_eq_right htmp,ite_eq_left hmod] using hpc
          obtain ⟨d,k,hk,td,pcd,vd,rd,cd⟩ := ModeDecode.contract B a ram bodyPtr body hbody apc a8 a9
          refine ⟨d,n+k,by omega,ht.trans td,pcd,?_,?_,cd.trans hcsr⟩
          · simpa only [CommandSpec.value,ite_eq_right hs,ite_eq_right hpnt,ite_eq_right htmp,ite_eq_left hmod] using vd
          · intro r h1 h5 hr
            exact (rd r (RelayCall.outside r 10 hr (by decide)) (RelayCall.outside r 11 hr (by decide)) (RelayCall.outside r 12 hr (by decide)) (RelayCall.outside r 13 hr (by decide))).trans (hregs r (RelayCall.outside r 11 hr (by decide)) (RelayCall.outside r 12 hr (by decide)) (RelayCall.outside r 13 hr (by decide)))
        ·
          have apc : a.pc = 0x80002194#32 := by simpa only [ite_eq_right hs,ite_eq_right hpnt,ite_eq_right htmp,ite_eq_right hmod] using hpc
          obtain ⟨d,k,hk,td,pcd,vd,rd,cd⟩ := RelayDecode.contract B a ram req bodyPtr first body hparam hbody apc a10 a8 a9
          refine ⟨d,n+k,by omega,ht.trans td,pcd,?_,?_,cd.trans hcsr⟩
          · simpa only [CommandSpec.value,ite_eq_right hs,ite_eq_right hpnt,ite_eq_right htmp,ite_eq_right hmod] using vd
          · intro r h1 h5 hr
            exact (rd r h1 h5 hr).trans (hregs r (RelayCall.outside r 11 hr (by decide)) (RelayCall.outside r 12 hr (by decide)) (RelayCall.outside r 13 hr (by decide)))
end E5R.Thermostat.CommandBody
