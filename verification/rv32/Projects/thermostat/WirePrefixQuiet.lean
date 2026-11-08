-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.WirePrefix
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.DecodeInputQuiet
import Projects.thermostat.TrimQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.WirePrefix
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp req p : Word) (body : List (BitVec 8))
    (hp : c.pc = 0x80001f6e#32) (hsp : c.get 2 = sp+16#32) (hreq : c.get 10 = req)
    (hm : Memory.Block B sp 16) (ha : sp.toNat%4 = 0) (h : DecodeInput.BodyAt B ram req p body)
    (hsep : WireInput.Separate req sp)
    (hbsep : ∀ i : Fin body.length, ∀ j : Fin 16, p+BitVec.ofNat 32 i.val ≠ sp+BitVec.ofNat 32 j.val) :
    ∃ d k, k ≤ 18*body.length+31 ∧ Quiet.Steps B img k ⟨c,ram⟩ ⟨d,DecodeSave.memory ram sp c⟩ ∧
      d.pc = 0x80001fb4#32 ∧ d.get 2 = sp ∧ d.get 10 = req ∧
      Bytes.Span B (DecodeSave.memory ram sp c) (d.get 8) (TrimMath.trim body) ∧
      d.get 9 = BitVec.ofNat 32 (TrimMath.trim body).length ∧
      (∀ r : Reg, r ≠ 2 → r.val < 8 ∨ 17 < r.val → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,ht,apc,asp,a11,a12,aregs,acsr⟩ := E5R.Thermostat.DecodeInput.contract_quiet B c ram sp req p body hp hsp hreq hm ha h (WireInput.body_separate hsep) hbsep
  have h' := DecodeInput.body_preserved h sp c (WireInput.body_separate hsep) hbsep
  obtain ⟨d,k,hk,htrim,dpc,d8,d9,dspan,dregs,dcsr⟩ := E5R.Thermostat.Trim.contract_quiet B a (DecodeSave.memory ram sp c) p body h'.bytes apc a11 a12
  refine ⟨d,6+k,by omega,ht.trans htrim,dpc,(dregs 2 (by decide)).trans asp,
    (dregs 10 (by decide)).trans ((aregs 10 (by decide) (by decide) (by decide)).trans hreq),dspan,d9,?_,dcsr.trans acsr⟩
  intro r h2 hr
  have hr' : r.val < 8 ∨ r.val = 10 ∨ 16 < r.val := by omega
  have h11 : r ≠ 11 := by intro he;have hv := congrArg Fin.val he;change r.val = 11 at hv;omega
  have h12 : r ≠ 12 := by intro he;have hv := congrArg Fin.val he;change r.val = 12 at hv;omega
  exact (dregs r hr').trans (aregs r h2 h11 h12)

end E5R.Thermostat.WirePrefix
