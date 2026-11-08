-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ErrorPrepare
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.ErrorCallQuiet
import Projects.thermostat.ErrorLoadQuiet
import Projects.thermostat.ErrorSaveQuiet
import Projects.thermostat.ErrorSelectQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.ErrorPrepare
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp ptr dst : Word) (cap : Nat) (e : Spec.Error)
    (hp : c.pc=0x80001e4a#32) (hsp : c.get 2=sp+16#32) (h10 : c.get 10=ptr) (h11 : c.get 11=dst)
    (h12 : c.get 12=BitVec.ofNat 32 cap) (hc : 33≤cap) (hb : cap<2^32)
    (hm : Memory.Block B sp 16) (ha : sp.toNat%4=0)
    (hx : ReadBytes.Byte B img ram ptr (Errors.code e)) (hsep : WordRegions.Disjoint ptr 1 sp 16) :
    ∃ d n, n≤19 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ErrorSave.memory ram sp c⟩ ∧ Ready c d sp dst e := by
  obtain ⟨a,ta,apc,asp,ar,ac⟩ := E5R.Thermostat.ErrorSave.contract_quiet B c ram sp hp hsp hm ha
  let r := ErrorSave.memory ram sp c
  have hx' : ReadBytes.Byte B img r ptr (Errors.code e) := hx.frame (ErrorSave.frame ram sp c ptr (by
    intro i
    have hh := hsep ⟨0,by decide⟩ i
    simpa only [BitVec.add_zero] using hh))
  obtain ⟨b,tb,bpc,b8,b12,b10,br,bc⟩ := E5R.Thermostat.ErrorLoad.contract_quiet B a r ptr dst (BitVec.ofNat 32 cap) e apc
    ((ar 10 (by decide)).trans h10) ((ar 11 (by decide)).trans h11) ((ar 12 (by decide)).trans h12) hx'
  obtain ⟨u,k,hk,tu,upc,u11,u12,u9,u8,ur,uc⟩ := E5R.Thermostat.ErrorSelect.contract_quiet B b r cap e bpc b8 b12 hc hb
  obtain ⟨d,td,dpc,d12,d1,dr,dc⟩ := E5R.Thermostat.ErrorCall.contract_quiet B u r (BitVec.ofNat 32 (ReplyJson.errorBody e).length) u8 upc
  have bsp : b.get 2=sp := (br 2 (by decide) (by decide) (by decide)).trans asp
  have usp : u.get 2=sp := (ur 2 (by decide) (by decide) (by decide) (by decide)).trans bsp
  have u10 : u.get 10=dst := (ur 10 (by decide) (by decide) (by decide) (by decide)).trans b10
  refine ⟨d,4+3+k+3,by omega,((ta.trans tb).trans tu).trans td,?_,?_,d1,?_,?_,d12,?_,?_,?_,((dc.trans uc).trans bc).trans ac⟩
  · exact dpc
  · exact (dr 2 (by decide) (by decide)).trans usp
  · exact (dr 10 (by decide) (by decide)).trans u10
  · exact (dr 11 (by decide) (by decide)).trans u11
  · exact (dr 8 (by decide) (by decide)).trans u8
  · exact (dr 9 (by decide) (by decide)).trans u9
  · intro reg hreg
    have ne (q : Reg) (hq : q.val<18) : reg≠q := by intro he;subst reg;omega
    exact (dr reg (ne 12 (by decide)) (ne 1 (by decide))).trans
      ((ur reg (ne 11 (by decide)) (ne 12 (by decide)) (ne 9 (by decide)) (ne 8 (by decide))).trans
        ((br reg (ne 8 (by decide)) (ne 12 (by decide)) (ne 10 (by decide))).trans (ar reg (ne 2 (by decide)))))

end E5R.Thermostat.ErrorPrepare
