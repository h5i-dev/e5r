import Projects.thermostat.ErrorSave
import Projects.thermostat.ErrorLoad
import Projects.thermostat.ErrorSelect
import Projects.thermostat.ErrorCall
import Projects.thermostat.WordRegions
namespace E5R.Thermostat.ErrorPrepare
open E5R E5R.Thermostat

structure Ready (before after : Core) (sp dst : Word) (e : Spec.Error) : Prop where
  pc : after.pc=0x80005182#32
  stack : after.get 2=sp
  ra : after.get 1=0x80001e96#32
  output : after.get 10=dst
  source : after.get 11=ErrorLiterals.pointer e
  length : after.get 12=BitVec.ofNat 32 (ReplyJson.errorBody e).length
  savedLength : after.get 8=BitVec.ofNat 32 (ReplyJson.errorBody e).length
  savedStatus : after.get 9=ErrorLiterals.status e
  saved : ∀ r : Reg, 18≤r.val ∧ r.val≤27 → after.get r=before.get r
  csr : after.sameCsr before

/-- Real encode_error saves, error-byte load, all three case/capacity branches
    and actual memcpy call. No output-copy behavior is assumed here. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp ptr dst : Word) (cap : Nat) (e : Spec.Error)
    (hp : c.pc=0x80001e4a#32) (hsp : c.get 2=sp+16#32) (h10 : c.get 10=ptr) (h11 : c.get 11=dst)
    (h12 : c.get 12=BitVec.ofNat 32 cap) (hc : 33≤cap) (hb : cap<2^32)
    (hm : Memory.Block B sp 16) (ha : sp.toNat%4=0)
    (hx : ReadBytes.Byte B img ram ptr (Errors.code e)) (hsep : WordRegions.Disjoint ptr 1 sp 16) :
    ∃ d n, n≤19 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ErrorSave.memory ram sp c⟩ ∧ Ready c d sp dst e := by
  obtain ⟨a,ta,apc,asp,ar,ac⟩ := ErrorSave.contract B c ram sp hp hsp hm ha
  let r := ErrorSave.memory ram sp c
  have hx' : ReadBytes.Byte B img r ptr (Errors.code e) := hx.frame (ErrorSave.frame ram sp c ptr (by
    intro i
    have hh := hsep ⟨0,by decide⟩ i
    simpa only [BitVec.add_zero] using hh))
  obtain ⟨b,tb,bpc,b8,b12,b10,br,bc⟩ := ErrorLoad.contract B a r ptr dst (BitVec.ofNat 32 cap) e apc
    ((ar 10 (by decide)).trans h10) ((ar 11 (by decide)).trans h11) ((ar 12 (by decide)).trans h12) hx'
  obtain ⟨u,k,hk,tu,upc,u11,u12,u9,u8,ur,uc⟩ := ErrorSelect.contract B b r cap e bpc b8 b12 hc hb
  obtain ⟨d,td,dpc,d12,d1,dr,dc⟩ := ErrorCall.contract B u r (BitVec.ofNat 32 (ReplyJson.errorBody e).length) u8 upc
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
