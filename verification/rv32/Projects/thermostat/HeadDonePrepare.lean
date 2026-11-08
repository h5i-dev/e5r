import Projects.thermostat.HeadDoneHostRead
import Projects.thermostat.HeadDoneHostBranch
import Projects.thermostat.HeadDoneMissingHost
import Projects.thermostat.HeadDoneLengthRead
import Projects.thermostat.HeadDoneTag
import Projects.thermostat.HeadFieldsConstants
namespace E5R.Thermostat.HeadDonePrepare
open E5R E5R.Thermostat HttpRequestSpec

structure Ready (c : Core) (sp : Word) (f : Fields) (len minor : Nat) : Prop where
  pc : c.pc=0x80003486#32
  stack : c.get 2=sp
  tag : c.get 20=HeadDoneTag.tag f.te f.hasCl
  low : c.get 18=BitVec.ofNat 32 f.cl
  high : c.get 19=BitVec.ofNat 32 (f.cl/4294967296)
  count : c.get 9=BitVec.ofNat 32 f.headers.length
  length : c.get 24=BitVec.ofNat 32 len
  version : c.get 8=BitVec.ofNat 32 minor

def Missing (c : Core) (sp : Word) : Prop :=
  c.pc=0x8000341a#32 ∧ c.get 10=4#32 ∧ c.get 11=400#32 ∧ c.get 2=sp

/-- Actual final Host check and framing selection, with no assumed branch
    decisions or preloaded content-length words. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (f : Fields) (len minor length : Nat)
    (hp : c.pc=0x80003456#32) (constants : HeadFieldsConstants.At c sp length minor)
    (fieldsView : HeadFieldsView.At ram sp f) (count : c.get 9=BitVec.ofNat 32 f.headers.length)
    (position : c.get 24=BitVec.ofNat 32 (len-2)) (transfer : c.get 23=(if f.te then 1#32 else 0#32))
    (positive : 2≤len) (version : minor≤1) (stack : Memory.Block B sp 327) (aligned : sp.toNat%4=0) :
    ∃ n d, 7≤n ∧ n≤12 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      (if minor=1 ∧ f.host=false then Missing d sp else Ready d sp f len minor) ∧ d.sameCsr c := by
  have input : ramRead ram (sp+324#32) .b=BitVec.ofNat 32 (HeadFieldsView.flag f.host).toNat := by
    change BitVec.ofNat 32 (ram (sp+324#32)).toNat=_;rw [fieldsView.host]
  obtain ⟨a,ta,apc,a10,ar,ac⟩ := HeadDoneHostRead.contract B c ram sp _ _ constants.stack constants.inverse input stack hp
  obtain ⟨b,tb,bpc,br,bc⟩ := HeadDoneHostBranch.contract B a ram _ 0#32 (decide (minor=1 ∧ f.host=false)) apc a10 (Core.get_zero _) (HeadDoneMath.host minor f.host version)
  have hostKeep (r : Reg) (ne : r≠10) : b.get r=c.get r := (br r).trans (ar r ne)
  by_cases missing : minor=1 ∧ f.host=false
  · have pc : b.pc=0x8000347c#32 := by simpa only [decide_eq_true missing,ite_true] using bpc
    obtain ⟨d,td,dpc,d10,d11,dr,dc⟩ := HeadDoneMissingHost.contract B b ram pc
    exact ⟨7,d,by decide,by decide,(ta.trans tb).trans td,by rw [ite_eq_left missing];exact ⟨dpc,d10,d11,(dr 2 (by decide) (by decide)).trans ((hostKeep 2 (by decide)).trans constants.stack)⟩,(dc.trans bc).trans ac⟩
  · have pc : b.pc=0x80003462#32 := by simpa only [decide_eq_false missing,Bool.false_eq_true,ite_false] using bpc
    obtain ⟨z,tz,zpc,z18,z19,z10,z24,zr,zc⟩ := HeadDoneLengthRead.contract B b ram sp _ _ _ _
      ((hostKeep 2 (by decide)).trans constants.stack) ((hostKeep 23 (by decide)).trans transfer)
      ((hostKeep 24 (by decide)).trans position) fieldsView.clLow fieldsView.clHigh stack aligned pc
    have zsp : z.get 2=sp := (zr 2 (by decide) (by decide) (by decide) (by decide)).trans ((hostKeep 2 (by decide)).trans constants.stack)
    obtain ⟨n,d,lo,hi,td,dpc,d20,dr,dc⟩ := HeadDoneTag.contract B z ram sp f.te f.hasCl zpc zsp z10 fieldsView.hasCl stack
    have ready : Ready d sp f len minor := by
      refine ⟨dpc,(dr 2 (by decide) (by decide)).trans zsp,d20,(dr 18 (by decide) (by decide)).trans z18,
        (dr 19 (by decide) (by decide)).trans z19,?_,?_,?_⟩
      · exact (dr 9 (by decide) (by decide)).trans ((zr 9 (by decide) (by decide) (by decide) (by decide)).trans ((hostKeep 9 (by decide)).trans count))
      · exact (dr 24 (by decide) (by decide)).trans (z24.trans (HeadDoneMath.length len positive))
      · exact (dr 8 (by decide) (by decide)).trans ((zr 8 (by decide) (by decide) (by decide) (by decide)).trans ((hostKeep 8 (by decide)).trans constants.version))
    exact ⟨3+1+4+n,d,by omega,by omega,((ta.trans tb).trans tz).trans td,by rw [ite_eq_right missing];exact ready,((dc.trans zc).trans bc).trans ac⟩
end E5R.Thermostat.HeadDonePrepare
