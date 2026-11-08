import Projects.thermostat.MainHeaderResultKind
import Projects.thermostat.MainHeaderResultLoad
import Projects.thermostat.MainHeaderResultBranch
import Projects.thermostat.MainHeaderResultSubtract
import Projects.thermostat.MainHeaderSubtractBranch
import Projects.thermostat.MainHeaderResultAccepted
import Projects.thermostat.MainHeaderAcceptedBranch
import Projects.thermostat.MainHeaderVariantBranch
import Projects.thermostat.MainHeaderResultReject
import Projects.thermostat.HeadRegisterFrame
namespace E5R.Thermostat.MainHeaderDispatchTwo
open E5R E5R.Thermostat HttpRequestSpec

def writes : List Reg := [10,11,12,18,27,9]

def At (c : Core) : HeadR → Prop
  | .incomplete => c.pc=0x80000a50#32
  | .reject status => c.pc=0x80000a9a#32 ∧ c.get 18=0#32 ∧ c.get 27=BitVec.ofNat 32 status ∧ c.get 9=3#32
  | .done _ => c.pc=0x80000bf6#32

def Keeps18 (c d : Core) : HeadR → Prop
  | .reject _ => True
  | _ => d.get 18=c.get 18

theorem ne : ∀ r : Reg, r∉writes → r≠10 ∧ r≠11 ∧ r≠12 ∧ r≠18 ∧ r≠27 ∧ r≠9 := by decide +kernel

/-- All three actual main result-dispatch paths derive from the complete RAM
    representation established by the parser, including the u16 error payload. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (fp : Word) (result : HeadR)
    (hp : c.pc=0x80000a26#32) (h8 : c.get 8=fp) (h22 : c.get 22=1#32)
    (view : HeadFinalResult.At ram (fp+1316#32) result) (object : Memory.Block B fp 1326) (aligned : fp.toNat%4=0) :
    ∃ n d, 8≤n ∧ n≤13 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ At d result ∧ HeadRegisterFrame.At c d writes ∧ d.sameCsr c ∧ Keeps18 c d result := by
  have words := MainHeaderResultKind.words view
  have small : Memory.Block B fp 1324 := by simpa only [BitVec.add_zero] using Memory.sub_block object (off := 0) (m := 1324) (by decide) (by decide)
  have pad : ramRead ram (fp+1320#32) .w=0#32 := by simpa only [show (fp+1316#32)+4#32=fp+1320#32 by rw [BitVec.add_assoc];rfl] using words.2
  obtain ⟨a,ta,apc,a10,a11,a12,ar,ac⟩ := MainHeaderResultLoad.contract B c ram fp (MainHeaderResultKind.tag result) h8 words.1 pad small aligned hp
  obtain ⟨b,tb,bpc,br,bc⟩ := MainHeaderResultBranch.contract B a ram _ 0#32 (MainHeaderResultKind.early result) apc a11 (Core.get_zero _) (MainHeaderResultKind.test result)
  have source (r : Reg) (h10 : r≠10) (h11 : r≠11) (h12 : r≠12) : b.get r=c.get r := (br r).trans (ar r h10 h11 h12)
  have b10 : b.get 10=MainHeaderResultKind.tag result := (br 10).trans a10
  have b22 : b.get 22=1#32 := (source 22 (by decide) (by decide) (by decide)).trans h22
  cases result with
  | incomplete =>
    have pc : b.pc=0x80000a4c#32 := by simpa only [MainHeaderResultKind.early,ite_true] using bpc
    obtain ⟨z,tz,zpc,z10,zr,zc⟩ := MainHeaderResultSubtract.contract B b ram 3#32 b10 pc
    have zero : z.get 10=0#32 := by simpa only [show 3#32+0xfffffffd#32=0#32 by decide +kernel] using z10
    obtain ⟨d,td,dpc,dr,dc⟩ := MainHeaderSubtractBranch.contract B z ram 0#32 0#32 false zpc zero (Core.get_zero _) (by decide +kernel)
    refine ⟨8,d,by decide,by decide,((ta.trans tb).trans tz).trans td,?_,?_,((dc.trans zc).trans bc).trans ac,?_⟩
    · simpa only [Bool.false_eq_true,ite_false,At] using dpc
    · intro r safe
      obtain ⟨h10,h11,h12,_,_,_⟩ := ne r safe
      exact (dr r).trans ((zr r h10).trans (source r h10 h11 h12))
    · exact (dr 18).trans ((zr 18 (by decide)).trans (source 18 (by decide) (by decide) (by decide)))
  | reject status =>
    have pc : b.pc=0x80000a4c#32 := by simpa only [MainHeaderResultKind.early,ite_true] using bpc
    obtain ⟨z,tz,zpc,z10,zr,zc⟩ := MainHeaderResultSubtract.contract B b ram 4#32 b10 pc
    have one : z.get 10=1#32 := by simpa only [show 4#32+0xfffffffd#32=1#32 by decide +kernel] using z10
    obtain ⟨u,tu,upc,ur,uc⟩ := MainHeaderSubtractBranch.contract B z ram 1#32 0#32 true zpc one (Core.get_zero _) (by decide +kernel)
    have upc' : u.pc=0x80000a3e#32 := by simpa only [ite_true] using upc
    obtain ⟨v,tv,vpc,vr,vc⟩ := MainHeaderVariantBranch.contract B u ram 1#32 1#32 false upc' ((ur 10).trans one)
      ((ur 22).trans ((zr 22 (by decide)).trans b22)) (by decide +kernel)
    have vpc' : v.pc=0x80000a42#32 := by simpa only [Bool.false_eq_true,ite_false] using vpc
    have v8 : v.get 8=fp := (vr 8).trans ((ur 8).trans ((zr 8 (by decide)).trans ((source 8 (by decide) (by decide) (by decide)).trans h8)))
    have payload : extend .h false (ramRead ram (fp+1324#32) .h)=BitVec.ofNat 32 status := by
      simpa only [show (fp+1316#32)+8#32=fp+1324#32 by rw [BitVec.add_assoc];rfl] using view.2.2.2
    obtain ⟨d,td,dpc,d18,d27,d9,dr,dc⟩ := MainHeaderResultReject.contract B v ram fp _ v8 payload object aligned vpc'
    refine ⟨13,d,by decide,by decide,((((ta.trans tb).trans tz).trans tu).trans tv).trans td,⟨dpc,d18,d27,d9⟩,?_,((((dc.trans vc).trans uc).trans zc).trans bc).trans ac,True.intro⟩
    intro r safe
    obtain ⟨h10,h11,h12,h18,h27,h9⟩ := ne r safe
    exact (dr r h18 h27 h9).trans ((vr r).trans ((ur r).trans ((zr r h10).trans (source r h10 h11 h12))))
  | done h =>
    have pc : b.pc=0x80000a3a#32 := by simpa only [MainHeaderResultKind.early,Bool.false_eq_true,ite_false] using bpc
    obtain ⟨z,tz,zpc,z10,zr,zc⟩ := MainHeaderResultAccepted.contract B b ram pc
    obtain ⟨u,tu,upc,ur,uc⟩ := MainHeaderAcceptedBranch.contract B z ram 2#32 0#32 false zpc z10 (Core.get_zero _) (by decide +kernel)
    have upc' : u.pc=0x80000a3e#32 := by simpa only [Bool.false_eq_true,ite_false] using upc
    obtain ⟨d,td,dpc,dr,dc⟩ := MainHeaderVariantBranch.contract B u ram 2#32 1#32 true upc' ((ur 10).trans z10)
      ((ur 22).trans ((zr 22 (by decide)).trans b22)) (by decide +kernel)
    refine ⟨9,d,by decide,by decide,(((ta.trans tb).trans tz).trans tu).trans td,?_,?_,(((dc.trans uc).trans zc).trans bc).trans ac,?_⟩
    · simpa only [ite_true,At] using dpc
    · intro r safe
      obtain ⟨h10,h11,h12,_,_,_⟩ := ne r safe
      exact (dr r).trans ((ur r).trans ((zr r h10).trans (source r h10 h11 h12)))
    · exact (dr 18).trans ((ur 18).trans ((zr 18 (by decide)).trans (source 18 (by decide) (by decide) (by decide))))
end E5R.Thermostat.MainHeaderDispatchTwo
