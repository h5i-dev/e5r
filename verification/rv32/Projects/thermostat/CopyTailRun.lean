import Projects.thermostat.CopyTailSetup
import Projects.thermostat.CopyRegs
import Projects.thermostat.SmallCopyLoop
import Projects.thermostat.SmallCopyReturn
import Projects.thermostat.OutsideRam
namespace E5R.Thermostat.CopyTailRun
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src finish : Word) (n bulk : Nat) (tail : List (BitVec 8))
    (hp : c.pc=0x80005222#32) (h11 : c.get 11=src) (h12 : c.get 12=BitVec.ofNat 32 n)
    (h13 : c.get 13=finish) (h15 : c.get 15=BitVec.ofNat 32 bulk)
    (hm : BitVec.ofNat 32 n &&& 3#32=BitVec.ofNat 32 tail.length) (hw : finish.toNat+tail.length<2^32)
    (hs : ReadBytes.Span B img ram (src+BitVec.ofNat 32 bulk) tail)
    (hro : ∀ i : Fin tail.length, B.inRam ((src+BitVec.ofNat 32 bulk)+BitVec.ofNat 32 i.val) 1=false)
    (hd : Memory.Block B finish tail.length) :
    ∃ d, DetSteps B img (5+6*tail.length+2) ⟨c,ram⟩ ⟨d,ByteWrite.write ram finish tail⟩ ∧
      d.pc=c.get 1 &&& ~~~1 ∧ d.get 2=c.get 2+16#32 ∧ d.get 10=c.get 10 ∧
      (∀ r : Reg, CopyRegs.Preserved r → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,ta,apc,a11,a12,ar,ac⟩ := CopyTailSetup.contract B c ram src finish n bulk tail.length hp h11 h12 h13 h15 hm hw
  have asp : a.get 2=c.get 2 := ar 2 (by decide) (by decide) (by decide)
  have a10 : a.get 10=c.get 10 := ar 10 (by decide) (by decide) (by decide)
  have a13 : a.get 13=finish := (ar 13 (by decide) (by decide) (by decide)).trans h13
  have keep (r : Reg) (hr : CopyRegs.Preserved r) : a.get r=c.get r := by
    exact ar r (CopyRegs.ne_low r 11 hr (by decide) (by decide) (by decide) (by decide))
      (CopyRegs.ne_low r 12 hr (by decide) (by decide) (by decide) (by decide))
      (CopyRegs.ne_low r 14 hr (by decide) (by decide) (by decide) (by decide))
  cases tail with
  | nil =>
    have apc' : a.pc=0x8000530c#32 := by simpa only [List.length_nil,ite_true] using apc
    obtain ⟨d,td,dpc,dsp,dr,dc⟩ := SmallCopyReturn.contract B a ram apc'
    refine ⟨d,ta.trans td,by rw [dpc,keep 1 (by decide)],by rw [dsp,asp],(dr 10 (by decide)).trans a10,?_,dc.trans ac⟩
    intro r hr
    have h2 : r≠2 := CopyRegs.ne_low r 2 hr (by decide) (by decide) (by decide) (by decide)
    exact (dr r h2).trans (keep r hr)
  | cons b bs =>
    have hne : (b::bs).length≠0 := by simp only [List.length_cons];omega
    have apc' : a.pc=0x800052fc#32 := by simpa only [ite_eq_right hne] using apc
    obtain ⟨u,tu,upc,_,_,_,ur,uc⟩ := SmallCopyLoop.contract B ram (b::bs) _ finish hs hd (by simp)
      (WordRegions.outside_ram hro hd) a apc' a11 a13 a12
    have usp : u.get 2=c.get 2 := (ur 2 (by decide) (by decide) (by decide) (by decide)).trans asp
    have u10 : u.get 10=c.get 10 := (ur 10 (by decide) (by decide) (by decide) (by decide)).trans a10
    have ukeep (r : Reg) (hr : CopyRegs.Preserved r) : u.get r=c.get r := by
      exact (ur r (CopyRegs.ne_low r 11 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 12 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 13 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 14 hr (by decide) (by decide) (by decide) (by decide))).trans (keep r hr)
    obtain ⟨d,td,dpc,dsp,dr,dc⟩ := SmallCopyReturn.contract B u (ByteWrite.write ram finish (b::bs)) upc
    refine ⟨d,(ta.trans tu).trans td,by rw [dpc,ukeep 1 (by decide)],by rw [dsp,usp],(dr 10 (by decide)).trans u10,?_,(dc.trans uc).trans ac⟩
    intro r hr
    exact (dr r (CopyRegs.ne_low r 2 hr (by decide) (by decide) (by decide) (by decide))).trans (ukeep r hr)
end E5R.Thermostat.CopyTailRun
