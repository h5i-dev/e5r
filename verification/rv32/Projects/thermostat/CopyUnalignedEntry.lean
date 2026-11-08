import Projects.thermostat.CopyLongStart
import Projects.thermostat.CopyAlignedDestination
import Projects.thermostat.CopyUnalignedHeader
import Projects.thermostat.CopyUnalignedScratch
import Projects.thermostat.CopyRegs
set_option maxHeartbeats 1000000
namespace E5R.Thermostat.CopyUnalignedEntry
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp src dst : Word) (n bulk offset : Nat)
    (hp : c.pc=0x80005182#32) (hsp : c.get 2=sp+16#32) (h10 : c.get 10=dst) (h11 : c.get 11=src)
    (h12 : c.get 12=BitVec.ofNat 32 n) (hn : 16≤n) (hnb : n<2^32)
    (had : dst.toNat%4=0) (hm : Memory.Block B sp 16) (ha : sp.toNat%4=0)
    (hmask : BitVec.ofNat 32 n &&& 0xfffffffc#32=BitVec.ofNat 32 bulk)
    (ho : src &&& 3#32=BitVec.ofNat 32 offset) (hoz : BitVec.ofNat 32 offset≠0#32) (hob : offset<4) :
    ∃ d, DetSteps B img 22 ⟨c,ram⟩ ⟨d,CopyUnalignedScratch.memory ram sp⟩ ∧ d.pc=0x800051e0#32 ∧
      d.get 2=sp ∧ d.get 10=dst ∧ d.get 11=src ∧ d.get 12=BitVec.ofNat 32 n ∧
      d.get 13=dst+BitVec.ofNat 32 bulk ∧ d.get 14=dst ∧ d.get 15=BitVec.ofNat 32 bulk ∧
      d.get 5=BitVec.ofNat 32 offset ∧ d.get 16=0#32 ∧ d.get 17=4#32-BitVec.ofNat 32 offset ∧
      d.get 6=sp+BitVec.ofNat 32 (12+offset) ∧ d.get 7=(4#32-BitVec.ofNat 32 offset) &&& 1#32 ∧
      (∀ r : Reg, CopyRegs.Preserved r → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,ta,pa,_,a2,_,ar,ac⟩ := CopyLongStart.contract B c ram sp n hsp h12 hn hnb hp
  have a10 := (ar 10 (by decide) (by decide) (by decide)).trans h10
  have a11 := (ar 11 (by decide) (by decide) (by decide)).trans h11
  have a12 := (ar 12 (by decide) (by decide) (by decide)).trans h12
  obtain ⟨b,tb,pb,b13,b14,br,bc⟩ := CopyAlignedDestination.contract B a ram dst a10 had pa
  obtain ⟨z,tz,pz,z11,z12,z15,z5,z13,zr,zc⟩ := CopyUnalignedHeader.contract B b ram src dst (BitVec.ofNat 32 offset) n bulk
    ((br 11 (by decide) (by decide)).trans a11) ((br 12 (by decide) (by decide)).trans a12) b13 b14 hmask ho hoz pb
  have z2 := (zr 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((br 2 (by decide) (by decide)).trans a2)
  obtain ⟨d,td,pd,d16,d17,d6,d7,dr,dc⟩ := CopyUnalignedScratch.contract B z ram sp offset pz z2 z5 hm ha hob
  refine ⟨d,by simpa using ((ta.trans tb).trans tz).trans td,pd,?_,?_,?_,?_,?_,?_,?_,?_,d16,d17,d6,d7,?_,dc.trans (zc.trans (bc.trans ac))⟩
  · exact (dr 2 (by decide) (by decide) (by decide) (by decide)).trans (z2)
  · exact (dr 10 (by decide) (by decide) (by decide) (by decide)).trans ((zr 10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((br 10 (by decide) (by decide)).trans a10))
  · exact (dr 11 (by decide) (by decide) (by decide) (by decide)).trans (z11)
  · exact (dr 12 (by decide) (by decide) (by decide) (by decide)).trans (z12)
  · exact (dr 13 (by decide) (by decide) (by decide) (by decide)).trans (z13)
  · exact (dr 14 (by decide) (by decide) (by decide) (by decide)).trans ((zr 14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans b14)
  · exact (dr 15 (by decide) (by decide) (by decide) (by decide)).trans (z15)
  · exact (dr 5 (by decide) (by decide) (by decide) (by decide)).trans (z5)
  · intro reg hr
    have ne (q : Reg) (hq : q.val<18) (h1 : q≠1) (h8 : q≠8) (h9 : q≠9) := CopyRegs.ne_low reg q hr hq h1 h8 h9
    apply Eq.trans (dr reg (ne 16 (by decide) (by decide) (by decide) (by decide)) (ne 17 (by decide) (by decide) (by decide) (by decide)) (ne 6 (by decide) (by decide) (by decide) (by decide)) (ne 7 (by decide) (by decide) (by decide) (by decide)))
    apply Eq.trans (zr reg (ne 11 (by decide) (by decide) (by decide) (by decide)) (ne 12 (by decide) (by decide) (by decide) (by decide)) (ne 15 (by decide) (by decide) (by decide) (by decide)) (ne 5 (by decide) (by decide) (by decide) (by decide)) (ne 13 (by decide) (by decide) (by decide) (by decide)))
    apply Eq.trans (br reg (ne 13 (by decide) (by decide) (by decide) (by decide)) (ne 14 (by decide) (by decide) (by decide) (by decide)))
    exact ar reg (ne 6 (by decide) (by decide) (by decide) (by decide)) (ne 2 (by decide) (by decide) (by decide) (by decide)) (ne 13 (by decide) (by decide) (by decide) (by decide))
end E5R.Thermostat.CopyUnalignedEntry
