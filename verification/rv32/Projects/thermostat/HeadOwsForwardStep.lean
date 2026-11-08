import Projects.thermostat.HeadOwsForwardLoad
import Projects.thermostat.HeadOwsForwardClass
import Projects.thermostat.HeadTargetMath
namespace E5R.Thermostat.HeadOwsForwardStep
open E5R E5R.Thermostat HttpRequestSpec

/-- Actual OWS load and SP/TAB check; the slice guard is derived from bounds. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (pos length : Nat)
    (hp : c.pc=0x800030a4#32) (h2 : c.get 2=sp) (h15 : c.get 15=BitVec.ofNat 32 pos)
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length) (hbuf : ramRead ram (sp+44#32) .w=buf)
    (hi : pos<length) (hlen : length≤2048) (mem : Memory.Block B buf length) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0) :
    let b := ram (buf+BitVec.ofNat 32 pos)
    ∃ n d, 7≤n ∧ n≤9 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if isOws b.toNat then 0x8000309c#32 else 0x800030c0#32) ∧
      (∀ r : Reg, r≠10 → r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let b := ram (buf+BitVec.ofNat 32 pos)
  have test : taken .geu (BitVec.ofNat 32 pos) (BitVec.ofNat 32 length)=false := by
    simpa only [show ¬length≤pos by omega,decide_false] using HeadTargetMath.geu pos length (by omega) hlen
  obtain ⟨a,load,pc,value,tab,frame,csr⟩ := HeadOwsForwardLoad.contract B c ram sp buf (BitVec.ofNat 32 pos) (BitVec.ofNat 32 length) b h2 h15 hraw hbuf test
    (Memory.block_access mem (off := pos) (by decide) (by change pos+1≤length;omega)) rfl stack ha hp
  obtain ⟨n,d,nlo,nhi,classify,pc2,frame2,csr2⟩ := HeadOwsForwardClass.contract B a ram b pc value tab
  exact ⟨6+n,d,by omega,by omega,load.trans classify,pc2,fun r h10 h12 => (frame2 r h12).trans (frame r h10 h12),csr2.trans csr⟩
end E5R.Thermostat.HeadOwsForwardStep
