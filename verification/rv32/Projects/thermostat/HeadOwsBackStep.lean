import Projects.thermostat.HeadOwsBackLoad
import Projects.thermostat.HeadOwsBackClass
import Projects.thermostat.HeadTargetMath
namespace E5R.Thermostat.HeadOwsBackStep
open E5R E5R.Thermostat HttpRequestSpec

/-- Actual backward OWS access uses p-1; its nonwrapping slice bound is derived. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (pos length : Nat)
    (hp : c.pc=0x800030d0#32) (h2 : c.get 2=sp) (h25 : c.get 25=BitVec.ofNat 32 pos)
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length) (hbuf : ramRead ram (sp+44#32) .w=buf)
    (hi : 0<pos) (hn : pos≤length) (hlen : length≤2048) (mem : Memory.Block B buf length) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0) :
    let b := ram (buf+BitVec.ofNat 32 (pos-1))
    ∃ n d, 7≤n ∧ n≤11 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if isOws b.toNat then 0x800030ca#32 else 0x800030fa#32) ∧ d.get 10=BitVec.ofNat 32 (pos-1) ∧
      (∀ r : Reg, r≠10 → r≠13 → r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let b := ram (buf+BitVec.ofNat 32 (pos-1))
  have previous : BitVec.ofNat 32 pos+0xffffffff#32=BitVec.ofNat 32 (pos-1) := by
    simpa only [Nat.sub_zero,Nat.zero_add] using HeadTargetMath.remaining_next 0 pos hi
  have test : taken .geu (BitVec.ofNat 32 pos+0xffffffff#32) (BitVec.ofNat 32 length)=false := by
    rw [previous]
    simpa only [show ¬length≤pos-1 by omega,decide_false] using HeadTargetMath.geu (pos-1) length (by omega) hlen
  have addr : (buf+BitVec.ofNat 32 pos)+0xffffffff#32=buf+BitVec.ofNat 32 (pos-1) := by rw [BitVec.add_assoc,previous]
  obtain ⟨a,load,pc,index,value,frame,csr⟩ := HeadOwsBackLoad.contract B c ram sp buf (BitVec.ofNat 32 pos) (BitVec.ofNat 32 length) b h2 h25 hraw hbuf test
    (by rw [addr];exact Memory.block_access mem (off := pos-1) (by decide) (by change pos-1+1≤length;omega)) (by rw [addr]) stack ha hp
  obtain ⟨n,d,nlo,nhi,classify,pc2,frame2,csr2⟩ := HeadOwsBackClass.contract B a ram b pc value
  exact ⟨6+n,d,by omega,by omega,load.trans classify,pc2,(frame2 10 (by decide)).trans (index.trans previous),
    fun r h10 h13 h12 => (frame2 r h12).trans (frame r h10 h13),csr2.trans csr⟩
end E5R.Thermostat.HeadOwsBackStep
