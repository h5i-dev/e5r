import Projects.thermostat.HeadMethodClass
import Projects.thermostat.HeadMethodLoad
import Projects.thermostat.HeadMethodMath
namespace E5R.Thermostat.HeadMethodStep
open E5R E5R.Thermostat HttpRequestSpec

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (buf : Word) (i length : Nat)
    (hp : c.pc=0x80002cfa#32) (h12 : c.get 12=BitVec.ofNat 32 length) (h17 : c.get 17=BitVec.ofNat 32 i)
    (h11 : c.get 11=buf) (hc : HeadMethodClass.Constants c) (hi : i<length) (hlen : length≤2048)
    (hm : Memory.Block B buf length) :
    let b := ram (buf+BitVec.ofNat 32 i)
    ∃ n d, 4≤n ∧ n≤16 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if b.toNat<33 then 0x80002da2#32 else if isTchar b.toNat then 0x80002cf4#32 else 0x80002efc#32) ∧
      (b.toNat<33 → d.get 19=BitVec.ofNat 32 b.toNat ∧ d.get 28=buf+BitVec.ofNat 32 i) ∧ HeadMethodClass.Constants d ∧
      (∀ r : Reg, r≠19 → r≠28 → d.get r=c.get r) ∧ d.sameCsr c := by
  let b := ram (buf+BitVec.ofNat 32 i)
  obtain ⟨a,load,pc,addr,value,frame,csr⟩ := HeadMethodLoad.contract B c ram buf (BitVec.ofNat 32 i) (BitVec.ofNat 32 length) b
    h12 h17 h11 (HeadMethodMath.different i length hi hlen)
    (Memory.block_access hm (off := i) (by decide) (by change i+1≤length;omega)) rfl hp
  have constants : HeadMethodClass.Constants a :=
    HeadMethodClass.preserve_constants hc (fun r h19 h28 => frame r h28 h19)
  obtain ⟨n,d,hlo,hn,body,endPC,small,frame2,csr2⟩ := HeadMethodClass.contract B a ram b pc value constants
  exact ⟨3+n,d,by omega,by omega,load.trans body,endPC,(fun hs => ⟨(small hs).1,((small hs).2).trans addr⟩),
    HeadMethodClass.preserve_constants constants frame2,
    fun r h19 h28 => (frame2 r h19 h28).trans (frame r h28 h19),csr2.trans csr⟩
end E5R.Thermostat.HeadMethodStep
