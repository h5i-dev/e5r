import Projects.thermostat.HeadFieldsScanLoad
import Projects.thermostat.HeadFieldsScanClass
import Projects.thermostat.HeadFieldsMath
namespace E5R.Thermostat.HeadFieldsScanStep
open E5R E5R.Thermostat

/-- Real current-byte bounds guard, load and LF/CR classification. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (buf : Word) (i t length : Nat)
    (hp : c.pc=0x80002f6e#32) (h13 : c.get 13=BitVec.ofNat 32 i-BitVec.ofNat 32 length)
    (h21 : c.get 21=BitVec.ofNat 32 t) (h14 : c.get 14=buf+BitVec.ofNat 32 t) (h24 : c.get 24=BitVec.ofNat 32 i)
    (h16 : c.get 16=10#32) (h17 : c.get 17=13#32)
    (hi : i+t<length) (hlen : length≤2048) (hm : Memory.Block B buf length) :
    let byte := ram (buf+BitVec.ofNat 32 (i+t))
    ∃ n d, 5≤n ∧ n≤6 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if byte.toNat=10 then 0x80003428#32 else if byte.toNat=13 then 0x80002f9a#32 else 0x80002f86#32) ∧
      d.get 15=buf+BitVec.ofNat 32 (i+t) ∧ d.get 30=BitVec.ofNat 32 byte.toNat ∧
      (∀ r : Reg, r≠15 → r≠30 → d.get r=c.get r) ∧ d.sameCsr c := by
  let byte := ram (buf+BitVec.ofNat 32 (i+t))
  have pointer := HeadFieldsMath.pointer buf i t
  have access : B.inRam ((buf+BitVec.ofNat 32 t)+BitVec.ofNat 32 i) 1=true := by
    rw [pointer]
    exact Memory.block_access hm (off := i+t) (by decide) (by change i+t+1≤length;omega)
  obtain ⟨a,load,pc,addr,value,frame,csr⟩ := HeadFieldsScanLoad.contract B c ram
    (BitVec.ofNat 32 i-BitVec.ofNat 32 length) (BitVec.ofNat 32 t) (buf+BitVec.ofNat 32 t) (BitVec.ofNat 32 i) byte
    h13 h21 h14 h24 (HeadFieldsMath.guard i t length hi hlen) access (by rw [pointer]) hp
  obtain ⟨n,d,nlo,nhi,classify,endPC,frame2,csr2⟩ := HeadFieldsScanClass.contract B a ram byte pc value
    ((frame 16 (by decide) (by decide)).trans h16) ((frame 17 (by decide) (by decide)).trans h17)
  exact ⟨4+n,d,by omega,by omega,load.trans classify,endPC,(frame2 15).trans (addr.trans pointer),(frame2 30).trans value,
    fun r h15 h30 => (frame2 r).trans (frame r h15 h30),csr2.trans csr⟩
end E5R.Thermostat.HeadFieldsScanStep
