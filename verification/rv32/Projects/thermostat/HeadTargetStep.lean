import Projects.thermostat.HeadTargetLoad
import Projects.thermostat.HeadTargetClass
import Projects.thermostat.HeadTargetMath
namespace E5R.Thermostat.HeadTargetStep
open E5R E5R.Thermostat HttpRequestSpec

/-- The real target-loop read and byte classification, with its slice panic
    excluded by the loop's bounded current index. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (buf : Word) (m i length : Nat)
    (hp : c.pc=0x80002dd8#32) (h17 : c.get 17=BitVec.ofNat 32 m)
    (h30 : c.get 30=BitVec.ofNat 32 (i-m-1)) (h12 : c.get 12=BitVec.ofNat 32 length)
    (h28 : c.get 28=buf+BitVec.ofNat 32 m) (h19 : c.get 19=94#32)
    (hm : m<i) (hi : i<length) (hlen : length≤2048) (mem : Memory.Block B buf length) :
    let byte := ram (buf+BitVec.ofNat 32 i)
    ∃ d, Quiet.Steps B img 7 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if isTargetByte byte.toNat then 0x80002df4#32 else 0x80002dfe#32) ∧
      d.get 18=BitVec.ofNat 32 i ∧ d.get 20=BitVec.ofNat 32 byte.toNat ∧ d.get 6=buf+BitVec.ofNat 32 (i-1) ∧ d.get 7=BitVec.ofNat 32 (i-1) ∧
      (∀ r : Reg, r≠7 → r≠18 → r≠6 → r≠20 → r≠21 → d.get r=c.get r) ∧ d.sameCsr c := by
  let byte := ram (buf+BitVec.ofNat 32 i)
  have current := HeadTargetMath.current m i hm
  have before := HeadTargetMath.before buf m i hm
  have address : buf+BitVec.ofNat 32 m+BitVec.ofNat 32 (i-m-1)+1#32=buf+BitVec.ofNat 32 i := by
    calc
      _ = buf+(BitVec.ofNat 32 m+BitVec.ofNat 32 (i-m-1)+1#32) := by simp only [BitVec.add_assoc]
      _ = _ := congrArg (fun x => buf+x) current
  have test : taken .geu (BitVec.ofNat 32 m+BitVec.ofNat 32 (i-m-1)+1#32) (BitVec.ofNat 32 length)=false := by
    rw [current,HeadTargetMath.geu i length (by omega) hlen]
    simp only [show ¬length≤i by omega,decide_false]
  have access : B.inRam (buf+BitVec.ofNat 32 m+BitVec.ofNat 32 (i-m-1)+1#32) 1=true := by
    rw [address]
    exact Memory.block_access mem (off := i) (by decide) (by change i+1≤length;omega)
  obtain ⟨a,load,pc,sum,index,addr,value,flags,frame,csr⟩ := HeadTargetLoad.contract B c ram
    (BitVec.ofNat 32 m) (BitVec.ofNat 32 (i-m-1)) (BitVec.ofNat 32 length) (buf+BitVec.ofNat 32 m) byte
    h17 h30 h12 h28 test access (by rw [address]) hp
  obtain ⟨d,classify,endPC,frame2,csr2⟩ := HeadTargetClass.contract B a ram byte pc flags
    ((frame 19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h19)
  refine ⟨d,load.trans classify,endPC,?_,?_,?_,?_,?_,csr2.trans csr⟩
  · exact (frame2 18).trans (index.trans current)
  · exact (frame2 20).trans value
  · exact (frame2 6).trans (addr.trans before)
  · have arithmetic : BitVec.ofNat 32 m+BitVec.ofNat 32 (i-m-1)=BitVec.ofNat 32 (i-1) := by
      rw [←BitVec.ofNat_add]
      congr 1
      omega
    exact (frame2 7).trans (sum.trans arithmetic)
  · intro r h7 h18 h6 h20 h21
    exact (frame2 r).trans (frame r h7 h18 h6 h20 h21)
end E5R.Thermostat.HeadTargetStep
