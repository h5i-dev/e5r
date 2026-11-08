import Projects.thermostat.MainCloseCode
import Projects.thermostat.MainCloseFoldCertificates
import Projects.thermostat.AsciiFoldCompare
import Projects.thermostat.AsciiFoldBranch
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.MainCloseValueCompare
open E5R E5R.Thermostat

theorem first (B : Board) (c : Core) (ram : Word → BitVec 8) (byte : BitVec 8)
    (hp : c.pc=0x8000260c#32) (h25 : c.get 25=BitVec.ofNat 32 byte.toNat) (h6 : c.get 6=99#32) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if HeaderSpec.lower byte≠99#8 then 0x800025d4#32 else 0x8000261e#32) ∧
      d.get 22=BitVec.ofNat 32 (HeaderSpec.lower byte).toNat ∧
      (∀ r : Reg, r≠22 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨d,trace,pc,value,frame,csr⟩ := AsciiFoldBranch.contract B img c ram 0x8000260c#32 4#32 0xffffffba#32 25 22 22 6 false byte 99#8
    MainCloseFoldCertificates.at2147493388 (by decide) (by decide) (by decide) (by decide) (by decide) hp h25 h6
    (by decide) (by decide)
    (by simpa only [show 0x8000260c#32+10#32+4#32=0x8000261a#32 by decide +kernel] using re2147493402)
  refine ⟨d,trace,?_,value,fun r ne => frame r ne ne,csr⟩
  simpa only [show 0x8000260c#32+10#32+4#32+0xffffffba#32=0x800025d4#32 by decide +kernel,
    show 0x8000260c#32+10#32+4#32+4#32=0x8000261e#32 by decide +kernel] using pc

theorem byte1 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x8000261e#32) (h15 : c.get 15=base) (hliteral : c.get 19=108#32)
    (memory : B.inRam (base+1#32) 1=true) (data : ram (base+1#32)=byte) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if HeaderSpec.lower byte≠108#8 then 0x800025d4#32 else 0x80002634#32) ∧
      d.get 22=BitVec.ofNat 32 (HeaderSpec.lower byte).toNat ∧
      (∀ r : Reg, r≠22 → r≠23 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [show 0x8000261e#32+4#32+10#32+4#32+0xffffffa4#32=0x800025d4#32 by decide +kernel,
      show 0x8000261e#32+4#32+10#32+4#32+4#32=0x80002634#32 by decide +kernel] using
    AsciiFoldCompare.contract B img c ram 0x8000261e#32 base 1#32 4#32 0xffffffa4#32 15 22 23 19 false byte 108#8
      hp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h15 hliteral memory data re2147493406
      (by simpa only [show 0x8000261e#32+4#32=0x80002622#32 by decide +kernel] using MainCloseFoldCertificates.at2147493410)
      (by decide) (by decide)
      (by simpa only [show 0x8000261e#32+4#32+10#32+4#32=0x80002630#32 by decide +kernel] using re2147493424)

theorem byte2 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x80002634#32) (h15 : c.get 15=base) (hliteral : c.get 7=111#32)
    (memory : B.inRam (base+2#32) 1=true) (data : ram (base+2#32)=byte) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if HeaderSpec.lower byte≠111#8 then 0x800025d4#32 else 0x8000264a#32) ∧
      d.get 22=BitVec.ofNat 32 (HeaderSpec.lower byte).toNat ∧
      (∀ r : Reg, r≠22 → r≠23 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [show 0x80002634#32+4#32+10#32+4#32+0xffffff8e#32=0x800025d4#32 by decide +kernel,
      show 0x80002634#32+4#32+10#32+4#32+4#32=0x8000264a#32 by decide +kernel] using
    AsciiFoldCompare.contract B img c ram 0x80002634#32 base 2#32 4#32 0xffffff8e#32 15 22 23 7 false byte 111#8
      hp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h15 hliteral memory data re2147493428
      (by simpa only [show 0x80002634#32+4#32=0x80002638#32 by decide +kernel] using MainCloseFoldCertificates.at2147493432)
      (by decide) (by decide)
      (by simpa only [show 0x80002634#32+4#32+10#32+4#32=0x80002646#32 by decide +kernel] using re2147493446)

theorem byte3 (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x8000264a#32) (h15 : c.get 15=base) (hliteral : c.get 20=115#32)
    (memory : B.inRam (base+3#32) 1=true) (data : ram (base+3#32)=byte) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if HeaderSpec.lower byte≠115#8 then 0x800025d4#32 else 0x80002660#32) ∧
      d.get 22=BitVec.ofNat 32 (HeaderSpec.lower byte).toNat ∧
      (∀ r : Reg, r≠22 → r≠23 → d.get r=c.get r) ∧ d.sameCsr c := by
  simpa only [show 0x8000264a#32+4#32+10#32+4#32+0xffffff78#32=0x800025d4#32 by decide +kernel,
      show 0x8000264a#32+4#32+10#32+4#32+4#32=0x80002660#32 by decide +kernel] using
    AsciiFoldCompare.contract B img c ram 0x8000264a#32 base 3#32 4#32 0xffffff78#32 15 22 23 20 false byte 115#8
      hp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h15 hliteral memory data re2147493450
      (by simpa only [show 0x8000264a#32+4#32=0x8000264e#32 by decide +kernel] using MainCloseFoldCertificates.at2147493454)
      (by decide) (by decide)
      (by simpa only [show 0x8000264a#32+4#32+10#32+4#32=0x8000265c#32 by decide +kernel] using re2147493468)

theorem lastByte (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (byte : BitVec 8)
    (hp : c.pc=0x80002660#32) (h15 : c.get 15=base)
    (memory : B.inRam (base+4#32) 1=true) (data : ram (base+4#32)=byte) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002672#32 ∧
      d.get 15=BitVec.ofNat 32 (HeaderSpec.lower byte).toNat ∧
      (∀ r : Reg, r≠15 → r≠22 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,load,pa,av,ar,ac⟩ := QuietByteLoad.contract B img c ram 0x80002660#32 base 4#32 15 15 byte
    hp (by decide) (by decide) re2147493472 h15 memory data
  have pa' : a.pc=0x80002664#32 := by simpa only [show 0x80002660#32+4#32=0x80002664#32 by decide +kernel] using pa
  obtain ⟨d,fold,pd,dv,dr,dc⟩ := AsciiFoldProgram.contract B img a ram 0x80002664#32 15 22 15 false 4#32 byte
    MainCloseFoldCertificates.at2147493476 (by decide) (by decide) (by decide) pa' av
  refine ⟨d,load.trans fold,?_,dv,?_,dc.trans ac⟩
  · simpa only [show 0x80002664#32+10#32+4#32=0x80002672#32 by decide +kernel] using pd
  · intro r n15 n22
    exact (dr r n22 n15).trans (ar r n15)
end E5R.Thermostat.MainCloseValueCompare
