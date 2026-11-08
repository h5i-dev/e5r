import Projects.thermostat.HeadFieldsScanLF
import Projects.thermostat.HeadFieldsScanCR
namespace E5R.Thermostat.HeadFieldsScanClass
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (byte : BitVec 8)
    (hp : c.pc=0x80002f7e#32) (h30 : c.get 30=BitVec.ofNat 32 byte.toNat)
    (h16 : c.get 16=10#32) (h17 : c.get 17=13#32) :
    ∃ n d, 1≤n ∧ n≤2 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if byte.toNat=10 then 0x80003428#32 else if byte.toNat=13 then 0x80002f9a#32 else 0x80002f86#32) ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,lf,pc,frame,csr⟩ := HeadFieldsScanLF.contract B c ram byte hp h30 h16
  by_cases isLF : byte.toNat=10
  · exact ⟨1,a,by decide,by decide,lf,by simpa only [isLF,ite_true] using pc,frame,csr⟩
  · have atCR : a.pc=0x80002f82#32 := by simpa only [isLF,ite_false] using pc
    obtain ⟨d,cr,pc2,frame2,csr2⟩ := HeadFieldsScanCR.contract B a ram byte atCR ((frame 30).trans h30) ((frame 17).trans h17)
    exact ⟨2,d,by decide,by decide,lf.trans cr,by simpa only [isLF,ite_false] using pc2,
      fun r => (frame2 r).trans (frame r),csr2.trans csr⟩
end E5R.Thermostat.HeadFieldsScanClass
