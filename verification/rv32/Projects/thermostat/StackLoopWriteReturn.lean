import Projects.thermostat.LoopWriteReturn
import Projects.thermostat.StackAccess
set_option autoImplicit false
namespace E5R.Thermostat.StackLoopWriteReturn
open E5R E5R.Thermostat LoopWriteReturn
abbrev B := StackBoard.board
theorem extract (kind : Fin 4) (c : Core) (ram : Word → BitVec 8) (ct len used status : Word)
    (hp : c.pc=entry kind) (h2 : c.get 2=sp) (h8 : c.get 8=fp) (h18 : c.get 18=2#32) (h22 : c.get 22=1#32)
    (hm : Memory.Block B sp 5232) (hv : BodyMemory.At ram 0x80fffd38#32 ct len used status) (hst : status.toNat<65536) :
    ∃ d n after, n≤13 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧ d.pc=0x80001710#32 ∧
      d.get 2=sp ∧ d.get 8=fp ∧ d.get 22=1#32 ∧ d.get 12=ct ∧ d.get 11=len ∧ d.get 20=used ∧ d.get 10=status ∧
      d.get 13=0#32 ∧ d.get 9=0x80fff878#32 ∧ d.get 24=0xfffffffe#32 ∧ d.sameCsr c ∧ ViewFrame.Region ram after sp 3780 ∧ d.get 19=c.get 19 ∧ d.get 18=c.get 18 ∧ d.get 23=c.get 23 ∧ d.get 26=c.get 26 := by
  have flag : ram 0x80fffd46#32=0#8 := BodyResponseView.extra hv
  have ctWord : ramRead ram 0x80fffd38#32 .w=ct := by
    simpa only [Nat.mul_zero,BitVec.add_zero,ite_true] using BodyResponseView.word hv ⟨0,by decide⟩
  have lenWord : ramRead ram 0x80fffd3c#32 .w=len := by
    simpa only [show (4*1 : Nat)=4 by decide,show 0x80fffd38#32+4#32=0x80fffd3c#32 by decide +kernel,
      show (1 : Nat)≠0 by decide,ite_false,ite_true] using BodyResponseView.word hv ⟨1,by decide⟩
  have usedWord : ramRead ram 0x80fffd40#32 .w=used := by
    simpa only [show (4*2 : Nat)=8 by decide,show 0x80fffd38#32+8#32=0x80fffd40#32 by decide +kernel,
      show (2 : Nat)≠0 by decide,show (2 : Nat)≠1 by decide,ite_false] using BodyResponseView.word hv ⟨2,by decide⟩
  have statusHalf : extend .h false (ramRead ram 0x80fffd44#32 .h)=status := by
    simpa only [show 0x80fffd38#32+12#32=0x80fffd44#32 by decide +kernel] using BodyResponseView.half hv hst
  have kinds : kind=0 ∨ kind=1 ∨ kind=2 ∨ kind=3 := by omega
  rcases kinds with rfl|rfl|rfl|rfl
  · obtain ⟨d,steps,pd,d13,d12,d11,d20,d10,d6,d9,d24,keep,csr⟩ := MainSetpointReturn.contract B c ram ct len used status h2 h8 h18 h22 hm ctWord lenWord usedWord statusHalf flag hp
    refine ⟨d,13,MainSetpointReturn.memory ram ct len used status,by decide,steps,pd,?_,?_,?_,d12,d11,d20,d10,d13,d9,d24,csr,?_,?_,?_,?_,?_⟩
    · exact (keep 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2
    · exact (keep 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h8
    · exact (keep 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h22
    · simpa only [BitVec.add_zero] using MainSetpointReturn.frame ram ct len used status 0 3780 (by decide) (Or.inl (by decide))
    · exact keep 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact keep 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact keep 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact keep 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · obtain ⟨d,steps,pd,d13,d12,d11,d20,d10,d6,d9,d24,keep,csr⟩ := MainTempReturn.contract B c ram ct len used status h2 h8 h18 h22 hm ctWord lenWord usedWord statusHalf flag hp
    refine ⟨d,13,MainTempReturn.memory ram ct len used status,by decide,steps,pd,?_,?_,?_,d12,d11,d20,d10,d13,d9,d24,csr,?_,?_,?_,?_,?_⟩
    · exact (keep 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2
    · exact (keep 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h8
    · exact (keep 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h22
    · simpa only [BitVec.add_zero] using MainTempReturn.frame ram ct len used status 0 3780 (by decide) (Or.inl (by decide))
    · exact keep 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact keep 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact keep 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact keep 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · obtain ⟨d,steps,pd,d13,d12,d11,d20,d10,d6,d9,d24,keep,csr⟩ := MainModeReturn.contract B c ram ct len used status h2 h8 h18 h22 hm ctWord lenWord usedWord statusHalf flag hp
    refine ⟨d,12,MainModeReturn.memory ram ct len used status,by decide,steps,pd,?_,?_,?_,d12,d11,d20,d10,d13,d9,d24,csr,?_,?_,?_,?_,?_⟩
    · exact (keep 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2
    · exact (keep 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h8
    · exact (keep 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h22
    · simpa only [BitVec.add_zero] using MainModeReturn.frame ram ct len used status 0 3780 (by decide) (Or.inl (by decide))
    · exact keep 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact keep 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact keep 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact keep 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · obtain ⟨d,steps,pd,d13,d9,d12,d11,d20,d10,d6,d24,keep,csr⟩ := MainRelayReturn.contract B c ram ct len used status h2 h8 h18 h22 hm ctWord lenWord usedWord statusHalf flag hp
    refine ⟨d,12,ram,by decide,steps,pd,?_,?_,?_,d12,d11,d20,d10,d13,d9,d24,csr,?_,?_,?_,?_,?_⟩
    · exact (keep 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2
    · exact (keep 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h8
    · exact (keep 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h22
    · intro i;rfl
    · exact keep 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact keep 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact keep 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact keep 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)


end E5R.Thermostat.StackLoopWriteReturn
