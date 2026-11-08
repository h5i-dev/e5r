import Projects.thermostat.HeadVersionSites
import Projects.thermostat.HeadVersionOffset
import Projects.thermostat.HeadVersionGuard4
import Projects.thermostat.HeadVersionGuard5
import Projects.thermostat.HeadVersionGuard6
import Projects.thermostat.HeadVersionMath
namespace E5R.Thermostat.HeadVersionTail
open E5R E5R.Thermostat

def Good (ram : Word → BitVec 8) (base : Word) : Prop :=
  ram (base+3#32)=84#8 ∧ ram (base+4#32)=84#8 ∧ ram (base+5#32)=80#8 ∧ ram (base+6#32)=47#8

instance (ram : Word → BitVec 8) (base : Word) : Decidable (Good ram base) := by unfold Good;infer_instance

/-- Actual suffix `TTP/` checks after metadata storage. Real arithmetic guards
    are proved false from available version width, rather than assumed absent. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (buf : Word) (m te length : Nat)
    (hp : c.pc=0x80002e3e#32) (h17 : c.get 17=BitVec.ofNat 32 m) (h12 : c.get 12=BitVec.ofNat 32 length)
    (h30 : c.get 30=BitVec.ofNat 32 (te-m-1)) (h6 : c.get 6=buf+BitVec.ofNat 32 (te-1))
    (hm : m<te) (ht : te+9≤length) (hlen : length≤2048) (mem : Memory.Block B buf length) :
    ∃ n d, 7≤n ∧ n≤22 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if Good ram (buf+BitVec.ofNat 32 (te-1)) then 0x80002e8c#32 else 0x80002efa#32) ∧
      d.get 30=BitVec.ofNat 32 (te-1)-BitVec.ofNat 32 length ∧
      (∀ r : Reg, r≠10 → r≠11 → r≠30 → d.get r=c.get r) ∧ d.sameCsr c := by
  let base := buf+BitVec.ofNat 32 (te-1)
  let relative := BitVec.ofNat 32 (te-1)-BitVec.ofNat 32 length
  have arithmetic := HeadVersionMath.offset m te length hm
  have guard3 : taken .eq (BitVec.ofNat 32 (te-m-1)+(BitVec.ofNat 32 m-BitVec.ofNat 32 length)) 0xfffffffd#32=false := by
    rw [arithmetic]
    exact HeadVersionMath.guard te length 3 ht hlen (by decide)
  obtain ⟨a0,start,pc0,minus3,offset0,frame0,csr0⟩ := HeadVersionOffset.contract B c ram
    (BitVec.ofNat 32 m) (BitVec.ofNat 32 length) (BitVec.ofNat 32 (te-m-1)) h17 h12 h30 guard3 hp
  have relative0 : a0.get 30=relative := offset0.trans arithmetic
  have source0 (r : Reg) (h10 : r≠10) (h11 : r≠11) (h30 : r≠30) : a0.get r=c.get r := frame0 r h10 h30
  have access (k : Nat) (hk : 3≤k ∧ k≤6) : B.inRam (base+BitVec.ofNat 32 k) 1=true := by
    have address : base+BitVec.ofNat 32 k=buf+BitVec.ofNat 32 (te+k-1) := by
      change buf+BitVec.ofNat 32 (te-1)+BitVec.ofNat 32 k= _
      rw [BitVec.add_assoc,←BitVec.ofNat_add]
      congr 2
      omega
    rw [address]
    exact Memory.block_access mem (off := te+k-1) (by decide) (by change te+k-1+1≤length;omega)
  obtain ⟨b0,cmp0,cmpPC0,byte0,const0,cmpFrame0,cmpCsr0⟩ := Literal.compare_quiet B img 84#8 (ram (base+3#32)) HeadVersionSites.t1
    a0 ram (base+3#32) pc0 (congrArg (fun x => x+3#32) ((source0 6 (by decide) (by decide) (by decide)).trans h6)) (access 3 (by decide)) rfl
  have relCmp0 : b0.get 30=relative := (cmpFrame0 30 (by decide) (by decide)).trans relative0
  have sourceCmp0 (r : Reg) (h10 : r≠10) (h11 : r≠11) (h30 : r≠30) : b0.get r=c.get r :=
    (cmpFrame0 r h10 h11).trans (source0 r h10 h11 h30)
  by_cases ne0 : ram (base+3#32)≠84#8
  · have bad : ¬Good ram base := by simp only [Good,ne0,false_and,and_false,not_false_eq_true]
    refine ⟨7,b0,by decide,by decide,(start.trans cmp0),?_,relCmp0,sourceCmp0,(cmpCsr0.trans csr0)⟩
    change b0.pc=(if Good ram base then _ else _)
    simpa only [HeadVersionSites.t1,ne0,bad,ite_false] using cmpPC0
  · have eq0 : ram (base+3#32)=84#8 := Classical.not_not.mp ne0
    have nextPC0 : b0.pc=0x80002e56#32 := by simpa only [HeadVersionSites.t1,eq0,ite_true] using cmpPC0
    obtain ⟨a1,guard1,pc1,minus4,guardFrame1,guardCsr1⟩ := HeadVersionGuard4.contract B b0 ram relative relCmp0
      (HeadVersionMath.guard te length 4 ht hlen (by decide)) nextPC0
    have relative1 : a1.get 30=relative := (guardFrame1 30 (by decide)).trans relCmp0
    have source1 (r : Reg) (h10 : r≠10) (h11 : r≠11) (h30 : r≠30) : a1.get r=c.get r :=
      (guardFrame1 r h10).trans (sourceCmp0 r h10 h11 h30)
    obtain ⟨b1,cmp1,cmpPC1,byte1,const1,cmpFrame1,cmpCsr1⟩ := Literal.compare_quiet B img 84#8 (ram (base+4#32)) HeadVersionSites.t2
      a1 ram (base+4#32) pc1 (congrArg (fun x => x+4#32) ((source1 6 (by decide) (by decide) (by decide)).trans h6)) (access 4 (by decide)) rfl
    have relCmp1 : b1.get 30=relative := (cmpFrame1 30 (by decide) (by decide)).trans relative1
    have sourceCmp1 (r : Reg) (h10 : r≠10) (h11 : r≠11) (h30 : r≠30) : b1.get r=c.get r :=
      (cmpFrame1 r h10 h11).trans (source1 r h10 h11 h30)
    by_cases ne1 : ram (base+4#32)≠84#8
    · have bad : ¬Good ram base := by simp only [Good,ne1,false_and,and_false,not_false_eq_true]
      refine ⟨12,b1,by decide,by decide,(((start.trans cmp0).trans guard1).trans cmp1),?_,relCmp1,sourceCmp1,(cmpCsr1.trans (guardCsr1.trans (cmpCsr0.trans csr0)))⟩
      change b1.pc=(if Good ram base then _ else _)
      simpa only [HeadVersionSites.t2,ne1,bad,ite_false] using cmpPC1
    · have eq1 : ram (base+4#32)=84#8 := Classical.not_not.mp ne1
      have nextPC1 : b1.pc=0x80002e68#32 := by simpa only [HeadVersionSites.t2,eq1,ite_true] using cmpPC1
      obtain ⟨a2,guard2,pc2,minus5,guardFrame2,guardCsr2⟩ := HeadVersionGuard5.contract B b1 ram relative relCmp1
        (HeadVersionMath.guard te length 5 ht hlen (by decide)) nextPC1
      have relative2 : a2.get 30=relative := (guardFrame2 30 (by decide)).trans relCmp1
      have source2 (r : Reg) (h10 : r≠10) (h11 : r≠11) (h30 : r≠30) : a2.get r=c.get r :=
        (guardFrame2 r h10).trans (sourceCmp1 r h10 h11 h30)
      obtain ⟨b2,cmp2,cmpPC2,byte2,const2,cmpFrame2,cmpCsr2⟩ := Literal.compare_quiet B img 80#8 (ram (base+5#32)) HeadVersionSites.p
        a2 ram (base+5#32) pc2 (congrArg (fun x => x+5#32) ((source2 6 (by decide) (by decide) (by decide)).trans h6)) (access 5 (by decide)) rfl
      have relCmp2 : b2.get 30=relative := (cmpFrame2 30 (by decide) (by decide)).trans relative2
      have sourceCmp2 (r : Reg) (h10 : r≠10) (h11 : r≠11) (h30 : r≠30) : b2.get r=c.get r :=
        (cmpFrame2 r h10 h11).trans (source2 r h10 h11 h30)
      by_cases ne2 : ram (base+5#32)≠80#8
      · have bad : ¬Good ram base := by simp only [Good,ne2,false_and,and_false,not_false_eq_true]
        refine ⟨17,b2,by decide,by decide,(((((start.trans cmp0).trans guard1).trans cmp1).trans guard2).trans cmp2),?_,relCmp2,sourceCmp2,(cmpCsr2.trans (guardCsr2.trans (cmpCsr1.trans (guardCsr1.trans (cmpCsr0.trans csr0)))))⟩
        change b2.pc=(if Good ram base then _ else _)
        simpa only [HeadVersionSites.p,ne2,bad,ite_false] using cmpPC2
      · have eq2 : ram (base+5#32)=80#8 := Classical.not_not.mp ne2
        have nextPC2 : b2.pc=0x80002e7a#32 := by simpa only [HeadVersionSites.p,eq2,ite_true] using cmpPC2
        obtain ⟨a3,guard3,pc3,minus6,guardFrame3,guardCsr3⟩ := HeadVersionGuard6.contract B b2 ram relative relCmp2
          (HeadVersionMath.guard te length 6 ht hlen (by decide)) nextPC2
        have relative3 : a3.get 30=relative := (guardFrame3 30 (by decide)).trans relCmp2
        have source3 (r : Reg) (h10 : r≠10) (h11 : r≠11) (h30 : r≠30) : a3.get r=c.get r :=
          (guardFrame3 r h10).trans (sourceCmp2 r h10 h11 h30)
        obtain ⟨b3,cmp3,cmpPC3,byte3,const3,cmpFrame3,cmpCsr3⟩ := Literal.compare_quiet B img 47#8 (ram (base+6#32)) HeadVersionSites.slash
          a3 ram (base+6#32) pc3 (congrArg (fun x => x+6#32) ((source3 6 (by decide) (by decide) (by decide)).trans h6)) (access 6 (by decide)) rfl
        have relCmp3 : b3.get 30=relative := (cmpFrame3 30 (by decide) (by decide)).trans relative3
        have sourceCmp3 (r : Reg) (h10 : r≠10) (h11 : r≠11) (h30 : r≠30) : b3.get r=c.get r :=
          (cmpFrame3 r h10 h11).trans (source3 r h10 h11 h30)
        by_cases ne3 : ram (base+6#32)≠47#8
        · have bad : ¬Good ram base := by simp only [Good,ne3,false_and,and_false,not_false_eq_true]
          refine ⟨22,b3,by decide,by decide,(((((((start.trans cmp0).trans guard1).trans cmp1).trans guard2).trans cmp2).trans guard3).trans cmp3),?_,relCmp3,sourceCmp3,(cmpCsr3.trans (guardCsr3.trans (cmpCsr2.trans (guardCsr2.trans (cmpCsr1.trans (guardCsr1.trans (cmpCsr0.trans csr0)))))))⟩
          change b3.pc=(if Good ram base then _ else _)
          simpa only [HeadVersionSites.slash,ne3,bad,ite_false] using cmpPC3
        · have eq3 : ram (base+6#32)=47#8 := Classical.not_not.mp ne3
          have good : Good ram base := ⟨eq0,eq1,eq2,eq3⟩
          refine ⟨22,b3,by decide,by decide,(((((((start.trans cmp0).trans guard1).trans cmp1).trans guard2).trans cmp2).trans guard3).trans cmp3),?_,relCmp3,sourceCmp3,(cmpCsr3.trans (guardCsr3.trans (cmpCsr2.trans (guardCsr2.trans (cmpCsr1.trans (guardCsr1.trans (cmpCsr0.trans csr0)))))))⟩
          change b3.pc=(if Good ram base then _ else _)
          simpa only [HeadVersionSites.slash,eq3,good,ite_true] using cmpPC3
end E5R.Thermostat.HeadVersionTail
