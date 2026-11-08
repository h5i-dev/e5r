import Projects.thermostat.HeadScanLoad
import Projects.thermostat.HeadScanLF
import Projects.thermostat.HeadScanCR
import Projects.thermostat.HeadScanAdvance
import Projects.thermostat.HeadScanMath
namespace E5R.Thermostat.HeadScanIteration
open E5R E5R.Thermostat

def endpoint (b : BitVec 8) (j n : Nat) : Word :=
  if b.toNat=10 then 0x80002d5a#32 else if b.toNat=13 then 0x80002ca8#32
  else if j+1<n then 0x80002c90#32 else 0x80002ce6#32

def cursor (b : BitVec 8) (j : Nat) : Nat := if b.toNat=10 ∨ b.toNat=13 then j else j+1

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (buf : Word) (j n : Nat)
    (hp : c.pc=0x80002c90#32) (h11 : c.get 11=buf) (h9 : c.get 9=BitVec.ofNat 32 j)
    (h14 : c.get 14=BitVec.ofNat 32 n) (h15 : c.get 15=10#32) (h17 : c.get 17=13#32)
    (hm : Memory.Block B buf n) (hj : j<n) (hn : n≤1024) :
    let b := ram (buf+BitVec.ofNat 32 j)
    ∃ steps d, 3≤steps ∧ steps≤7 ∧ Quiet.Steps B img steps ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=endpoint b j n ∧ d.get 9=BitVec.ofNat 32 (cursor b j) ∧
      d.get 5=buf+BitVec.ofNat 32 j ∧ d.get 6=BitVec.ofNat 32 b.toNat ∧
      (∀ r : Reg, r≠5 → r≠6 → r≠9 → d.get r=c.get r) ∧ d.sameCsr c := by
  let b := ram (buf+BitVec.ofNat 32 j)
  change ∃ steps d, 3≤steps ∧ steps≤7 ∧ Quiet.Steps B img steps ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=endpoint b j n ∧ d.get 9=BitVec.ofNat 32 (cursor b j) ∧
      d.get 5=buf+BitVec.ofNat 32 j ∧ d.get 6=BitVec.ofNat 32 b.toNat ∧
      (∀ r : Reg, r≠5 → r≠6 → r≠9 → d.get r=c.get r) ∧ d.sameCsr c
  obtain ⟨a,load,pc1,addr,value,frame1,csr1⟩ := HeadScanLoad.contract B c ram buf (BitVec.ofNat 32 j) b
    h11 h9 (Memory.block_access hm (off := j) (by decide) (by change j+1≤n;omega)) rfl hp
  obtain ⟨e,lf,pc2,frame2,csr2⟩ := HeadScanLF.contract B a ram b pc1 value
    ((frame1 15 (by decide) (by decide)).trans h15)
  have regs (r : Reg) (h5 : r≠5) (h6 : r≠6) : e.get r=c.get r := (frame2 r).trans (frame1 r h5 h6)
  by_cases isLF : b.toNat=10
  · refine ⟨3,e,by decide,by decide,load.trans lf,?_,?_,(frame2 5).trans addr,(frame2 6).trans value,?_,csr2.trans csr1⟩
    · simpa only [endpoint,isLF,ite_true] using pc2
    · simpa only [cursor,isLF,true_or,ite_true] using (regs 9 (by decide) (by decide)).trans h9
    · intro r h5 h6 h9;exact regs r h5 h6
  · have pc2' : e.pc=0x80002c9c#32 := by simpa only [isLF,ite_false] using pc2
    obtain ⟨f,cr,pc3,frame3,csr3⟩ := HeadScanCR.contract B e ram b pc2'
      ((frame2 6).trans value) ((regs 17 (by decide) (by decide)).trans h17)
    have regs2 (r : Reg) (h5 : r≠5) (h6 : r≠6) : f.get r=c.get r := (frame3 r).trans (regs r h5 h6)
    by_cases isCR : b.toNat=13
    · refine ⟨4,f,by decide,by decide,(load.trans lf).trans cr,?_,?_,
        (frame3 5).trans ((frame2 5).trans addr),(frame3 6).trans ((frame2 6).trans value),?_,csr3.trans (csr2.trans csr1)⟩
      · simpa [endpoint,isLF,isCR] using pc3
      · simpa only [cursor,isCR,or_true,ite_true] using (regs2 9 (by decide) (by decide)).trans h9
      · intro r h5 h6 h9;exact regs2 r h5 h6
    · have pc3' : f.pc=0x80002ca0#32 := by simpa only [isCR,ite_false] using pc3
      have nextTest := HeadScanMath.next_again j n hj hn
      by_cases again : j+1<n
      · obtain ⟨g,advance,pc4,index4,frame4,csr4⟩ := HeadScanAdvance.contract B f ram (BitVec.ofNat 32 j)
          (BitVec.ofNat 32 n) true pc3' ((regs2 9 (by decide) (by decide)).trans h9)
          ((regs2 14 (by decide) (by decide)).trans h14) (by simpa only [again,decide_true] using nextTest)
        refine ⟨6,g,by decide,by decide,((load.trans lf).trans cr).trans advance,?_,?_,
          (frame4 5 (by decide)).trans ((frame3 5).trans ((frame2 5).trans addr)),
          (frame4 6 (by decide)).trans ((frame3 6).trans ((frame2 6).trans value)),?_,csr4.trans (csr3.trans (csr2.trans csr1))⟩
        · simpa only [endpoint,isLF,isCR,again,ite_false,ite_true] using pc4
        · simpa only [cursor,isLF,isCR,false_or,ite_false,HeadScanMath.next_word] using index4
        · intro r h5 h6 h9;exact (frame4 r h9).trans (regs2 r h5 h6)
      · obtain ⟨g,advance,pc4,index4,frame4,csr4⟩ := HeadScanAdvance.contract B f ram (BitVec.ofNat 32 j)
          (BitVec.ofNat 32 n) false pc3' ((regs2 9 (by decide) (by decide)).trans h9)
          ((regs2 14 (by decide) (by decide)).trans h14) (by simpa only [again,decide_false] using nextTest)
        obtain ⟨d,finish,pc5,frame5,csr5⟩ := HeadScanAdvance.finish B g ram pc4
        refine ⟨7,d,by decide,by decide,(((load.trans lf).trans cr).trans advance).trans finish,?_,?_,
          (frame5 5).trans ((frame4 5 (by decide)).trans ((frame3 5).trans ((frame2 5).trans addr))),
          (frame5 6).trans ((frame4 6 (by decide)).trans ((frame3 6).trans ((frame2 6).trans value))),?_,
          csr5.trans (csr4.trans (csr3.trans (csr2.trans csr1)))⟩
        · simpa only [endpoint,isLF,isCR,again,ite_false] using pc5
        · simpa only [cursor,isLF,isCR,false_or,ite_false,HeadScanMath.next_word] using (frame5 9).trans index4
        · intro r h5 h6 h9;exact (frame5 r).trans ((frame4 r h9).trans (regs2 r h5 h6))
end E5R.Thermostat.HeadScanIteration
