import Projects.thermostat.HeadFieldsScanAdvanceRaw
import Projects.thermostat.HeadFieldsScanBranch
import Projects.thermostat.HeadFieldsMath
namespace E5R.Thermostat.HeadFieldsScanAdvance
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (i t cap : Nat)
    (hp : c.pc=0x80002f86#32) (h21 : c.get 21=BitVec.ofNat 32 t) (h24 : c.get 24=BitVec.ofNat 32 i)
    (h14 : c.get 14=buf+BitVec.ofNat 32 t) (h25 : c.get 25=BitVec.ofNat 32 t+0xffffffff#32)
    (h11 : c.get 11=BitVec.ofNat 32 (i+t)) (h2 : c.get 2=sp)
    (hcap : ramRead ram (sp+40#32) .w=BitVec.ofNat 32 cap)
    (hi : i+t<cap) (hn : cap≤2048) (hm : Memory.Block B sp 56) (ha : sp.toNat%4=0) :
    ∃ n d, 7≤n ∧ n≤8 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if i+(t+1)<cap then 0x80002f6e#32 else 0x800033ea#32) ∧
      d.get 21=BitVec.ofNat 32 (t+1) ∧ d.get 14=buf+BitVec.ofNat 32 (t+1) ∧
      d.get 25=BitVec.ofNat 32 (t+1)+0xffffffff#32 ∧ d.get 11=BitVec.ofNat 32 (i+(t+1)) ∧
      (∀ r : Reg, r≠21 → r≠30 → r≠14 → r≠25 → r≠11 → r≠15 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,inc,pc,countWord,indexWord,ptrWord,inverseWord,cursorWord,limitWord,frame,csr⟩ := HeadFieldsScanAdvanceRaw.contract B c ram
    sp (BitVec.ofNat 32 t) (BitVec.ofNat 32 i) (buf+BitVec.ofNat 32 t) (BitVec.ofNat 32 t+0xffffffff#32)
    (BitVec.ofNat 32 (i+t)) (BitVec.ofNat 32 cap) h21 h24 h14 h25 h11 h2 hcap hm ha hp
  have count : a.get 21=BitVec.ofNat 32 (t+1) := countWord.trans (HeadFieldsMath.count_next t)
  have index : a.get 30=BitVec.ofNat 32 (i+(t+1)) := indexWord.trans (by rw [HeadFieldsMath.count_next,←BitVec.ofNat_add])
  have ptr : a.get 14=buf+BitVec.ofNat 32 (t+1) := ptrWord.trans (HeadFieldsMath.pointer_next buf t)
  have inverse : a.get 25=BitVec.ofNat 32 (t+1)+0xffffffff#32 := inverseWord.trans (HeadFieldsMath.inverse_next t)
  have cursor : a.get 11=BitVec.ofNat 32 (i+(t+1)) := cursorWord.trans (HeadFieldsMath.index_next i t)
  obtain ⟨b,branch,pc2,frame2,csr2⟩ := HeadFieldsScanBranch.contract B a ram (BitVec.ofNat 32 (i+(t+1))) (BitVec.ofNat 32 cap)
    (decide (i+(t+1)<cap)) pc index limitWord (HeadFieldsMath.next_test i t cap hi hn)
  have source (r : Reg) (h21 : r≠21) (h30 : r≠30) (h14 : r≠14) (h25 : r≠25) (h11 : r≠11) (h15 : r≠15) : b.get r=c.get r :=
    (frame2 r).trans (frame r h21 h30 h14 h25 h11 h15)
  by_cases more : i+(t+1)<cap
  · refine ⟨7,b,by decide,by decide,inc.trans branch,?_,(frame2 21).trans count,(frame2 14).trans ptr,
      (frame2 25).trans inverse,(frame2 11).trans cursor,source,csr2.trans csr⟩
    simpa only [more,decide_true,ite_true] using pc2
  · have atExit : b.pc=0x80002f98#32 := by simpa only [more,decide_false,Bool.false_eq_true,ite_false] using pc2
    obtain ⟨d,exit,pc3,frame3,csr3⟩ := HeadFieldsScanBranch.exhausted B b ram atExit
    refine ⟨8,d,by decide,by decide,(inc.trans branch).trans exit,?_,(frame3 21).trans ((frame2 21).trans count),
      (frame3 14).trans ((frame2 14).trans ptr),(frame3 25).trans ((frame2 25).trans inverse),
      (frame3 11).trans ((frame2 11).trans cursor),?_,csr3.trans (csr2.trans csr)⟩
    · simpa only [more,ite_false] using pc3
    · intro r h21 h30 h14 h25 h11 h15
      exact (frame3 r).trans (source r h21 h30 h14 h25 h11 h15)
end E5R.Thermostat.HeadFieldsScanAdvance
