import Projects.thermostat.HeadMethodPrefix
import Projects.thermostat.HeadMethodStart
import Projects.thermostat.HeadMethodScan
import Projects.thermostat.HeadMethodSpace
namespace E5R.Thermostat.HeadMethodStrong
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

abbrev Good := HeadMethodPrefix.Good

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (buf : Word) (j length : Nat)
    (hp : c.pc=0x80002cba#32) (h9 : c.get 9=BitVec.ofNat 32 j) (h12 : c.get 12=BitVec.ofNat 32 length)
    (h11 : c.get 11=buf) (hj : j≤length) (hlen : length≤2048) (hm : Memory.Block B buf length) :
    let g := bytes ram buf
    let m := scan isTchar g 0 j
    ∃ steps d, 0<steps ∧ steps≤21+18*j ∧ Quiet.Steps B img steps ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if Good g j then 0x80002dc0#32 else 0x80002efc#32) ∧ d.get 15=400#32 ∧
      (0<j → d.get 17=BitVec.ofNat 32 m) ∧ (Good g j → d.get 28=buf+BitVec.ofNat 32 m) ∧
      (Good g j → d.get 5=9409#32) ∧
      (∀ r : Reg, r≠5 → r≠6 → r≠7 → r≠8 → r≠15 → r≠17 → r≠18 → r≠19 → r≠28 → r≠29 → r≠30 → r≠31 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  let m := scan isTchar g 0 j
  change ∃ steps d, 0<steps ∧ steps≤21+18*j ∧ Quiet.Steps B img steps ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if Good g j then 0x80002dc0#32 else 0x80002efc#32) ∧ d.get 15=400#32 ∧
      (0<j → d.get 17=BitVec.ofNat 32 m) ∧ (Good g j → d.get 28=buf+BitVec.ofNat 32 m) ∧
      (Good g j → d.get 5=9409#32) ∧
      (∀ r : Reg, r≠5 → r≠6 → r≠7 → r≠8 → r≠15 → r≠17 → r≠18 → r≠19 → r≠28 → r≠29 → r≠30 → r≠31 → d.get r=c.get r) ∧ d.sameCsr c
  by_cases empty : j=0
  · subst j
    obtain ⟨d,entry,pc,status,frame,csr⟩ := HeadMethodEntry.contract B c ram 0#32 true hp h9 (by decide +kernel)
    refine ⟨2,d,by decide,by decide,entry,?_,status,by omega,?_,?_,?_,csr⟩
    · have bad : ¬Good g 0 := by simp [Good,HeadMethodPrefix.Good,scan]
      simpa only [bad,ite_false,ite_true] using pc
    · intro good
      have bad : ¬Good g 0 := by simp [Good,HeadMethodPrefix.Good,scan]
      exact False.elim (bad good)
    · intro good
      have bad : ¬Good g 0 := by simp [Good,HeadMethodPrefix.Good,scan]
      exact False.elim (bad good)
    · intro r h5 h6 h7 h8 h15 h17 h18 h19 h28 h29 h30 h31
      exact frame r h15
  · have positive : 0<j := by omega
    obtain ⟨a,start,pc,index,status,constants,frame1,csr1⟩ := HeadMethodStart.contract B c ram j hp h9 positive (by omega)
    have source1 (r : Reg) (h5 : r≠5) (h6 : r≠6) (h7 : r≠7) (h8 : r≠8) (h15 : r≠15)
        (h17 : r≠17) (h18 : r≠18) (h29 : r≠29) (h30 : r≠30) (h31 : r≠31) : a.get r=c.get r :=
      frame1 r h15 h17 h5 h6 h7 h8 h18 h29 h30 h31
    obtain ⟨n,d,hlo,hn,scan,endPC,stop,constants2,cache,frame2,csr2⟩ := HeadMethodScan.contract B a ram buf 0 j length pc
      ((source1 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h12)
      index ((source1 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h11)
      ((source1 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h9)
      constants positive hj hlen hm
    have status2 : d.get 15=400#32 := (frame2 15 (by decide) (by decide) (by decide)).trans status
    have source2 (r : Reg) (h5 : r≠5) (h6 : r≠6) (h7 : r≠7) (h8 : r≠8) (h15 : r≠15)
        (h17 : r≠17) (h18 : r≠18) (h19 : r≠19) (h28 : r≠28) (h29 : r≠29) (h30 : r≠30) (h31 : r≠31) : d.get r=c.get r :=
      (frame2 r h17 h19 h28).trans (source1 r h5 h6 h7 h8 h15 h17 h18 h29 h30 h31)
    have bounded : m≤j := scan_le isTchar g 0 j (by omega)
    by_cases inside : m<j
    · by_cases small : g m<33
      · have atSpace : d.pc=0x80002da2#32 := by
          change d.pc=HeadMethodSpec.pc g m j at endPC
          simpa only [HeadMethodSpec.pc,show ¬j≤m by omega,small,ite_false,ite_true] using endPC
        let b := ram (buf+BitVec.ofNat 32 m)
        obtain ⟨e,space,pc3,frame3,csr3⟩ := HeadMethodSpace.contract B d ram m j b atSpace stop
          ((source2 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h9)
          (cache inside small).1 inside (by omega)
        have goodEq : Good g j ↔ ¬(m=0 ∨ b.toNat≠32) := by
          change (0<m ∧ m<j ∧ g m=32) ↔ _
          change (0<m ∧ m<j ∧ b.toNat=32) ↔ _
          omega
        refine ⟨13+n+8,e,by omega,by omega,(start.trans scan).trans space,?_,
          (frame3 15 (by decide) (by decide) (by decide)).trans status2,
          fun _ => (frame3 17 (by decide) (by decide) (by decide)).trans stop,?_,?_,?_,csr3.trans (csr2.trans csr1)⟩
        · by_cases good : Good g j
          · have valid : ¬(m=0 ∨ b.toNat≠32) := goodEq.mp good
            simpa only [good,valid,ite_true,ite_false] using pc3
          · have invalid : m=0 ∨ b.toNat≠32 := by exact Classical.not_not.mp (fun h => good (goodEq.mpr h))
            simpa only [good,invalid,ite_false,ite_true] using pc3
        · intro good
          exact (frame3 28 (by decide) (by decide) (by decide)).trans (cache inside small).2
        · intro _
          exact (frame3 5 (by decide) (by decide) (by decide)).trans constants2.x5
        · intro r h5 h6 h7 h8 h15 h17 h18 h19 h28 h29 h30 h31
          exact (frame3 r h6 h7 h19).trans (source2 r h5 h6 h7 h8 h15 h17 h18 h19 h28 h29 h30 h31)
      · have bad : ¬Good g j := by
          intro good
          have last : g m=32 := good.2.2
          rw [last] at small
          omega
        refine ⟨13+n,d,by omega,by omega,start.trans scan,?_,status2,fun _ => stop,fun good => False.elim (bad good),fun good => False.elim (bad good),source2,csr2.trans csr1⟩
        change d.pc=HeadMethodSpec.pc g m j at endPC
        simpa only [HeadMethodSpec.pc,show ¬j≤m by omega,small,bad,ite_false] using endPC
    · have bad : ¬Good g j := by intro good;have := good.2.1;omega
      refine ⟨13+n,d,by omega,by omega,start.trans scan,?_,status2,fun _ => stop,fun good => False.elim (bad good),fun good => False.elim (bad good),source2,csr2.trans csr1⟩
      change d.pc=HeadMethodSpec.pc g m j at endPC
      simpa only [HeadMethodSpec.pc,show j≤m by omega,bad,ite_true,ite_false] using endPC
end E5R.Thermostat.HeadMethodStrong
