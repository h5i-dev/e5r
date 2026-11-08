import Projects.thermostat.HeadLineScanSpec
import Projects.thermostat.HeadFoldSites
import Projects.thermostat.HeadHostSpec
import Projects.thermostat.HeadHostGuardLoad
import Projects.thermostat.HeadHostGuard1
import Projects.thermostat.HeadHostGuard2
import Projects.thermostat.HeadHostGuard3
namespace E5R.Thermostat.HeadHostCompare
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- Actual four-byte Host comparison, including all three real slice guards.
    A mismatch selects ordinary-header commit; a full match selects Host flags. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (start length : Nat)
    (hp : c.pc=0x8000310a#32) (h2 : c.get 2=sp) (h24 : c.get 24=BitVec.ofNat 32 start) (h10 : c.get 10=buf+BitVec.ofNat 32 start)
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length)
    (width : start+4≤length) (hlen : length≤2048) (mem : Memory.Block B buf length) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0) :
    let g := bytes ram buf
    ∃ n d, 7≤n ∧ n≤36 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if HeadHostSpec.Prefix g start then 0x80003182#32 else 0x800033b6#32) ∧
      (∀ r : Reg, r≠10 → r≠11 → r≠12 → r≠13 → r≠14 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  change ∃ n d, 7≤n ∧ n≤36 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if HeadHostSpec.Prefix g start then 0x80003182#32 else 0x800033b6#32) ∧
      (∀ r : Reg, r≠10 → r≠11 → r≠12 → r≠13 → r≠14 → d.get r=c.get r) ∧ d.sameCsr c
  have addr0 : (buf+BitVec.ofNat 32 start)+0#32=buf+BitVec.ofNat 32 (start+0) := by
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
  obtain ⟨a0,read0,pc0,value0,literal0,frame0,csr0⟩ := HeadFoldLiteral.compare B img 104#8 (ram (buf+BitVec.ofNat 32 (start+0))) HeadFoldSites.host0
    c ram (buf+BitVec.ofNat 32 (start+0)) hp
    (by change c.get 10+0#32=_;rw [h10,addr0])
    (Memory.block_access mem (off := start+0) (by decide) (by change start+0+1≤length;omega)) rfl
  change a0.pc=(if lower (g start)=104 then 0x80003122#32 else 0x800033b6#32) at pc0
  have source0 (r : Reg) (h11 : r≠11) (h12 : r≠12) (h13 : r≠13) (h14 : r≠14) : a0.get r=c.get r :=
    (frame0 r h11 h13 h12)
  by_cases h0 : lower (g start)=104
  · have atGuard0 : a0.pc=0x80003122#32 := by simpa only [h0,ite_true] using pc0
    obtain ⟨b0,loadGuard,guardPC,remaining0,one,loadFrame,loadCSR⟩ := HeadHostGuardLoad.contract B a0 ram sp (BitVec.ofNat 32 start) (BitVec.ofNat 32 length)
      ((source0 2 (by decide) (by decide) (by decide) (by decide)).trans h2) ((source0 24 (by decide) (by decide) (by decide) (by decide)).trans h24) hraw stack ha atGuard0
    obtain ⟨d0,guard0,nextPC0,guardFrame0,guardCSR0⟩ := HeadHostGuard1.contract B b0 ram (BitVec.ofNat 32 length-BitVec.ofNat 32 start) remaining0
      (HeadHostSpec.guard start length 1 hlen width (by decide)) one guardPC
    have after0 (r : Reg) (h11 : r≠11) (h12 : r≠12) (h13 : r≠13) (h14 : r≠14) : d0.get r=c.get r :=
      (guardFrame0 r).trans ((loadFrame r h11 h12).trans (source0 r h11 h12 h13 h14))
    have rem0 : d0.get 11=BitVec.ofNat 32 length-BitVec.ofNat 32 start := (guardFrame0 11).trans remaining0
    have addr1 : (buf+BitVec.ofNat 32 start)+1#32=buf+BitVec.ofNat 32 (start+1) := by
      rw [BitVec.add_assoc,←BitVec.ofNat_add]
    obtain ⟨a1,read1,pc1,value1,literal1,frame1,csr1⟩ := HeadFoldLiteral.compare B img 111#8 (ram (buf+BitVec.ofNat 32 (start+1))) HeadFoldSites.host1
      d0 ram (buf+BitVec.ofNat 32 (start+1)) nextPC0
      (by change d0.get 10+1#32=_;rw [(after0 10 (by decide) (by decide) (by decide) (by decide)).trans h10,addr1])
      (Memory.block_access mem (off := start+1) (by decide) (by change start+1+1≤length;omega)) rfl
    change a1.pc=(if lower (g (start+1))=111 then 0x80003146#32 else 0x800033b6#32) at pc1
    have source1 (r : Reg) (h11 : r≠11) (h12 : r≠12) (h13 : r≠13) (h14 : r≠14) : a1.get r=c.get r :=
      (frame1 r h13 h14 h12).trans (after0 r h11 h12 h13 h14)
    by_cases h1 : lower (g (start+1))=111
    · have atGuard1 : a1.pc=0x80003146#32 := by simpa only [h1,ite_true] using pc1
      obtain ⟨d1,guard1,nextPC1,literalGuard1,guardFrame1,guardCSR1⟩ := HeadHostGuard2.contract B a1 ram (BitVec.ofNat 32 length-BitVec.ofNat 32 start)
        ((frame1 11 (by decide) (by decide) (by decide)).trans rem0) (HeadHostSpec.guard start length 2 hlen width (by decide)) atGuard1
      have after1 (r : Reg) (h11 : r≠11) (h12 : r≠12) (h13 : r≠13) (h14 : r≠14) : d1.get r=c.get r :=
        (guardFrame1 r h12).trans (source1 r h11 h12 h13 h14)
      have rem1 : d1.get 11=BitVec.ofNat 32 length-BitVec.ofNat 32 start := ((guardFrame1 11 (by decide))).trans ((frame1 11 (by decide) (by decide) (by decide)).trans rem0)
      have addr2 : (buf+BitVec.ofNat 32 start)+2#32=buf+BitVec.ofNat 32 (start+2) := by
        rw [BitVec.add_assoc,←BitVec.ofNat_add]
      obtain ⟨a2,read2,pc2,value2,literal2,frame2,csr2⟩ := HeadFoldLiteral.compare B img 115#8 (ram (buf+BitVec.ofNat 32 (start+2))) HeadFoldSites.host2
        d1 ram (buf+BitVec.ofNat 32 (start+2)) nextPC1
        (by change d1.get 10+2#32=_;rw [(after1 10 (by decide) (by decide) (by decide) (by decide)).trans h10,addr2])
        (Memory.block_access mem (off := start+2) (by decide) (by change start+2+1≤length;omega)) rfl
      change a2.pc=(if lower (g (start+2))=115 then 0x80003164#32 else 0x800033b6#32) at pc2
      have source2 (r : Reg) (h11 : r≠11) (h12 : r≠12) (h13 : r≠13) (h14 : r≠14) : a2.get r=c.get r :=
        (frame2 r h13 h14 h12).trans (after1 r h11 h12 h13 h14)
      by_cases h2 : lower (g (start+2))=115
      · have atGuard2 : a2.pc=0x80003164#32 := by simpa only [h2,ite_true] using pc2
        obtain ⟨d2,guard2,nextPC2,literalGuard2,guardFrame2,guardCSR2⟩ := HeadHostGuard3.contract B a2 ram (BitVec.ofNat 32 length-BitVec.ofNat 32 start)
          ((frame2 11 (by decide) (by decide) (by decide)).trans rem1) (HeadHostSpec.guard start length 3 hlen width (by decide)) atGuard2
        have after2 (r : Reg) (h11 : r≠11) (h12 : r≠12) (h13 : r≠13) (h14 : r≠14) : d2.get r=c.get r :=
          (guardFrame2 r h12).trans (source2 r h11 h12 h13 h14)
        have rem2 : d2.get 11=BitVec.ofNat 32 length-BitVec.ofNat 32 start := ((guardFrame2 11 (by decide))).trans ((frame2 11 (by decide) (by decide) (by decide)).trans rem1)
        have addr3 : (buf+BitVec.ofNat 32 start)+3#32=buf+BitVec.ofNat 32 (start+3) := by
          rw [BitVec.add_assoc,←BitVec.ofNat_add]
        obtain ⟨a3,read3,pc3,value3,literal3,frame3,csr3⟩ := HeadFoldLiteral.compare B img 116#8 (ram (buf+BitVec.ofNat 32 (start+3))) HeadFoldSites.host3
          d2 ram (buf+BitVec.ofNat 32 (start+3)) nextPC2
          (by change d2.get 10+3#32=_;rw [(after2 10 (by decide) (by decide) (by decide) (by decide)).trans h10,addr3])
          (Memory.block_access mem (off := start+3) (by decide) (by change start+3+1≤length;omega)) rfl
        change a3.pc=(if lower (g (start+3))=116 then 0x80003182#32 else 0x800033b6#32) at pc3
        have source3 (r : Reg) (h10 : r≠10) (h11 : r≠11) (h12 : r≠12) (h13 : r≠13) (h14 : r≠14) : a3.get r=c.get r :=
          (frame3 r h10 h11 h11).trans (after2 r h11 h12 h13 h14)
        by_cases h3 : lower (g (start+3))=116
        · have full : HeadHostSpec.Prefix g start := ⟨h0,h1,h2,h3⟩
          refine ⟨36,a3,by decide,by decide,((((((read0.trans loadGuard).trans guard0).trans read1).trans guard1).trans read2).trans guard2).trans read3,?_,source3,csr3.trans (guardCSR2.trans (csr2.trans (guardCSR1.trans (csr1.trans (guardCSR0.trans (loadCSR.trans (csr0)))))))⟩
          simpa [full,h3] using pc3
        · have bad : ¬HeadHostSpec.Prefix g start := by intro full;exact h3 full.2.2.2
          refine ⟨36,a3,by decide,by decide,((((((read0.trans loadGuard).trans guard0).trans read1).trans guard1).trans read2).trans guard2).trans read3,?_,?_,csr3.trans (guardCSR2.trans (csr2.trans (guardCSR1.trans (csr1.trans (guardCSR0.trans (loadCSR.trans (csr0)))))))⟩
          · simpa [bad,h3] using pc3
          · exact source3
      · have bad : ¬HeadHostSpec.Prefix g start := by intro full;exact h2 full.2.2.1
        refine ⟨27,a2,by decide,by decide,((((read0.trans loadGuard).trans guard0).trans read1).trans guard1).trans read2,?_,?_,csr2.trans (guardCSR1.trans (csr1.trans (guardCSR0.trans (loadCSR.trans (csr0)))))⟩
        · simpa [bad,h2] using pc2
        · intro r _ h11 h12 h13 h14;exact source2 r h11 h12 h13 h14
    · have bad : ¬HeadHostSpec.Prefix g start := by intro full;exact h1 full.2.1
      refine ⟨18,a1,by decide,by decide,((read0.trans loadGuard).trans guard0).trans read1,?_,?_,csr1.trans (guardCSR0.trans (loadCSR.trans (csr0)))⟩
      · simpa [bad,h1] using pc1
      · intro r _ h11 h12 h13 h14;exact source1 r h11 h12 h13 h14
  · have bad : ¬HeadHostSpec.Prefix g start := by intro full;exact h0 full.1
    refine ⟨7,a0,by decide,by decide,read0,?_,?_,csr0⟩
    · simpa [bad,h0] using pc0
    · intro r _ h11 h12 h13 h14;exact source0 r h11 h12 h13 h14
end E5R.Thermostat.HeadHostCompare
