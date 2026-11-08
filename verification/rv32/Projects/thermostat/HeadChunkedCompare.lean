import Projects.thermostat.HeadFoldSites
import Projects.thermostat.HeadChunkedSpec
import Projects.thermostat.HeadChunkedGuardLoad
import Projects.thermostat.HeadChunkedGuard1
import Projects.thermostat.HeadChunkedGuard2
import Projects.thermostat.HeadChunkedGuard3
import Projects.thermostat.HeadChunkedGuard4
import Projects.thermostat.HeadChunkedGuard5
import Projects.thermostat.HeadChunkedGuard6
import Projects.thermostat.HeadLineScanSpec
namespace E5R.Thermostat.HeadChunkedCompare
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- Actual seven-byte chunked comparison, including all six real slice guards.
    A mismatch selects rejection; a full match selects the actual TE flag store. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (start length : Nat)
    (hp : c.pc=0x800032e0#32) (h2 : c.get 2=sp) (h15 : c.get 15=BitVec.ofNat 32 start) (h10 : c.get 10=buf+BitVec.ofNat 32 start)
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length)
    (width : start+7≤length) (hlen : length≤2048) (mem : Memory.Block B buf length) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0) :
    let g := bytes ram buf
    ∃ n d, 7≤n ∧ n≤63 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if HeadChunkedSpec.Prefix g start then 0x800033b0#32 else 0x8000342c#32) ∧
      (∀ r : Reg, r≠10 → r≠11 → r≠12 → r≠13 → r≠14 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  change ∃ n d, 7≤n ∧ n≤63 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
    d.pc=(if HeadChunkedSpec.Prefix g start then 0x800033b0#32 else 0x8000342c#32) ∧
    (∀ r : Reg, r≠10 → r≠11 → r≠12 → r≠13 → r≠14 → d.get r=c.get r) ∧ d.sameCsr c
  have addr0 : (buf+BitVec.ofNat 32 start)+0#32=buf+BitVec.ofNat 32 (start+0) := by
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
  obtain ⟨a0,read0,pc0,value0,literal0,frame0,csr0⟩ := HeadFoldLiteral.compare B img 99#8 (ram (buf+BitVec.ofNat 32 (start+0))) HeadFoldSites.chunk0
    c ram (buf+BitVec.ofNat 32 (start+0)) hp
    (by change c.get 10+0#32=_;rw [h10,addr0])
    (Memory.block_access mem (off := start+0) (by decide) (by change start+0+1≤length;omega)) rfl
  change a0.pc=(if lower (g start)=99 then 0x800032f8#32 else 0x8000342c#32) at pc0
  have source0 (r : Reg) (h11 : r≠11) (h12 : r≠12) (h13 : r≠13) (h14 : r≠14) : a0.get r=c.get r :=
    (frame0 r h11 h12 h12)
  by_cases h0 : lower (g start)=99
  · have atGuard0 : a0.pc=0x800032f8#32 := by simpa only [h0,ite_true] using pc0
    obtain ⟨b0,loadGuard,guardPC,remaining0,one,loadFrame,loadCSR⟩ := HeadChunkedGuardLoad.contract B a0 ram sp (BitVec.ofNat 32 start) (BitVec.ofNat 32 length)
      ((source0 2 (by decide) (by decide) (by decide) (by decide)).trans h2) ((source0 15 (by decide) (by decide) (by decide) (by decide)).trans h15) hraw stack ha atGuard0
    obtain ⟨d0,guard0,nextPC0,guardFrame0,guardCSR0⟩ := HeadChunkedGuard1.contract B b0 ram (BitVec.ofNat 32 length-BitVec.ofNat 32 start) remaining0
      (HeadChunkedSpec.guard start length 1 hlen width (by decide)) one guardPC
    have after0 (r : Reg) (h11 : r≠11) (h12 : r≠12) (h13 : r≠13) (h14 : r≠14) : d0.get r=c.get r :=
      (guardFrame0 r).trans ((loadFrame r h11 h12).trans (source0 r h11 h12 h13 h14))
    have rem0 : d0.get 11=BitVec.ofNat 32 length-BitVec.ofNat 32 start := (guardFrame0 11).trans remaining0
    have addr1 : (buf+BitVec.ofNat 32 start)+1#32=buf+BitVec.ofNat 32 (start+1) := by
      rw [BitVec.add_assoc,←BitVec.ofNat_add]
    obtain ⟨a1,read1,pc1,value1,literal1,frame1,csr1⟩ := HeadFoldLiteral.compare B img 104#8 (ram (buf+BitVec.ofNat 32 (start+1))) HeadFoldSites.chunk1
      d0 ram (buf+BitVec.ofNat 32 (start+1)) nextPC0
      (by change d0.get 10+1#32=_;rw [(after0 10 (by decide) (by decide) (by decide) (by decide)).trans h10,addr1])
      (Memory.block_access mem (off := start+1) (by decide) (by change start+1+1≤length;omega)) rfl
    change a1.pc=(if lower (g (start+1))=104 then 0x8000331a#32 else 0x8000342c#32) at pc1
    have source1 (r : Reg) (h11 : r≠11) (h12 : r≠12) (h13 : r≠13) (h14 : r≠14) : a1.get r=c.get r :=
      (frame1 r h12 h13 h13).trans (after0 r h11 h12 h13 h14)
    by_cases h1 : lower (g (start+1))=104
    · have atGuard1 : a1.pc=0x8000331a#32 := by simpa only [h1,ite_true] using pc1
      obtain ⟨d1,guard1,nextPC1,literalGuard1,guardFrame1,guardCSR1⟩ := HeadChunkedGuard2.contract B a1 ram (BitVec.ofNat 32 length-BitVec.ofNat 32 start)
        ((frame1 11 (by decide) (by decide) (by decide)).trans rem0) (HeadChunkedSpec.guard start length 2 hlen width (by decide)) atGuard1
      have after1 (r : Reg) (h11 : r≠11) (h12 : r≠12) (h13 : r≠13) (h14 : r≠14) : d1.get r=c.get r :=
        (guardFrame1 r h12).trans (source1 r h11 h12 h13 h14)
      have rem1 : d1.get 11=BitVec.ofNat 32 length-BitVec.ofNat 32 start := ((guardFrame1 11 (by decide))).trans ((frame1 11 (by decide) (by decide) (by decide)).trans rem0)
      have addr2 : (buf+BitVec.ofNat 32 start)+2#32=buf+BitVec.ofNat 32 (start+2) := by
        rw [BitVec.add_assoc,←BitVec.ofNat_add]
      obtain ⟨a2,read2,pc2,value2,literal2,frame2,csr2⟩ := HeadFoldLiteral.compare B img 117#8 (ram (buf+BitVec.ofNat 32 (start+2))) HeadFoldSites.chunk2
        d1 ram (buf+BitVec.ofNat 32 (start+2)) nextPC1
        (by change d1.get 10+2#32=_;rw [(after1 10 (by decide) (by decide) (by decide) (by decide)).trans h10,addr2])
        (Memory.block_access mem (off := start+2) (by decide) (by change start+2+1≤length;omega)) rfl
      change a2.pc=(if lower (g (start+2))=117 then 0x80003338#32 else 0x8000342c#32) at pc2
      have source2 (r : Reg) (h11 : r≠11) (h12 : r≠12) (h13 : r≠13) (h14 : r≠14) : a2.get r=c.get r :=
        (frame2 r h12 h13 h13).trans (after1 r h11 h12 h13 h14)
      by_cases h2 : lower (g (start+2))=117
      · have atGuard2 : a2.pc=0x80003338#32 := by simpa only [h2,ite_true] using pc2
        obtain ⟨d2,guard2,nextPC2,literalGuard2,guardFrame2,guardCSR2⟩ := HeadChunkedGuard3.contract B a2 ram (BitVec.ofNat 32 length-BitVec.ofNat 32 start)
          ((frame2 11 (by decide) (by decide) (by decide)).trans rem1) (HeadChunkedSpec.guard start length 3 hlen width (by decide)) atGuard2
        have after2 (r : Reg) (h11 : r≠11) (h12 : r≠12) (h13 : r≠13) (h14 : r≠14) : d2.get r=c.get r :=
          (guardFrame2 r h12).trans (source2 r h11 h12 h13 h14)
        have rem2 : d2.get 11=BitVec.ofNat 32 length-BitVec.ofNat 32 start := ((guardFrame2 11 (by decide))).trans ((frame2 11 (by decide) (by decide) (by decide)).trans rem1)
        have addr3 : (buf+BitVec.ofNat 32 start)+3#32=buf+BitVec.ofNat 32 (start+3) := by
          rw [BitVec.add_assoc,←BitVec.ofNat_add]
        obtain ⟨a3,read3,pc3,value3,literal3,frame3,csr3⟩ := HeadFoldLiteral.compare B img 110#8 (ram (buf+BitVec.ofNat 32 (start+3))) HeadFoldSites.chunk3
          d2 ram (buf+BitVec.ofNat 32 (start+3)) nextPC2
          (by change d2.get 10+3#32=_;rw [(after2 10 (by decide) (by decide) (by decide) (by decide)).trans h10,addr3])
          (Memory.block_access mem (off := start+3) (by decide) (by change start+3+1≤length;omega)) rfl
        change a3.pc=(if lower (g (start+3))=110 then 0x80003356#32 else 0x8000342c#32) at pc3
        have source3 (r : Reg) (h11 : r≠11) (h12 : r≠12) (h13 : r≠13) (h14 : r≠14) : a3.get r=c.get r :=
          (frame3 r h12 h13 h13).trans (after2 r h11 h12 h13 h14)
        by_cases h3 : lower (g (start+3))=110
        · have atGuard3 : a3.pc=0x80003356#32 := by simpa only [h3,ite_true] using pc3
          obtain ⟨d3,guard3,nextPC3,literalGuard3,guardFrame3,guardCSR3⟩ := HeadChunkedGuard4.contract B a3 ram (BitVec.ofNat 32 length-BitVec.ofNat 32 start)
            ((frame3 11 (by decide) (by decide) (by decide)).trans rem2) (HeadChunkedSpec.guard start length 4 hlen width (by decide)) atGuard3
          have after3 (r : Reg) (h11 : r≠11) (h12 : r≠12) (h13 : r≠13) (h14 : r≠14) : d3.get r=c.get r :=
            (guardFrame3 r h12).trans (source3 r h11 h12 h13 h14)
          have rem3 : d3.get 11=BitVec.ofNat 32 length-BitVec.ofNat 32 start := ((guardFrame3 11 (by decide))).trans ((frame3 11 (by decide) (by decide) (by decide)).trans rem2)
          have addr4 : (buf+BitVec.ofNat 32 start)+4#32=buf+BitVec.ofNat 32 (start+4) := by
            rw [BitVec.add_assoc,←BitVec.ofNat_add]
          obtain ⟨a4,read4,pc4,value4,literal4,frame4,csr4⟩ := HeadFoldLiteral.compare B img 107#8 (ram (buf+BitVec.ofNat 32 (start+4))) HeadFoldSites.chunk4
            d3 ram (buf+BitVec.ofNat 32 (start+4)) nextPC3
            (by change d3.get 10+4#32=_;rw [(after3 10 (by decide) (by decide) (by decide) (by decide)).trans h10,addr4])
            (Memory.block_access mem (off := start+4) (by decide) (by change start+4+1≤length;omega)) rfl
          change a4.pc=(if lower (g (start+4))=107 then 0x80003374#32 else 0x8000342c#32) at pc4
          have source4 (r : Reg) (h11 : r≠11) (h12 : r≠12) (h13 : r≠13) (h14 : r≠14) : a4.get r=c.get r :=
            (frame4 r h12 h13 h13).trans (after3 r h11 h12 h13 h14)
          by_cases h4 : lower (g (start+4))=107
          · have atGuard4 : a4.pc=0x80003374#32 := by simpa only [h4,ite_true] using pc4
            obtain ⟨d4,guard4,nextPC4,literalGuard4,guardFrame4,guardCSR4⟩ := HeadChunkedGuard5.contract B a4 ram (BitVec.ofNat 32 length-BitVec.ofNat 32 start)
              ((frame4 11 (by decide) (by decide) (by decide)).trans rem3) (HeadChunkedSpec.guard start length 5 hlen width (by decide)) atGuard4
            have after4 (r : Reg) (h11 : r≠11) (h12 : r≠12) (h13 : r≠13) (h14 : r≠14) : d4.get r=c.get r :=
              (guardFrame4 r h12).trans (source4 r h11 h12 h13 h14)
            have rem4 : d4.get 11=BitVec.ofNat 32 length-BitVec.ofNat 32 start := ((guardFrame4 11 (by decide))).trans ((frame4 11 (by decide) (by decide) (by decide)).trans rem3)
            have addr5 : (buf+BitVec.ofNat 32 start)+5#32=buf+BitVec.ofNat 32 (start+5) := by
              rw [BitVec.add_assoc,←BitVec.ofNat_add]
            obtain ⟨a5,read5,pc5,value5,literal5,frame5,csr5⟩ := HeadFoldLiteral.compare B img 101#8 (ram (buf+BitVec.ofNat 32 (start+5))) HeadFoldSites.chunk5
              d4 ram (buf+BitVec.ofNat 32 (start+5)) nextPC4
              (by change d4.get 10+5#32=_;rw [(after4 10 (by decide) (by decide) (by decide) (by decide)).trans h10,addr5])
              (Memory.block_access mem (off := start+5) (by decide) (by change start+5+1≤length;omega)) rfl
            change a5.pc=(if lower (g (start+5))=101 then 0x80003392#32 else 0x8000342c#32) at pc5
            have source5 (r : Reg) (h11 : r≠11) (h12 : r≠12) (h13 : r≠13) (h14 : r≠14) : a5.get r=c.get r :=
              (frame5 r h12 h13 h13).trans (after4 r h11 h12 h13 h14)
            by_cases h5 : lower (g (start+5))=101
            · have atGuard5 : a5.pc=0x80003392#32 := by simpa only [h5,ite_true] using pc5
              obtain ⟨d5,guard5,nextPC5,literalGuard5,guardFrame5,guardCSR5⟩ := HeadChunkedGuard6.contract B a5 ram (BitVec.ofNat 32 length-BitVec.ofNat 32 start)
                ((frame5 11 (by decide) (by decide) (by decide)).trans rem4) (HeadChunkedSpec.guard start length 6 hlen width (by decide)) atGuard5
              have after5 (r : Reg) (h11 : r≠11) (h12 : r≠12) (h13 : r≠13) (h14 : r≠14) : d5.get r=c.get r :=
                (guardFrame5 r h12).trans (source5 r h11 h12 h13 h14)
              have rem5 : d5.get 11=BitVec.ofNat 32 length-BitVec.ofNat 32 start := ((guardFrame5 11 (by decide))).trans ((frame5 11 (by decide) (by decide) (by decide)).trans rem4)
              have addr6 : (buf+BitVec.ofNat 32 start)+6#32=buf+BitVec.ofNat 32 (start+6) := by
                rw [BitVec.add_assoc,←BitVec.ofNat_add]
              obtain ⟨a6,read6,pc6,value6,literal6,frame6,csr6⟩ := HeadFoldLiteral.compare B img 100#8 (ram (buf+BitVec.ofNat 32 (start+6))) HeadFoldSites.chunk6
                d5 ram (buf+BitVec.ofNat 32 (start+6)) nextPC5
                (by change d5.get 10+6#32=_;rw [(after5 10 (by decide) (by decide) (by decide) (by decide)).trans h10,addr6])
                (Memory.block_access mem (off := start+6) (by decide) (by change start+6+1≤length;omega)) rfl
              change a6.pc=(if lower (g (start+6))=100 then 0x800033b0#32 else 0x8000342c#32) at pc6
              have source6 (r : Reg) (h10 : r≠10) (h11 : r≠11) (h12 : r≠12) (h13 : r≠13) (h14 : r≠14) : a6.get r=c.get r :=
                (frame6 r h10 h11 h11).trans (after5 r h11 h12 h13 h14)
              by_cases h6 : lower (g (start+6))=100
              · have full : HeadChunkedSpec.Prefix g start := ⟨h0,h1,h2,h3,h4,h5,h6⟩
                refine ⟨63,a6,by decide,by decide,((((((((((((read0.trans loadGuard).trans guard0).trans read1).trans guard1).trans read2).trans guard2).trans read3).trans guard3).trans read4).trans guard4).trans read5).trans guard5).trans read6,?_,source6,csr6.trans (guardCSR5.trans (csr5.trans (guardCSR4.trans (csr4.trans (guardCSR3.trans (csr3.trans (guardCSR2.trans (csr2.trans (guardCSR1.trans (csr1.trans (guardCSR0.trans (loadCSR.trans (csr0)))))))))))))⟩
                simpa [full,h6] using pc6
              · have bad : ¬HeadChunkedSpec.Prefix g start := by intro full;exact h6 full.2.2.2.2.2.2
                refine ⟨63,a6,by decide,by decide,((((((((((((read0.trans loadGuard).trans guard0).trans read1).trans guard1).trans read2).trans guard2).trans read3).trans guard3).trans read4).trans guard4).trans read5).trans guard5).trans read6,?_,?_,csr6.trans (guardCSR5.trans (csr5.trans (guardCSR4.trans (csr4.trans (guardCSR3.trans (csr3.trans (guardCSR2.trans (csr2.trans (guardCSR1.trans (csr1.trans (guardCSR0.trans (loadCSR.trans (csr0)))))))))))))⟩
                · simpa [bad,h6] using pc6
                · exact source6
            · have bad : ¬HeadChunkedSpec.Prefix g start := by intro full;exact h5 full.2.2.2.2.2.1
              refine ⟨54,a5,by decide,by decide,((((((((((read0.trans loadGuard).trans guard0).trans read1).trans guard1).trans read2).trans guard2).trans read3).trans guard3).trans read4).trans guard4).trans read5,?_,?_,csr5.trans (guardCSR4.trans (csr4.trans (guardCSR3.trans (csr3.trans (guardCSR2.trans (csr2.trans (guardCSR1.trans (csr1.trans (guardCSR0.trans (loadCSR.trans (csr0)))))))))))⟩
              · simpa [bad,h5] using pc5
              · intro r _ h11 h12 h13 h14;exact source5 r h11 h12 h13 h14
          · have bad : ¬HeadChunkedSpec.Prefix g start := by intro full;exact h4 full.2.2.2.2.1
            refine ⟨45,a4,by decide,by decide,((((((((read0.trans loadGuard).trans guard0).trans read1).trans guard1).trans read2).trans guard2).trans read3).trans guard3).trans read4,?_,?_,csr4.trans (guardCSR3.trans (csr3.trans (guardCSR2.trans (csr2.trans (guardCSR1.trans (csr1.trans (guardCSR0.trans (loadCSR.trans (csr0)))))))))⟩
            · simpa [bad,h4] using pc4
            · intro r _ h11 h12 h13 h14;exact source4 r h11 h12 h13 h14
        · have bad : ¬HeadChunkedSpec.Prefix g start := by intro full;exact h3 full.2.2.2.1
          refine ⟨36,a3,by decide,by decide,((((((read0.trans loadGuard).trans guard0).trans read1).trans guard1).trans read2).trans guard2).trans read3,?_,?_,csr3.trans (guardCSR2.trans (csr2.trans (guardCSR1.trans (csr1.trans (guardCSR0.trans (loadCSR.trans (csr0)))))))⟩
          · simpa [bad,h3] using pc3
          · intro r _ h11 h12 h13 h14;exact source3 r h11 h12 h13 h14
      · have bad : ¬HeadChunkedSpec.Prefix g start := by intro full;exact h2 full.2.2.1
        refine ⟨27,a2,by decide,by decide,((((read0.trans loadGuard).trans guard0).trans read1).trans guard1).trans read2,?_,?_,csr2.trans (guardCSR1.trans (csr1.trans (guardCSR0.trans (loadCSR.trans (csr0)))))⟩
        · simpa [bad,h2] using pc2
        · intro r _ h11 h12 h13 h14;exact source2 r h11 h12 h13 h14
    · have bad : ¬HeadChunkedSpec.Prefix g start := by intro full;exact h1 full.2.1
      refine ⟨18,a1,by decide,by decide,((read0.trans loadGuard).trans guard0).trans read1,?_,?_,csr1.trans (guardCSR0.trans (loadCSR.trans (csr0)))⟩
      · simpa [bad,h1] using pc1
      · intro r _ h11 h12 h13 h14;exact source1 r h11 h12 h13 h14
  · have bad : ¬HeadChunkedSpec.Prefix g start := by intro full;exact h0 full.1
    refine ⟨7,a0,by decide,by decide,read0,?_,?_,csr0⟩
    · simpa [bad,h0] using pc0
    · intro r _ h11 h12 h13 h14;exact source0 r h11 h12 h13 h14
end E5R.Thermostat.HeadChunkedCompare
