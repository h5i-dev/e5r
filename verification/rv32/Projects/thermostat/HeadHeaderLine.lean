import Projects.thermostat.HeadName
import Projects.thermostat.HeadNameSpec
import Projects.thermostat.HeadHeaderValue
import Projects.thermostat.HeadHeaderLineView
import Projects.thermostat.HeadFieldCongr
namespace E5R.Thermostat.HeadHeaderLine
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- Complete actual nonempty header_line at the real parser layout. Its typed
    name/value spans or 400 come from the original receive bytes. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (start finish length : Nat)
    (hp : c.pc=0x80002fbc#32) (h1 : c.get 1=400#32) (h2 : c.get 2=sp) (h24 : c.get 24=BitVec.ofNat 32 start)
    (h21 : c.get 21=BitVec.ofNat 32 (finish-start)) (h22 : c.get 22=0#32-BitVec.ofNat 32 length)
    (h25 : c.get 25=BitVec.ofNat 32 (finish-start)+0xffffffff#32) (hc : HeadNameClass.Constants c)
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length) (hbuf : ramRead ram (sp+44#32) .w=(sp+516#32))
    (hnext : ramRead ram (sp+16#32) .w=(sp+516#32)+1#32) (hbefore : ramRead ram (sp+12#32) .w=BitVec.ofNat 32 length+0xffffffff#32)
    (hmask : ramRead ram (sp+32#32) .w=9409#32) (h26 : c.get 26=BitVec.ofNat 32 finish)
    (mem : Memory.Block B (sp+516#32) length) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0) (hi : start<finish) (hn : finish≤length) (hlen : length≤2048) :
    let g := bytes ram (sp+516#32)
    let k := scan isTchar g start finish
    ∃ n d after, 12<n ∧ n≤26+64*(finish-start) ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      HeadHeaderLineView.At d after sp (sp+516#32) start finish (headerLine g start finish) ∧
      (after=ram ∨ after=ramWrite ram (sp+4#32) (BitVec.ofNat 32 k) .w) ∧
      (∀ r : Reg, r≠10 → r≠14 → r≠15 → r≠13 → r≠20 → r≠12 → r≠31 → r≠30 → r≠19 → r≠25 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram (sp+516#32)
  let k := scan isTchar g start finish
  obtain ⟨n,a,after,nlo,nhi,name,pc,effect,ready,frame,csr⟩ := HeadName.contract B c ram sp (sp+516#32) start finish length hp h2 h24 h21 h22 h25 hc hraw hbuf hnext hbefore hmask h26 mem stack ha hi hn hlen
  change a.pc=(if HeadNameChecked.good g start k finish then 0x80003068#32 else 0x8000342c#32) at pc
  have status : a.get 1=400#32 := (frame 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h1
  by_cases accepted : HeadNameChecked.good g start k finish
  · obtain ⟨nameEnd,state⟩ := ready accepted
    let h := bytes after (sp+516#32)
    have rx := HeadNameMemory.region ram after sp k 516 2048 effect (by decide) (by decide)
    have agree (i : Nat) (bound : i<finish) : g i=h i := by
      exact congrArg BitVec.toNat (rx ⟨i,by omega⟩).symm
    have newName : scan isTchar h start finish=k := (scan_congr isTchar g h start finish agree).symm
    have newGood : HeadNameChecked.good h start k finish :=
      ⟨accepted.1,accepted.2.1,(agree k accepted.2.1).symm.trans accepted.2.2⟩
    have spec : headerLine g start finish=
        (if !allIn isFieldByte h (k+1) finish then HdrLine.bad 400 else
          let vs := scan isOws h (k+1) finish; HdrLine.ok k vs (trimEnd h vs finish)) := by
      rw [HeadFieldCongr.header_congr g h start finish agree]
      have parsed := HeadNameSpec.accepted h start finish (by rw [newName];exact newGood)
      simpa only [newName] using parsed
    have atValue : a.pc=0x80003068#32 := by simpa only [accepted,ite_true] using pc
    have a26 : a.get 26=BitVec.ofNat 32 finish := (frame 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h26
    obtain ⟨m,d,mlo,mhi,value,pc2,spans,frame2,csr2⟩ := HeadHeaderValue.contract B a after sp (sp+516#32) start k finish length atValue state a26 nameEnd
      ((HeadNameMemory.word_frame ram after sp k 48 effect (by decide) (by decide)).trans hraw)
      ((HeadNameMemory.word_frame ram after sp k 44 effect (by decide) (by decide)).trans hbuf) accepted.2.1 hn hlen stack ha mem
    have finalFrame (r : Reg) (h10 : r≠10) (h14 : r≠14) (h15 : r≠15) (h13 : r≠13) (h20 : r≠20) (h12 : r≠12) (h31 : r≠31) (h30 : r≠30) (h19 : r≠19) (h25 : r≠25) : d.get r=c.get r :=
      (frame2 r h15 h13 h30 h12 h10 h31 h25).trans (frame r h10 h14 h15 h13 h20 h12 h31 h30 h19 h25)
    have earlier : start<k := accepted.1
    have spanBound : finish-(k+1)≤finish-start := by omega
    refine ⟨n+m,d,after,by omega,by omega,name.trans value,?_,effect,finalFrame,csr2.trans csr⟩
    change HeadHeaderLineView.At d after sp (sp+516#32) start finish (headerLine g start finish)
    rw [spec]
    change d.pc=(if allIn isFieldByte h (k+1) finish then 0x800030fa#32 else 0x8000342c#32) at pc2
    cases valid : allIn isFieldByte h (k+1) finish with
    | false =>
      change d.pc=0x8000342c#32 ∧ d.get 1=BitVec.ofNat 32 400
      exact ⟨by simpa only [valid,Bool.false_eq_true,ite_false] using pc2,
        (frame2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans status⟩
    | true =>
      obtain ⟨valueStart,valueEnd⟩ := spans valid
      have startBound : k+1≤scan isOws h (k+1) finish := scan_ge isOws h (k+1) finish
      have endBound : scan isOws h (k+1) finish≤finish := scan_le isOws h (k+1) finish (by have := accepted.2.1;omega)
      exact ⟨by simpa only [valid,ite_true] using pc2,nameEnd,
        (frame2 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans state.count,valueStart,valueEnd,
        (frame2 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans state.base,
        accepted.1,by omega,trimEnd_ge h _ _ endBound,trimEnd_le h _ _⟩
  · have bad := HeadNameSpec.reject g start finish hi accepted
    refine ⟨n,a,after,nlo,by omega,name,?_,effect,frame,csr⟩
    change HeadHeaderLineView.At a after sp (sp+516#32) start finish (headerLine g start finish)
    rw [bad]
    exact ⟨by simpa only [accepted,ite_false] using pc,status⟩
end E5R.Thermostat.HeadHeaderLine
