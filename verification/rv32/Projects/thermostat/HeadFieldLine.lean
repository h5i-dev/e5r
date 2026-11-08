import Projects.thermostat.HeadFieldsLine
import Projects.thermostat.HeadHeaderLine
import Projects.thermostat.HeadFieldsRegs
import Projects.thermostat.HeadFieldsMeta
import Projects.thermostat.HeadFieldLineSpec
namespace E5R.Thermostat.HeadFieldLine
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- Complete real line scanning, CRLF validation and name/value parsing at a
    stable header-loop entry. Typed fields are derived from receive bytes. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (i cap length minor : Nat) (f : Fields)
    (regs : HeadFieldsRegs.At c sp i length minor f) (metadata : HeadFieldsMeta.At ram sp length cap)
    (hi : i<cap) (hn : cap≤length) (hlen : length≤2048) (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) :
    let g := bytes ram (sp+516#32)
    ∃ n d after, 10≤n ∧ n≤44+78*(cap-i) ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      HeadFieldLineSpec.At d after sp i (HeadFieldLineSpec.next g i cap) ∧
      ViewFrame.Region ram after (sp+8#32) 5304 ∧ HeadFieldsMeta.At after sp length cap ∧
      (∀ r : Reg, r≠10 → r≠11 → r≠21 → r≠13 → r≠25 → r≠14 → r≠30 → r≠15 → r≠26 → r≠1 → r≠20 → r≠12 → r≠31 → r≠19 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram (sp+516#32)
  let j := lineEnd g i cap
  have lower : i≤j := scan_ge notEol g i cap
  have upper : j≤cap := scan_le notEol g i cap (by omega)
  have mem : Memory.Block B (sp+516#32) length := Memory.sub_block hm (off := 516) (by omega) (by omega)
  have stack : Memory.Block B sp 56 := by simpa only [BitVec.add_zero] using Memory.sub_block hm (off := 0) (m := 56) (by decide) (by decide)
  obtain ⟨n,a,nlo,nhi,line,pc,count,inverse,cursor,endIndex,status,frame,csr⟩ := HeadFieldsLine.contract B c ram sp (sp+516#32) i cap length
    regs.pc regs.stack regs.position regs.lf regs.cr metadata.limit metadata.raw metadata.buffer hi hn hlen mem stack ha
  change a.pc=HeadFieldsLine.endpoint g i j cap at pc
  have position : a.get 24=BitVec.ofNat 32 i := (frame 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans regs.position
  have stackA : a.get 2=sp := (frame 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans regs.stack
  by_cases more : lineTerm g j cap=1
  · have result : HeadFieldLineSpec.next g i cap=.more := by
      change (if lineTerm g j cap=1 then _ else _)=_
      rw [ite_eq_left more]
    refine ⟨n,a,ram,nlo,by omega,line,?_,fun _ => rfl,metadata,fun r h10 h11 h21 h13 h25 h14 h30 h15 h26 h1 _ _ _ _ => frame r h10 h11 h21 h13 h25 h14 h30 h15 h26 h1,csr⟩
    change HeadFieldLineSpec.At a ram sp i (HeadFieldLineSpec.next g i cap)
    rw [result]
    change a.pc=0x800033ea#32
    simpa only [HeadFieldsLine.endpoint,more,ite_true] using pc
  · by_cases bad : lineTerm g j cap=2
    · have result : HeadFieldLineSpec.next g i cap=.bad 400 := by
        change (if lineTerm g j cap=1 then _ else if lineTerm g j cap=2 then _ else _)=_
        rw [ite_eq_right more,ite_eq_left bad]
      refine ⟨n,a,ram,nlo,by omega,line,?_,fun _ => rfl,metadata,fun r h10 h11 h21 h13 h25 h14 h30 h15 h26 h1 _ _ _ _ => frame r h10 h11 h21 h13 h25 h14 h30 h15 h26 h1,csr⟩
      change HeadFieldLineSpec.At a ram sp i (HeadFieldLineSpec.next g i cap)
      rw [result]
      exact ⟨by simpa [HeadFieldsLine.endpoint,more,bad] using pc,status more⟩
    · have term : lineTerm g j cap=0 := (HeadFieldLineSpec.term_cases g j cap).resolve_right (by intro h;rcases h with h|h;exact more h;exact bad h)
      by_cases empty : j=i
      · have result : HeadFieldLineSpec.next g i cap=.done (j+2) := by
          change (if lineTerm g j cap=1 then _ else if lineTerm g j cap=2 then _ else if j=i then _ else _)=_
          rw [ite_eq_right more,ite_eq_right bad,ite_eq_left empty]
        refine ⟨n,a,ram,nlo,by omega,line,?_,fun _ => rfl,metadata,fun r h10 h11 h21 h13 h25 h14 h30 h15 h26 h1 _ _ _ _ => frame r h10 h11 h21 h13 h25 h14 h30 h15 h26 h1,csr⟩
        change HeadFieldLineSpec.At a ram sp i (HeadFieldLineSpec.next g i cap)
        rw [result]
        exact ⟨by rw [HeadFieldsLine.endpoint,ite_eq_right more,ite_eq_right bad,ite_eq_left empty] at pc;exact pc,by simpa only [Nat.add_sub_cancel,empty] using position⟩
      · have atName : a.pc=0x80002fbc#32 := by simpa only [HeadFieldsLine.endpoint,more,bad,empty,ite_false] using pc
        have constants : HeadNameClass.Constants a := ⟨
          (frame 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans regs.tcharMin,
          (frame 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans regs.digitMin,
          (frame 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans regs.maskWidth,
          (frame 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans regs.colon,
          (frame 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans regs.upperEnd⟩
        obtain ⟨m,d,after,mlo,mhi,parse,result,effect,frame2,csr2⟩ := HeadHeaderLine.contract B a ram sp i j length atName (status more) stackA position count
          ((frame 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans regs.negLength) inverse constants
          metadata.raw metadata.buffer metadata.next metadata.before metadata.mask (endIndex term) mem stack ha (by omega) (by omega) hlen
        have next : HeadFieldLineSpec.next g i cap=.header j (headerLine g i j) := by
          change (if lineTerm g j cap=1 then _ else if lineTerm g j cap=2 then _ else if j=i then _ else _)=_
          rw [ite_eq_right more,ite_eq_right bad,ite_eq_right empty]
        let k := scan isTchar g i j
        refine ⟨n+m,d,after,by omega,by omega,line.trans parse,?_,HeadNameMemory.region ram after sp k 8 5304 effect (by decide) (by decide),HeadFieldsMeta.preserve metadata effect,?_,csr2.trans csr⟩
        · change HeadFieldLineSpec.At d after sp i (HeadFieldLineSpec.next g i cap)
          rw [next]
          exact ⟨result,(frame2 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans cursor,
            (frame2 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans count,
            (frame2 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans position,
            (frame2 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (endIndex term)⟩
        · intro r h10 h11 h21 h13 h25 h14 h30 h15 h26 h1 h20 h12 h31 h19
          exact (frame2 r h10 h14 h15 h13 h20 h12 h31 h30 h19 h25).trans (frame r h10 h11 h21 h13 h25 h14 h30 h15 h26 h1)
end E5R.Thermostat.HeadFieldLine
