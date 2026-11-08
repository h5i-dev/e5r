import Projects.thermostat.HeadOwsTrimSetup
import Projects.thermostat.HeadOwsTrimBranch
import Projects.thermostat.HeadOwsTrimEmpty
import Projects.thermostat.HeadOwsBackScan
namespace E5R.Thermostat.HeadOwsTrim
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- Actual trim entry, empty-range branch and complete backward loop. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (start finish length : Nat)
    (hp : c.pc=0x800030c0#32) (h2 : c.get 2=sp) (h15 : c.get 15=BitVec.ofNat 32 start) (h26 : c.get 26=BitVec.ofNat 32 finish)
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length) (hbuf : ramRead ram (sp+44#32) .w=buf)
    (hi : start≤finish) (hn : finish≤length) (hlen : length≤2048) (mem : Memory.Block B buf length) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0) :
    let g := bytes ram buf
    ∃ n d, 2≤n ∧ n≤4+14*(finish-start) ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800030fa#32 ∧
      d.get 25=BitVec.ofNat 32 (trimEnd g start finish) ∧
      (∀ r : Reg, r≠10 → r≠13 → r≠12 → r≠25 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  obtain ⟨a,setup,pc,index,frame,csr⟩ := HeadOwsTrimSetup.contract B c ram (BitVec.ofNat 32 finish) h26 hp
  have test : taken .ltu (BitVec.ofNat 32 start) (BitVec.ofNat 32 finish)=decide (start<finish) := by
    simp only [taken,BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : start<2^32),Nat.mod_eq_of_lt (by omega : finish<2^32)]
  obtain ⟨b,branch,pc2,frame2,csr2⟩ := HeadOwsTrimBranch.contract B a ram (BitVec.ofNat 32 start) (BitVec.ofNat 32 finish) (decide (start<finish)) pc
    ((frame 15 (by decide)).trans h15) ((frame 26 (by decide)).trans h26) test
  have source (r : Reg) (h25 : r≠25) : b.get r=c.get r := (frame2 r).trans (frame r h25)
  by_cases more : start<finish
  · have atLoop : b.pc=0x800030d0#32 := by simpa only [more,decide_true,ite_true] using pc2
    obtain ⟨n,d,nlo,nhi,scan,endPC,result,frame3,csr3⟩ := HeadOwsBackScan.contract B b ram sp buf start finish length atLoop
      ((source 2 (by decide)).trans h2) ((source 15 (by decide)).trans h15) ((frame2 25).trans index) hraw hbuf more hn hlen mem stack ha
    exact ⟨2+n,d,by omega,by omega,(setup.trans branch).trans scan,endPC,result,
      fun r h10 h13 h12 h25 => (frame3 r h10 h13 h12 h25).trans (source r h25),csr3.trans (csr2.trans csr)⟩
  · have atEmpty : b.pc=0x800030c6#32 := by simpa only [more,decide_false,Bool.false_eq_true,ite_false] using pc2
    obtain ⟨d,finishTrace,endPC,result,frame3,csr3⟩ := HeadOwsTrimEmpty.contract B b ram (BitVec.ofNat 32 finish) ((source 26 (by decide)).trans h26) atEmpty
    refine ⟨4,d,by decide,by omega,(setup.trans branch).trans finishTrace,endPC,?_,
      fun r _ _ _ h25 => (frame3 r h25).trans (source r h25),csr3.trans (csr2.trans csr)⟩
    change d.get 25=BitVec.ofNat 32 (trimEnd g start finish)
    have same : start=finish := by omega
    have done : trimEnd g start finish=finish := by rw [same,trimEnd];simp
    rw [done];exact result
end E5R.Thermostat.HeadOwsTrim
