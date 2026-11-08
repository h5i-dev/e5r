import Projects.thermostat.HeadTeWidthSetup
import Projects.thermostat.HeadTeWidthBranch
import Projects.thermostat.HeadTeCompare
namespace E5R.Thermostat.HeadTeName
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- Actual TE width dispatch and ROM-backed name comparison, without a
    postulated typed header name. Non-seventeen-byte names bypass all reads. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (ns ne length : Nat)
    (hp : c.pc=0x8000326e#32) (h2 : c.get 2=sp) (h24 : c.get 24=BitVec.ofNat 32 ns)
    (h14 : c.get 14=BitVec.ofNat 32 (ne-ns)) (h20 : c.get 20=buf+BitVec.ofNat 32 ns)
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length)
    (ordered : ns≤ne ∧ ne≤length) (bound : length≤2048) (mem : Memory.Block B buf length)
    (stack : Memory.Block B sp 56) (aligned : sp.toNat%4=0)
    (outside : ∀ q : Fin 17, B.inRam (BitVec.ofNat 32 (0x80005dee+q.val)) 1=false) :
    let g := bytes ram buf
    ∃ n d, 2≤n ∧ n≤245 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if eqCi g ns ne litTransferEncoding then 0x800032ae#32 else 0x800033b6#32) ∧
      (∀ r : Reg, r≠10 → r≠11 → r≠13 → r≠12 → r≠14 → r≠29 → r≠20 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,setup,pc,v10,frame,csr⟩ := HeadTeWidthSetup.contract B c ram hp
  have test : taken .ne (BitVec.ofNat 32 (ne-ns)) 17#32=decide (ne-ns≠17) :=
    Usize.ne _ _ (by omega) (by decide)
  obtain ⟨b,branch,pc2,frame2,csr2⟩ := HeadTeWidthBranch.contract B a ram _ _ _ pc
    ((frame 14 (by decide)).trans h14) v10 test
  have source (r : Reg) (h10 : r≠10) : b.get r=c.get r := (frame2 r).trans (frame r h10)
  by_cases wrongWidth : ne-ns≠17
  · have noMatch : eqCi (bytes ram buf) ns ne litTransferEncoding=false := by
      change (if ne<ns ∨ ne-ns≠17 then false else eqFrom (bytes ram buf) ns litTransferEncoding 0)=false
      rw [ite_eq_left (Or.inr wrongWidth)]
    change ∃ n d, _
    rw [noMatch]
    refine ⟨2,b,by decide,by decide,by simpa using setup.trans branch,?_,fun r h10 _ _ _ _ _ _ => source r h10,csr2.trans csr⟩
    simpa [wrongWidth] using pc2
  · have exactWidth : ne=ns+17 := by omega
    have atCompare : b.pc=0x80003274#32 := by simpa [wrongWidth] using pc2
    obtain ⟨n,d,lo,hi,compare,result,frame3,csr3⟩ := HeadTeCompare.contract B b ram sp buf ns length atCompare
      ((source 2 (by decide)).trans h2) ((source 24 (by decide)).trans h24) ((source 20 (by decide)).trans h20)
      hraw (by omega) bound mem stack aligned outside
    change ∃ n d, _
    rw [exactWidth]
    refine ⟨2+n,d,by omega,by omega,(setup.trans branch).trans compare,result,?_,csr3.trans (csr2.trans csr)⟩
    intro r h10 h11 h13 h12 h14 h29 h20
    exact (frame3 r h10 h11 h13 h12 h14 h29 h20).trans (source r h10)
end E5R.Thermostat.HeadTeName
