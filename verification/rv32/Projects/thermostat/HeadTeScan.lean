import Projects.thermostat.HeadTeStep
import Projects.thermostat.HeadTeAdvance
namespace E5R.Thermostat.HeadTeScan
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- Complete actual ROM-backed Transfer-Encoding name loop. Slice checks follow
    from the byte-derived name span; no panic path is assumed away. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (buf : Word) (start length k : Nat)
    (hp : c.pc=0x80003284#32)
    (h11 : c.get 11=BitVec.ofNat 32 length-BitVec.ofNat 32 start)
    (h10 : c.get 10=BitVec.ofNat 32 (17-k))
    (h20 : c.get 20=buf+BitVec.ofNat 32 (start+k))
    (h13 : c.get 13=BitVec.ofNat 32 (0x80005dee+k))
    (width : start+17≤length) (bound : length≤2048) (hk : k<17)
    (mem : Memory.Block B buf length)
    (outside : ∀ q : Fin 17, B.inRam (BitVec.ofNat 32 (0x80005dee+q.val)) 1=false) :
    let g := bytes ram buf
    ∃ n d, 10≤n ∧ n≤14*(17-k) ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if eqFrom g start litTransferEncoding k then 0x800032ae#32 else 0x800033b6#32) ∧
      (∀ r : Reg, r≠12 → r≠14 → r≠29 → r≠10 → r≠20 → r≠13 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  have unfoldSpec : eqFrom g start litTransferEncoding k=
      (if lower (g (start+k))≠litTransferEncoding[k] then false else eqFrom g start litTransferEncoding (k+1)) := by
    rw [eqFrom]
    simp only [show litTransferEncoding.length=17 by rfl,hk,ite_true]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (show k<litTransferEncoding.length from hk),Option.getD_some]
    rfl
  obtain ⟨a,trace,pc,frame,csr⟩ := HeadTeStep.contract B c ram buf start length k hp h11 h10 h20 h13 width bound hk mem (outside ⟨k,hk⟩)
  change a.pc=(if lower (g (start+k))=litTransferEncoding[k] then _ else _) at pc
  by_cases same : lower (g (start+k))=litTransferEncoding[k]
  · have nextSpec : eqFrom g start litTransferEncoding k=eqFrom g start litTransferEncoding (k+1) := by
      rw [unfoldSpec];simp [same]
    have advancePc : a.pc=0x800032a6#32 := by simpa [same] using pc
    obtain ⟨d,advance,pc2,v10,v20,v13,frame2,csr2⟩ := HeadTeAdvance.contract B a ram buf start k advancePc
      ((frame 10 (by decide) (by decide) (by decide)).trans h10)
      ((frame 20 (by decide) (by decide) (by decide)).trans h20)
      ((frame 13 (by decide) (by decide) (by decide)).trans h13) hk
    have source (r : Reg) (h12 : r≠12) (h14 : r≠14) (h29 : r≠29) (h10 : r≠10) (h20 : r≠20) (h13 : r≠13) : d.get r=c.get r :=
      (frame2 r h10 h20 h13).trans (frame r h12 h14 h29)
    by_cases more : k+1<17
    · have recursivePc : d.pc=0x80003284#32 := by simpa [more] using pc2
      obtain ⟨rest,e,lo,hi,tail,result,frame3,csr3⟩ := contract B d ram buf start length (k+1) recursivePc
        ((source 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h11)
        v10 v20 v13 width bound more mem outside
      change ∃ n d, _
      rw [nextSpec]
      refine ⟨10+4+rest,e,by omega,by omega,(trace.trans advance).trans tail,result,?_,csr3.trans (csr2.trans csr)⟩
      intro r h12 h14 h29 h10 h20 h13
      exact (frame3 r h12 h14 h29 h10 h20 h13).trans (source r h12 h14 h29 h10 h20 h13)
    · have last : k+1=17 := by omega
      have endSpec : eqFrom g start litTransferEncoding (k+1)=true := by
        rw [eqFrom]
        simp only [show litTransferEncoding.length=17 by rfl,last,Nat.lt_irrefl,ite_false]
      change ∃ n d, _
      rw [nextSpec,endSpec]
      refine ⟨14,d,by omega,by omega,by simpa using trace.trans advance,?_,source,csr2.trans csr⟩
      simpa [more] using pc2
  · change ∃ n d, _
    have stopSpec : eqFrom g start litTransferEncoding k=false := by rw [unfoldSpec];simp [same]
    rw [stopSpec]
    refine ⟨10,a,by omega,by omega,trace,?_,fun r h12 h14 h29 _ _ _ => frame r h12 h14 h29,csr⟩
    simpa [same] using pc
termination_by 17-k
 decreasing_by omega
end E5R.Thermostat.HeadTeScan
