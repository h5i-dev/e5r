import Projects.thermostat.HeadClStep
import Projects.thermostat.HeadClAdvance
namespace E5R.Thermostat.HeadClScan
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- Complete actual ROM-backed Content-Length name loop. Slice checks follow
    from the byte-derived name span; no panic path is assumed away. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (buf : Word) (start length k : Nat)
    (hp : c.pc=0x800031b2#32) (h7 : c.get 7=14#32)
    (h13 : c.get 13=BitVec.ofNat 32 length-BitVec.ofNat 32 start)
    (h10 : c.get 10=BitVec.ofNat 32 (14-k))
    (h31 : c.get 31=buf+BitVec.ofNat 32 (start+k))
    (h30 : c.get 30=BitVec.ofNat 32 (0x80005de0+k))
    (width : start+14≤length) (bound : length≤2048) (hk : k<14)
    (mem : Memory.Block B buf length)
    (outside : ∀ q : Fin 14, B.inRam (BitVec.ofNat 32 (0x80005de0+q.val)) 1=false) :
    let g := bytes ram buf
    ∃ n d, 9≤n ∧ n≤13*(14-k) ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if eqFrom g start litContentLength k then 0x800031dc#32 else 0x8000326e#32) ∧
      (∀ r : Reg, r≠19 → r≠12 → r≠29 → r≠10 → r≠31 → r≠30 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  have unfoldSpec : eqFrom g start litContentLength k=
      (if lower (g (start+k))≠litContentLength[k] then false else eqFrom g start litContentLength (k+1)) := by
    rw [eqFrom]
    simp only [show litContentLength.length=14 by rfl,hk,ite_true]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (show k<litContentLength.length from hk),Option.getD_some]
    rfl
  obtain ⟨a,trace,pc,frame,csr⟩ := HeadClStep.contract B c ram buf start length k hp h7 h13 h10 h31 h30 width bound hk mem (outside ⟨k,hk⟩)
  change a.pc=(if lower (g (start+k))=litContentLength[k] then _ else _) at pc
  by_cases same : lower (g (start+k))=litContentLength[k]
  · have nextSpec : eqFrom g start litContentLength k=eqFrom g start litContentLength (k+1) := by
      rw [unfoldSpec];simp [same]
    have advancePc : a.pc=0x800031d4#32 := by simpa [same] using pc
    obtain ⟨d,advance,pc2,v10,v31,v30,frame2,csr2⟩ := HeadClAdvance.contract B a ram buf start k advancePc
      ((frame 10 (by decide) (by decide) (by decide)).trans h10)
      ((frame 31 (by decide) (by decide) (by decide)).trans h31)
      ((frame 30 (by decide) (by decide) (by decide)).trans h30) hk
    have source (r : Reg) (h19 : r≠19) (h12 : r≠12) (h29 : r≠29) (h10 : r≠10) (h31 : r≠31) (h30 : r≠30) : d.get r=c.get r :=
      (frame2 r h10 h31 h30).trans (frame r h19 h12 h29)
    by_cases more : k+1<14
    · have recursivePc : d.pc=0x800031b2#32 := by simpa [more] using pc2
      obtain ⟨rest,e,lo,hi,tail,result,frame3,csr3⟩ := contract B d ram buf start length (k+1) recursivePc
        ((source 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h7)
        ((source 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h13)
        v10 v31 v30 width bound more mem outside
      change ∃ n d, _
      rw [nextSpec]
      refine ⟨9+4+rest,e,by omega,by omega,(trace.trans advance).trans tail,result,?_,csr3.trans (csr2.trans csr)⟩
      intro r h19 h12 h29 h10 h31 h30
      exact (frame3 r h19 h12 h29 h10 h31 h30).trans (source r h19 h12 h29 h10 h31 h30)
    · have last : k+1=14 := by omega
      have endSpec : eqFrom g start litContentLength (k+1)=true := by
        rw [eqFrom]
        simp only [show litContentLength.length=14 by rfl,last,Nat.lt_irrefl,ite_false]
      change ∃ n d, _
      rw [nextSpec,endSpec]
      refine ⟨13,d,by omega,by omega,by simpa using trace.trans advance,?_,source,csr2.trans csr⟩
      simpa [more] using pc2
  · change ∃ n d, _
    have stopSpec : eqFrom g start litContentLength k=false := by rw [unfoldSpec];simp [same]
    rw [stopSpec]
    refine ⟨9,a,by omega,by omega,trace,?_,fun r h19 h12 h29 _ _ _ => frame r h19 h12 h29,csr⟩
    simpa [same] using pc
termination_by 14-k
 decreasing_by omega
end E5R.Thermostat.HeadClScan
