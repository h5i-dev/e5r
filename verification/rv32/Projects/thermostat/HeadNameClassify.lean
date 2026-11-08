import Projects.thermostat.HeadClName
import Projects.thermostat.HeadTeName
import Projects.thermostat.HeadClassSpec
namespace E5R.Thermostat.HeadNameClassify
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

def endpoint (kind : Nat) : Word := if kind=2 then 0x800031dc#32 else if kind=3 then 0x800032ae#32 else 0x800033b6#32

/-- Actual non-Host width/name dispatch selects the CL/TE value parser or the
    ordinary-header commit from the independent byte classification. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (ns ne length : Nat)
    (hp : c.pc=0x8000319a#32) (h2 : c.get 2=sp) (h24 : c.get 24=BitVec.ofNat 32 ns)
    (h14 : c.get 14=BitVec.ofNat 32 (ne-ns)) (h7 : c.get 7=14#32) (h20 : c.get 20=buf+BitVec.ofNat 32 ns)
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length) (hbuf : ramRead ram (sp+44#32) .w=buf)
    (ordered : ns≤ne ∧ ne≤length) (bound : length≤2048) (notHost : ne-ns≠4)
    (mem : Memory.Block B buf length) (stack : Memory.Block B sp 56) (aligned : sp.toNat%4=0)
    (clOutside : ∀ q : Fin 14, B.inRam (BitVec.ofNat 32 (0x80005de0+q.val)) 1=false)
    (teOutside : ∀ q : Fin 17, B.inRam (BitVec.ofNat 32 (0x80005dee+q.val)) 1=false) :
    let g := bytes ram buf
    ∃ n d, 1≤n ∧ n≤435 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=endpoint (classify g ns ne) ∧
      (classify g ns ne=2 → d.get 11=c.get 11) ∧
      (∀ r : Reg, r≠10 → r≠13 → r≠31 → r≠30 → r≠19 → r≠12 → r≠29 → r≠11 → r≠14 → r≠20 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  have noHost : eqCi g ns ne litHost=false := HeadClassSpec.different g ns ne litHost notHost
  obtain ⟨n,a,lo,hi,clName,pc,frame,csr⟩ := HeadClName.contract B c ram sp buf ns ne length hp h2 h24 h14 h7 hraw hbuf ordered bound mem stack aligned clOutside
  change a.pc=(if eqCi g ns ne litContentLength then 0x800031dc#32 else 0x8000326e#32) at pc
  by_cases cl : eqCi g ns ne litContentLength=true
  · have kind : classify g ns ne=2 := by simp only [classify,noHost,Bool.false_eq_true,ite_false,cl,ite_true]
    change ∃ n d, _
    refine ⟨n,a,lo,by omega,clName,?_,fun _ => frame 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),?_,csr⟩
    · change a.pc=endpoint (classify g ns ne)
      simpa only [endpoint,kind,cl,ite_true] using pc
    · intro r h10 h13 h31 h30 h19 h12 h29 _ _ _;exact frame r h10 h13 h31 h30 h19 h12 h29
  · have atTe : a.pc=0x8000326e#32 := by simpa [cl] using pc
    obtain ⟨k,d,klo,khi,teName,pc2,frame2,csr2⟩ := HeadTeName.contract B a ram sp buf ns ne length atTe
      ((frame 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2)
      ((frame 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h24)
      ((frame 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h14)
      ((frame 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h20)
      hraw ordered bound mem stack aligned teOutside
    have clFalse : eqCi g ns ne litContentLength=false := by cases h : eqCi g ns ne litContentLength <;> simp_all
    have endpointEq : endpoint (classify g ns ne)=
        (if eqCi g ns ne litTransferEncoding then 0x800032ae#32 else 0x800033b6#32) := by
      simp only [classify,noHost,clFalse,Bool.false_eq_true,ite_false]
      cases eqCi g ns ne litTransferEncoding <;> rfl
    have impossible : classify g ns ne≠2 := by
      simp only [classify,noHost,clFalse,Bool.false_eq_true,ite_false]
      cases eqCi g ns ne litTransferEncoding <;> decide
    change ∃ n d, _
    refine ⟨n+k,d,by omega,by omega,clName.trans teName,?_,fun h => False.elim (impossible h),?_,csr2.trans csr⟩
    · change d.pc=endpoint (classify g ns ne)
      rw [endpointEq];exact pc2
    · intro r h10 h13 h31 h30 h19 h12 h29 h11 h14 h20
      exact (frame2 r h10 h11 h13 h12 h14 h29 h20).trans (frame r h10 h13 h31 h30 h19 h12 h29)
end E5R.Thermostat.HeadNameClassify
