import Projects.thermostat.HeadClWidth
import Projects.thermostat.HeadClCompare
namespace E5R.Thermostat.HeadClName
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (ns ne length : Nat)
    (hp : c.pc=0x8000319a#32) (h2 : c.get 2=sp) (h24 : c.get 24=BitVec.ofNat 32 ns)
    (h14 : c.get 14=BitVec.ofNat 32 (ne-ns)) (h7 : c.get 7=14#32)
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length) (hbuf : ramRead ram (sp+44#32) .w=buf)
    (ordered : ns≤ne ∧ ne≤length) (bound : length≤2048) (mem : Memory.Block B buf length)
    (stack : Memory.Block B sp 56) (aligned : sp.toNat%4=0)
    (outside : ∀ q : Fin 14, B.inRam (BitVec.ofNat 32 (0x80005de0+q.val)) 1=false) :
    let g := bytes ram buf
    ∃ n d, 1≤n ∧ n≤190 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if eqCi g ns ne litContentLength then 0x800031dc#32 else 0x8000326e#32) ∧
      (∀ r : Reg, r≠10 → r≠13 → r≠31 → r≠30 → r≠19 → r≠12 → r≠29 → d.get r=c.get r) ∧ d.sameCsr c := by
  have test : taken .ne (BitVec.ofNat 32 (ne-ns)) 14#32=decide (ne-ns≠14) :=
    Usize.ne _ _ (by omega) (by decide)
  obtain ⟨a,branch,pc,frame,csr⟩ := HeadClWidth.contract B c ram _ _ _ hp h14 h7 test
  by_cases wrongWidth : ne-ns≠14
  · have noMatch : eqCi (bytes ram buf) ns ne litContentLength=false := by
      change (if ne<ns ∨ ne-ns≠14 then false else eqFrom (bytes ram buf) ns litContentLength 0)=false
      rw [ite_eq_left (Or.inr wrongWidth)]
    change ∃ n d, _
    rw [noMatch]
    refine ⟨1,a,by decide,by decide,branch,?_,fun r _ _ _ _ _ _ _ => frame r,csr⟩
    simpa [wrongWidth] using pc
  · have exactWidth : ne=ns+14 := by omega
    have atCompare : a.pc=0x8000319e#32 := by simpa [wrongWidth] using pc
    obtain ⟨n,d,lo,hi,compare,result,frame2,csr2⟩ := HeadClCompare.contract B a ram sp buf ns length atCompare
      ((frame 2).trans h2) ((frame 24).trans h24) ((frame 7).trans h7) hraw hbuf
      (by omega) bound mem stack aligned outside
    change ∃ n d, _
    rw [exactWidth]
    exact ⟨1+n,d,by omega,by omega,branch.trans compare,result,
      fun r h10 h13 h31 h30 h19 h12 h29 => (frame2 r h10 h13 h31 h30 h19 h12 h29).trans (frame r),csr2.trans csr⟩
end E5R.Thermostat.HeadClName
