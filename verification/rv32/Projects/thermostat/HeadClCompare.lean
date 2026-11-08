import Projects.thermostat.HeadClSetup
import Projects.thermostat.HeadClScan
namespace E5R.Thermostat.HeadClCompare
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (start length : Nat)
    (hp : c.pc=0x8000319e#32) (h2 : c.get 2=sp) (h24 : c.get 24=BitVec.ofNat 32 start) (h7 : c.get 7=14#32)
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length) (hbuf : ramRead ram (sp+44#32) .w=buf)
    (width : start+14≤length) (bound : length≤2048) (mem : Memory.Block B buf length)
    (stack : Memory.Block B sp 56) (aligned : sp.toNat%4=0)
    (outside : ∀ q : Fin 14, B.inRam (BitVec.ofNat 32 (0x80005de0+q.val)) 1=false) :
    let g := bytes ram buf
    ∃ n d, 16≤n ∧ n≤189 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if eqCi g start (start+14) litContentLength then 0x800031dc#32 else 0x8000326e#32) ∧
      (∀ r : Reg, r≠10 → r≠13 → r≠31 → r≠30 → r≠19 → r≠12 → r≠29 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,setup,pc,v10,v13,v31,v30,frame,csr⟩ := HeadClSetup.contract B c ram sp _ _ buf h2 h24 hraw hbuf stack aligned hp
  have a7 : a.get 7=14#32 := (frame 7 (by decide) (by decide) (by decide) (by decide)).trans h7
  have a31 : a.get 31=buf+BitVec.ofNat 32 (start+0) := by simpa using v31
  have a30 : a.get 30=BitVec.ofNat 32 (0x80005de0+0) := v30
  obtain ⟨n,d,lo,hi,scan,pc2,frame2,csr2⟩ := HeadClScan.contract B a ram buf start length 0 pc a7 v13 v10 a31 a30 width bound (by decide) mem outside
  have spec : eqCi (bytes ram buf) start (start+14) litContentLength=eqFrom (bytes ram buf) start litContentLength 0 := by
    rw [eqCi,ite_eq_right (by change ¬(start+14<start ∨ start+14-start≠14);omega)]
  refine ⟨7+n,d,by omega,by omega,setup.trans scan,?_,?_,csr2.trans csr⟩
  · rw [spec];exact pc2
  · intro r h10 h13 h31 h30 h19 h12 h29
    exact (frame2 r h19 h12 h29 h10 h31 h30).trans (frame r h10 h13 h31 h30)
end E5R.Thermostat.HeadClCompare
