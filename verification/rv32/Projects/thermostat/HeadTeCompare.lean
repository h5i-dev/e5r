import Projects.thermostat.HeadTeSetup
import Projects.thermostat.HeadTeScan
namespace E5R.Thermostat.HeadTeCompare
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (start length : Nat)
    (hp : c.pc=0x80003274#32) (h2 : c.get 2=sp) (h24 : c.get 24=BitVec.ofNat 32 start)
    (h20 : c.get 20=buf+BitVec.ofNat 32 start)
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length)
    (width : start+17≤length) (bound : length≤2048) (mem : Memory.Block B buf length)
    (stack : Memory.Block B sp 56) (aligned : sp.toNat%4=0)
    (outside : ∀ q : Fin 17, B.inRam (BitVec.ofNat 32 (0x80005dee+q.val)) 1=false) :
    let g := bytes ram buf
    ∃ n d, 15≤n ∧ n≤243 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if eqCi g start (start+17) litTransferEncoding then 0x800032ae#32 else 0x800033b6#32) ∧
      (∀ r : Reg, r≠10 → r≠11 → r≠13 → r≠12 → r≠14 → r≠29 → r≠20 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,setup,pc,v10,v11,v13,frame,csr⟩ := HeadTeSetup.contract B c ram sp _ _ h2 h24 hraw stack aligned hp
  have a20 : a.get 20=buf+BitVec.ofNat 32 (start+0) := by
    simpa using (frame 20 (by decide) (by decide) (by decide)).trans h20
  have a13 : a.get 13=BitVec.ofNat 32 (0x80005dee+0) := v13
  obtain ⟨n,d,lo,hi,scan,pc2,frame2,csr2⟩ := HeadTeScan.contract B a ram buf start length 0 pc v11 v10 a20 a13 width bound (by decide) mem outside
  have spec : eqCi (bytes ram buf) start (start+17) litTransferEncoding=eqFrom (bytes ram buf) start litTransferEncoding 0 := by
    rw [eqCi,ite_eq_right (by change ¬(start+17<start ∨ start+17-start≠17);omega)]
  refine ⟨5+n,d,by omega,by omega,setup.trans scan,?_,?_,csr2.trans csr⟩
  · rw [spec];exact pc2
  · intro r h10 h11 h13 h12 h14 h29 h20
    exact (frame2 r h12 h14 h29 h10 h20 h13).trans (frame r h10 h11 h13)
end E5R.Thermostat.HeadTeCompare
