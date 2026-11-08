import Projects.thermostat.HeadNameState
import Projects.thermostat.HeadNameLoad
namespace E5R.Thermostat.HeadNameStep
open E5R E5R.Thermostat HttpRequestSpec

/-- Real address calculation, byte load and complete character classifier. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (start pos finish length : Nat)
    (hp : c.pc=0x80002ff0#32) (state : HeadNameState.At c sp buf start pos finish length)
    (hmask : ramRead ram (sp+32#32) .w=9409#32) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0)
    (hs : start≤pos) (hi : pos<finish) (hn : finish≤length) (hlen : length≤2048) (mem : Memory.Block B buf length) :
    let b := ram (buf+BitVec.ofNat 32 pos)
    ∃ n d, 3≤n ∧ n≤19 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if 58≤b.toNat ∧ b.toNat<65 then 0x80003056#32 else if isTchar b.toNat ∧ pos+1≠finish then 0x80002fe0#32 else 0x8000342c#32) ∧
      HeadNameState.At d sp buf start pos finish length ∧
      (d.pc=0x80003056#32 → d.get 30=BitVec.ofNat 32 b.toNat) ∧
      (∀ r : Reg, r≠30 → r≠19 → r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let b := ram (buf+BitVec.ofNat 32 pos)
  have addr : (buf+BitVec.ofNat 32 start)+BitVec.ofNat 32 (pos-start)=buf+BitVec.ofNat 32 pos := by
    rw [BitVec.add_assoc,HeadNameState.index start pos hs]
  obtain ⟨a,load,pc,value,frame,csr⟩ := HeadNameLoad.contract B c ram (buf+BitVec.ofNat 32 start) (BitVec.ofNat 32 (pos-start)) b
    state.base state.count (by rw [addr];exact Memory.block_access mem (off := pos) (by decide) (by change pos+1≤length;omega)) (by rw [addr]) hp
  have aState : HeadNameState.At a sp buf start pos finish length := HeadNameState.preserve state (fun r h30 _ _ => frame r h30)
  obtain ⟨n,d,nlo,nhi,classify,pc2,colon,frame2,csr2⟩ := HeadNameClass.contract B a ram sp (BitVec.ofNat 32 (finish-start-1)) (BitVec.ofNat 32 (pos-start)) b
    pc value aState.last aState.count aState.stack aState.constants hmask stack ha
  refine ⟨2+n,d,by omega,by omega,load.trans classify,?_,HeadNameState.preserve aState frame2,colon,
    fun r h30 h19 h12 => (frame2 r h30 h19 h12).trans (frame r h30),csr2.trans csr⟩
  simpa only [HeadNameState.last_test start pos finish hs hi (by omega),decide_eq_false_iff_not] using pc2
end E5R.Thermostat.HeadNameStep
