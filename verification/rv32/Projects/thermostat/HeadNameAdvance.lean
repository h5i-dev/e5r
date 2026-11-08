import Projects.thermostat.HeadNameState
import Projects.thermostat.HeadNameAdvanceRaw
namespace E5R.Thermostat.HeadNameAdvance
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (start pos finish length : Nat)
    (hp : c.pc=0x80002fe0#32) (state : HeadNameState.At c sp buf start pos finish length)
    (hs : start≤pos) (hi : pos+1<finish) (hn : finish≤length) (hlen : length≤2048) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002ff0#32 ∧
      HeadNameState.At d sp buf start (pos+1) finish length ∧
      (∀ r : Reg, r≠14 → r≠30 → r≠10 → r≠25 → r≠31 → d.get r=c.get r) ∧ d.sameCsr c := by
  have countNext : BitVec.ofNat 32 (pos-start)+1#32=BitVec.ofNat 32 (pos+1-start) := by
    rw [←BitVec.ofNat_add];congr 1;omega
  have guard : taken .eq ((BitVec.ofNat 32 start-BitVec.ofNat 32 length)+(BitVec.ofNat 32 (pos-start)+1#32)) (0 : Word)=false := by
    rw [countNext]
    apply HeadFieldsMath.guard start (pos+1-start) length (by omega) hlen
  obtain ⟨d,trace,pc,count,relative,ptr,inverse,remaining,frame,csr⟩ := HeadNameAdvanceRaw.contract B c ram
    (BitVec.ofNat 32 (pos-start)) (BitVec.ofNat 32 start-BitVec.ofNat 32 length)
    (buf+BitVec.ofNat 32 (pos+1)) (BitVec.ofNat 32 (finish-pos-1)) (BitVec.ofNat 32 (length-pos-1))
    state.count state.relative state.ptr state.inverse state.remaining guard hp
  refine ⟨d,trace,pc,?_,frame,csr⟩
  refine ⟨(frame 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans state.stack,
    (frame 20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans state.base,count.trans countNext,
    (frame 15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans state.last,
    (frame 13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans state.relative,
    ptr.trans (HeadFieldsMath.pointer_next buf (pos+1)),?_,?_,?_⟩
  · simpa only [Nat.sub_sub,Nat.add_assoc] using inverse.trans (HeadTargetMath.remaining_next (pos+1) finish hi)
  · simpa only [Nat.sub_sub,Nat.add_assoc] using remaining.trans (HeadTargetMath.remaining_next (pos+1) length (by omega))
  · exact ⟨(frame 5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans state.constants.x5,
      (frame 6 (by decide) (by decide) (by decide) (by decide) (by decide)).trans state.constants.x6,
      (frame 7 (by decide) (by decide) (by decide) (by decide) (by decide)).trans state.constants.x7,
      (frame 28 (by decide) (by decide) (by decide) (by decide) (by decide)).trans state.constants.x28,
      (frame 27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans state.constants.x27⟩
end E5R.Thermostat.HeadNameAdvance
