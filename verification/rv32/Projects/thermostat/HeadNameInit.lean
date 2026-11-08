import Projects.thermostat.HeadNameInitRaw
import Projects.thermostat.HeadNameState
namespace E5R.Thermostat.HeadNameInit
open E5R E5R.Thermostat

/-- Real name-parser entry establishes its cursor and every byte-range guard. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (start finish length : Nat)
    (hp : c.pc=0x80002fbc#32) (h2 : c.get 2=sp) (h24 : c.get 24=BitVec.ofNat 32 start)
    (h21 : c.get 21=BitVec.ofNat 32 (finish-start)) (h22 : c.get 22=0#32-BitVec.ofNat 32 length)
    (h25 : c.get 25=BitVec.ofNat 32 (finish-start)+0xffffffff#32) (hc : HeadNameClass.Constants c)
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length) (hbuf : ramRead ram (sp+44#32) .w=buf)
    (hnext : ramRead ram (sp+16#32) .w=buf+1#32) (hbefore : ramRead ram (sp+12#32) .w=BitVec.ofNat 32 length+0xffffffff#32)
    (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0) (hi : start<finish) (hn : finish≤length) (hlen : length≤2048) :
    ∃ d, Quiet.Steps B img 12 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002ff0#32 ∧
      HeadNameState.At d sp buf start start finish length ∧
      (∀ r : Reg, r≠10 → r≠14 → r≠15 → r≠13 → r≠20 → r≠12 → r≠31 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨d,trace,pc,ptr,count,last,relative,base,before,remaining,frame,csr⟩ := HeadNameInitRaw.contract B c ram sp
    (BitVec.ofNat 32 start) (BitVec.ofNat 32 (finish-start)) (0#32-BitVec.ofNat 32 length) (BitVec.ofNat 32 length) buf (buf+1#32) (BitVec.ofNat 32 length+0xffffffff#32)
    h2 h24 h21 h22 hraw hbuf hnext hbefore (HeadMethodMath.different start length (by omega) hlen) stack ha hp
  have inverseWord : BitVec.ofNat 32 (finish-start)+0xffffffff#32=BitVec.ofNat 32 (finish-start-1) := by
    simpa only [Nat.sub_zero,Nat.zero_add] using HeadTargetMath.remaining_next 0 (finish-start) (by omega)
  have remainingWord : (BitVec.ofNat 32 length+0xffffffff#32)-BitVec.ofNat 32 start=BitVec.ofNat 32 (length-start-1) := by
    have one : BitVec.ofNat 32 length+0xffffffff#32=BitVec.ofNat 32 (length-1) := by
      simpa only [Nat.sub_zero,Nat.zero_add] using HeadTargetMath.remaining_next 0 length (by omega)
    rw [one,show length-1=(length-start-1)+start by omega,BitVec.ofNat_add,BitVec.add_sub_cancel]
  refine ⟨d,trace,pc,?_,frame,csr⟩
  refine ⟨(frame 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2,base,?_,last.trans inverseWord,?_,?_,?_,remaining.trans remainingWord,?_⟩
  · simpa only [Nat.sub_self] using count
  · apply relative.trans
    rw [BitVec.zero_sub,BitVec.sub_eq_add_neg,BitVec.add_comm]
  · apply ptr.trans
    rw [BitVec.add_assoc,BitVec.add_comm 1#32,←BitVec.ofNat_add]
  · exact (frame 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (h25.trans inverseWord)
  · exact ⟨(frame 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc.x5,
      (frame 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc.x6,
      (frame 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc.x7,
      (frame 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc.x28,
      (frame 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc.x27⟩
end E5R.Thermostat.HeadNameInit
