import Projects.thermostat.I16Input
import Projects.thermostat.I16Exit
import Projects.thermostat.AppendPost
namespace E5R.Thermostat.I16AppendExit
open E5R E5R.Thermostat

theorem contract (B : Board) (original a z : Core) (before mid ram : Word → BitVec 8)
    (p ptr fmt obj dst : Word) (cap pos off len base size : Nat) (v : BitVec 16) (xs : List (BitVec 8))
    (h : I16Input.Data B before p ptr fmt obj dst cap pos v)
    (ha : I16Ready.Ready original a (p+144#32) fmt v off len)
    (hz : AppendPost.Post B a z mid ram (p+BitVec.ofNat 32 base) obj dst size cap pos xs)
    (hsp : original.get 2 = p+160#32) (hbound : base+size ≤ 144) (hfit : pos+xs.length ≤ cap)
    (hf : I16Input.ScratchFrame p before mid)
    (hs : ViewFrame.Region (I16Save.memory before (p+144#32) original) mid ((p+144#32)+8#32) 8) :
    ∃ d, DetSteps B img 4 ⟨z,ram⟩ ⟨d,ram⟩ ∧ AppendPost.Post B original d before ram p obj dst 160 cap pos xs := by
  have hr : ViewFrame.Region (I16Save.memory before (p+144#32) original) ram ((p+144#32)+8#32) 8 := by
    intro i
    apply Eq.trans _ (hs i)
    apply hz.frame
    · intro j
      have hi := i.isLt;have hj := j.isLt
      simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using Bytes.offset_ne p (144+8+i.val) (base+j.val) (by omega) (by omega) (by omega)
    · intro j
      have hi := i.isLt;have hj := j.isLt
      simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using Ne.symm (h.outputArena ⟨pos+j.val,by omega⟩ ⟨144+8+i.val,by omega⟩)
    · intro j
      have hi := i.isLt;have hj := j.isLt
      simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using Ne.symm (h.objectArena ⟨8+j.val,by omega⟩ ⟨144+8+i.val,by omega⟩)
  obtain ⟨d,td,hd,d10⟩ := I16Exit.contract B original a z before ram (p+144#32) fmt v off len ha hz.returned
    (by simpa only [BitVec.add_assoc,show 144#32+16#32 = 160#32 by decide +kernel] using hsp)
    (Memory.sub_block h.arena (off := 144) (m := 16) (by decide) (by decide)) (Memory.word_aligned p 36 h.arenaAligned) hr
  refine ⟨d,td,hd,d10.trans hz.result,hz.pointer,hz.capacity,hz.position,hz.written,?_,?_⟩
  · intro hn;exact False.elim (hn hfit)
  · intro x hx hbytes hobj
    apply Eq.trans (hz.frame x (by
      intro i
      have hi := i.isLt
      simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hx ⟨base+i.val,by omega⟩) hbytes hobj)
    apply hf
    intro i
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hx ⟨144+i.val,by have := i.isLt;omega⟩
end E5R.Thermostat.I16AppendExit
