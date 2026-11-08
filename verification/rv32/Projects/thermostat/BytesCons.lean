import Projects.thermostat.Bytes
namespace E5R.Thermostat.Bytes
open E5R E5R.Thermostat

theorem cons_of_block {B ram dst cap pos xs b} (hm : Memory.Block B dst cap) (hc : cap < 2^32)
    (hf : pos+1+xs.length ≤ cap) (hb : ram (dst+BitVec.ofNat 32 pos) = b)
    (ht : Span B ram (dst+BitVec.ofNat 32 (pos+1)) xs) :
    Span B ram (dst+BitVec.ofNat 32 pos) (b::xs) := by
  apply of_block
  · apply Memory.sub_block hm (off := pos) (m := (b::xs).length) (by simp) (by simp only [List.length_cons];omega)
  · simp only [List.length_cons];omega
  · intro i
    change ram ((dst+BitVec.ofNat 32 pos)+BitVec.ofNat 32 i.val) = (b::xs)[i.val]
    by_cases hi : i.val = 0
    · simp only [hi,List.getElem_cons_zero]
      change ram ((dst+BitVec.ofNat 32 pos)+0#32) = b
      rw [BitVec.add_zero];exact hb
    · have hn : i.val-1 < xs.length := by have := i.isLt;simp only [List.length_cons] at this;omega
      have hj : i.val = (i.val-1)+1 := by omega
      have hh := ht.bytes ⟨i.val-1,hn⟩
      change ram ((dst+BitVec.ofNat 32 (pos+1))+BitVec.ofNat 32 (i.val-1)) = xs[i.val-1] at hh
      have he : (dst+BitVec.ofNat 32 pos)+BitVec.ofNat 32 i.val =
          (dst+BitVec.ofNat 32 (pos+1))+BitVec.ofNat 32 (i.val-1) := by
        simp only [BitVec.add_assoc,←BitVec.ofNat_add];congr 2;omega
      rw [he]
      have hl : (b::xs)[i.val] = xs[i.val-1] := by
        have helem : (b::xs)[(i.val-1)+1] = xs[i.val-1] := by rw [List.getElem_cons_succ]
        simpa only [←hj] using helem
      exact hh.trans hl.symm
end E5R.Thermostat.Bytes
