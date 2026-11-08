import Projects.thermostat.HttpPutTurn
import Projects.thermostat.ByteWrite
import Projects.thermostat.ReadFrame
namespace E5R.Thermostat.HttpPutData
open E5R E5R.Thermostat

theorem byte_word (v : BitVec 8) : byteOf (v.setWidth 32) 0=v := by
  apply BitVec.eq_of_toNat_eq
  have hv := v.isLt
  simp only [byteOf,BitVec.toNat_ofNat,BitVec.toNat_setWidth,Nat.pow_zero,Nat.div_one]
  omega

theorem memory (ram : Word → BitVec 8) (src dst pos cap finish : Word) (v : BitVec 8) :
    HttpPutTurn.memory ram src dst pos cap finish v=ramPut ram (dst+pos) v := by
  unfold HttpPutTurn.memory
  change ramPut ram (dst+pos) (byteOf (v.setWidth 32) 0)=_
  rw [byte_word]

theorem next_pos (pos : Nat) : (BitVec.ofNat 32 pos)+1#32=BitVec.ofNat 32 (pos+1) := by
  rw [←BitVec.ofNat_add]

theorem next_dst (dst : Word) (pos : Nat) : (dst+BitVec.ofNat 32 pos)+1#32=dst+BitVec.ofNat 32 (pos+1) := by
  rw [BitVec.add_assoc,next_pos]

theorem tail_source {B ram src dst xs v}
    (hs : ReadBytes.Span B img ram src (v::xs))
    (hsep : WordRegions.Disjoint src (v::xs).length dst (v::xs).length) :
    ReadBytes.Span B img (ramPut ram dst v) (src+1#32) xs := by
  apply ReadFrame.span (ReadBytes.tail hs)
  intro i
  apply ramPut_ne
  have hh := hsep ⟨1+i.val,by have := i.isLt;simp only [List.length_cons];omega⟩ ⟨0,by simp⟩
  simpa only [BitVec.add_zero,BitVec.ofNat_add,BitVec.add_assoc] using hh

theorem tail_disjoint {src dst : Word} {v : BitVec 8} {xs : List (BitVec 8)}
    (hsep : WordRegions.Disjoint src (v::xs).length dst (v::xs).length) :
    WordRegions.Disjoint (src+1#32) xs.length (dst+1#32) xs.length := by
  intro i j
  have hh := hsep ⟨1+i.val,by have := i.isLt;simp only [List.length_cons];omega⟩
    ⟨1+j.val,by have := j.isLt;simp only [List.length_cons];omega⟩
  simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hh
end E5R.Thermostat.HttpPutData
