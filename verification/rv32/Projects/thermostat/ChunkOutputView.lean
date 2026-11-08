import Projects.thermostat.ChunkLayout
import Projects.thermostat.ResponseWordBytes
namespace E5R.Thermostat.ChunkOutputView
open E5R E5R.Thermostat HttpRequestSpec

def tag (o : COut) : Word := BitVec.ofNat 32 (ChunkLayout.outTag o).toNat

theorem tag_load {ram p out} (h : ChunkLayout.OutAt ram p out) :
    extend .h false (ramRead ram (p+32#32) .h)=tag out := by
  have htag : byteOf (tag out) 0=ChunkLayout.outTag out := by cases out <;> simp [tag,ChunkLayout.outTag,byteOf]
  apply ResponseWordBytes.half _ _ _ (by cases out <;> simp [tag,ChunkLayout.outTag])
  intro i
  have hi := i.isLt
  have hc : i.val=0 ∨ i.val=1 := by omega
  rcases hc with e|e
  · simpa [e,htag] using h.1
  · have hh := h.2.1
    have addr : (p+32#32)+BitVec.ofNat 32 i.val=p+33#32 := by
      rw [e,BitVec.add_assoc,show 32#32+1#32=33#32 by decide +kernel]
    rw [addr,hh,e]
    cases out <;> simp [tag,ChunkLayout.outTag,byteOf]

theorem status_load {ram p status} (h : ChunkLayout.OutAt ram p (.reject status))
    (hs : status<65536) :
    extend .h false (ramRead ram (p+34#32) .h)=BitVec.ofNat 32 status := by
  apply ResponseWordBytes.half _ _ _ (by simp only [BitVec.toNat_ofNat];omega)
  intro i
  have hi := i.isLt
  have hc : i.val=0 ∨ i.val=1 := by omega
  rcases hc with e|e
  · simpa [e] using h.2.2.1
  · have addr : (p+34#32)+BitVec.ofNat 32 i.val=p+35#32 := by
      rw [e,BitVec.add_assoc,show 34#32+1#32=35#32 by decide +kernel]
    rw [addr]
    simpa only [e] using h.2.2.2

end E5R.Thermostat.ChunkOutputView
