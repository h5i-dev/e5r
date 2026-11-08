import Projects.thermostat.AlignedCopyMemory
import Projects.thermostat.ByteWrite
namespace E5R.Thermostat.AlignedCopyResult
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (dst : Word) (ws : List Word) (tail : List (BitVec 8)) :=
  ByteWrite.write (AlignedCopyLoop.writes ram dst ws) (dst+BitVec.ofNat 32 (4*ws.length)) tail

theorem frame (ram : Word → BitVec 8) (dst : Word) (ws : List Word) (tail : List (BitVec 8)) (x : Word)
    (hx : ∀ i : Fin (4*ws.length+tail.length), x ≠ dst+BitVec.ofNat 32 i.val) : memory ram dst ws tail x=ram x := by
  unfold memory
  rw [ByteWrite.frame _ _ _ _ (by
    intro i
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hx ⟨4*ws.length+i.val,by have := i.isLt;omega⟩)]
  exact AlignedCopyLoop.frame ram dst ws x (fun i => hx ⟨i.val,by have := i.isLt;omega⟩)

theorem written {B} (ram : Word → BitVec 8) (dst : Word) (ws : List Word) (tail : List (BitVec 8))
    (hm : Memory.Block B dst (4*ws.length+tail.length)) (hw : dst.toNat+4*ws.length+tail.length<2^32) :
    Bytes.Span B (memory ram dst ws tail) dst (AlignedCopyLoop.bytes ws++tail) := by
  have hn : 4*ws.length+tail.length<2^32 := by omega
  have htop : dst.toNat+(4*ws.length+tail.length)<2^32 := by omega
  have hfull := AlignedCopyLoop.written ram dst ws
    (by simpa only [BitVec.add_zero] using Subregion.block hm hn htop 0 (4*ws.length) (by omega)) (by omega)
  have hprefix : Bytes.Span B (memory ram dst ws tail) dst (AlignedCopyLoop.bytes ws) := by
    apply ViewFrame.span hfull
    intro i
    have hi : i.val<4*ws.length := by have hh := i.isLt;have hl := AlignedCopyLoop.bytes_length ws;omega
    apply ByteWrite.frame
    intro j
    have hj := j.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using WordZero.offset_ne dst i.val (4*ws.length+j.val) (by omega) (by omega) (by omega)
  have htail : Bytes.Span B (memory ram dst ws tail) (dst+BitVec.ofNat 32 (4*ws.length)) tail :=
    ByteWrite.span (Subregion.block hm hn htop (4*ws.length) tail.length (by omega)) (by omega)
  have hh := Bytes.append_of_block (xs := AlignedCopyLoop.bytes ws) (ys := tail) hm hn (by rw [AlignedCopyLoop.bytes_length];exact Nat.le_refl _) hprefix
    (by simpa only [AlignedCopyLoop.bytes_length] using htail)
  exact hh
end E5R.Thermostat.AlignedCopyResult
