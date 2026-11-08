import Projects.thermostat.AlignedCopyResult
import Projects.thermostat.WordBytes
import Projects.thermostat.BytesAppend
namespace E5R.Thermostat.CopyLastResult
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (dst : Word) (xs : List (BitVec 8)) (last : Word) (tail : List (BitVec 8)) :=
  ByteWrite.write (ramWrite ram (dst+BitVec.ofNat 32 xs.length) last .w) (dst+BitVec.ofNat 32 (xs.length+4)) tail

theorem written {B} (ram : Word → BitVec 8) (dst : Word) (xs : List (BitVec 8)) (last : Word) (tail : List (BitVec 8))
    (hm : Memory.Block B dst (xs.length+4+tail.length)) (hw : dst.toNat+xs.length+4+tail.length<2^32)
    (hx : Bytes.Span B ram dst xs) :
    Bytes.Span B (memory ram dst xs last tail) dst ((xs++WordBytes.bytes last)++tail) := by
  let r := ramWrite ram (dst+BitVec.ofNat 32 xs.length) last .w
  have hlen : (WordBytes.bytes last).length=4 := rfl
  have hpre : Bytes.Span B r dst xs := by
    apply ViewFrame.span hx
    intro i
    apply StoreBytes.frame
    intro j
    have hj : j.val<4 := j.isLt
    have hi := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using
      WordZero.offset_ne dst i.val (xs.length+j.val) (by omega) (by omega) (by omega)
  have hword : Bytes.Span B r (dst+BitVec.ofNat 32 xs.length) (WordBytes.bytes last) :=
    WordBytes.span ram _ last (Memory.sub_block hm (off := xs.length) (m := 4) (by omega) (by omega))
  have hboth : Bytes.Span B r dst (xs++WordBytes.bytes last) :=
    Bytes.append_of_block (xs := xs) (ys := WordBytes.bytes last) hm (by omega) (by rw [hlen];omega) hpre hword
  have hkeep : Bytes.Span B (memory ram dst xs last tail) dst (xs++WordBytes.bytes last) := by
    apply ViewFrame.span hboth
    intro i
    apply ByteWrite.frame
    intro j
    have hi : i.val<xs.length+4 := by have := i.isLt;simpa only [List.length_append,hlen] using this
    have hj := j.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using
      WordZero.offset_ne dst i.val (xs.length+4+j.val) (by omega) (by omega) (by omega)
  have htail : Bytes.Span B (memory ram dst xs last tail) (dst+BitVec.ofNat 32 (xs.length+4)) tail :=
    ByteWrite.span (Subregion.block hm (by omega) (by omega) (xs.length+4) tail.length (by omega)) (by omega)
  apply Bytes.append_of_block (xs := xs++WordBytes.bytes last) (ys := tail) hm (by omega) (by simp only [List.length_append,hlen];omega) hkeep
  simpa only [List.length_append,hlen] using htail

theorem frame (ram : Word → BitVec 8) (dst : Word) (xs : List (BitVec 8)) (last : Word) (tail : List (BitVec 8)) (x : Word)
    (hx : ∀ i : Fin (xs.length+4+tail.length), x≠dst+BitVec.ofNat 32 i.val) :
    memory ram dst xs last tail x=ram x := by
  unfold memory
  rw [ByteWrite.frame _ _ _ _ (by
    intro i
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hx ⟨xs.length+4+i.val,by have := i.isLt;omega⟩)]
  apply StoreBytes.frame
  intro i
  have hi : i.val<4 := i.isLt
  simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hx ⟨xs.length+i.val,by omega⟩
end E5R.Thermostat.CopyLastResult
