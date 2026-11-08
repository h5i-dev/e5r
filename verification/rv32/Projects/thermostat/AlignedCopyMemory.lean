import Projects.thermostat.AlignedCopyLoop
import Projects.thermostat.WordBytes
import Projects.thermostat.BytesAppend
import Projects.thermostat.ViewFrame
import Projects.thermostat.Subregion
namespace E5R.Thermostat.AlignedCopyLoop
open E5R E5R.Thermostat

def bytes : List Word → List (BitVec 8)
  | [] => []
  | w::ws => WordBytes.bytes w ++ bytes ws

theorem bytes_length (ws : List Word) : (bytes ws).length = 4*ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [bytes,List.length_append,ih,List.length_cons]
    change 4+4*ws.length = 4*(ws.length+1)
    omega

theorem frame (ram : Word → BitVec 8) (dst : Word) (ws : List Word) (x : Word)
    (hx : ∀ i : Fin (4*ws.length), x ≠ dst+BitVec.ofNat 32 i.val) : writes ram dst ws x = ram x := by
  induction ws generalizing ram dst with
  | nil => rfl
  | cons w ws ih =>
    change writes (ramWrite ram dst w .w) (dst+4#32) ws x = ram x
    rw [ih _ _ (by
      intro i
      simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hx ⟨4+i.val,by have := i.isLt;simp only [List.length_cons];omega⟩)]
    exact ramWrite_w_other ram dst w x (fun i hi => hx ⟨i,by simp only [List.length_cons];omega⟩)

theorem written {B} (ram : Word → BitVec 8) (dst : Word) (ws : List Word)
    (hm : Memory.Block B dst (4*ws.length)) (htop : dst.toNat+4*ws.length<2^32) :
    Bytes.Span B (writes ram dst ws) dst (bytes ws) := by
  induction ws generalizing ram dst with
  | nil => exact Bytes.empty B ram dst
  | cons w ws ih =>
    have hc : 4*(w::ws).length < 2^32 := by omega
    have hb : 4+4*ws.length ≤ 4*(w::ws).length := by simp only [List.length_cons];omega
    have hm' := Subregion.block hm hc htop 4 (4*ws.length) hb
    have ht' := Subregion.nowrap htop 4 (4*ws.length) hb
    have htail := ih (ramWrite ram dst w .w) (dst+4#32) hm' ht'
    have hfirst : Bytes.Span B (writes (ramWrite ram dst w .w) (dst+4#32) ws) dst (WordBytes.bytes w) := by
      have hm4 : Memory.Block B dst 4 := by
        simpa only [BitVec.add_zero] using Memory.sub_block hm (off := 0) (m := 4) (by decide) (by simp only [List.length_cons];omega)
      apply ViewFrame.span (WordBytes.span ram dst w hm4)
      intro i
      apply frame
      intro j
      have hi : i.val<4 := i.isLt
      have hj := j.isLt
      simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using WordZero.offset_ne dst i.val (4+j.val)
        (by omega) (by simp only [List.length_cons] at hc;omega) (by omega)
    apply Bytes.append_of_block hm hc _ hfirst htail
    simp only [bytes_length]
    change 4+4*ws.length ≤ 4*(w::ws).length
    exact hb
end E5R.Thermostat.AlignedCopyLoop
