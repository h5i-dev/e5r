import Projects.thermostat.CopyScratchFrame
import Projects.thermostat.CopyLastResult
namespace E5R.Thermostat.CopyThreeResult
open E5R E5R.Thermostat

def words := UnalignedCopyLoop.mixes (UnalignedCopyData.initial false) (UnalignedCopyData.nexts false) (UnalignedCopyData.shift false) (UnalignedCopyData.comp false)

theorem words_length : words.length=5 := by rw [words,UnalignedCopyLoop.length];decide

theorem bytes_length : (AlignedCopyLoop.bytes words).length=20 := by rw [AlignedCopyLoop.bytes_length,words_length]

theorem memory_eq (ram : Word → BitVec 8) (sp dst : Word) :
    CopyThreeExecute.memory ram sp dst=CopyLastResult.memory (CopyThreeFinal.scratch (CopyThreeExecute.prefixMemory ram sp dst) sp)
      dst (AlignedCopyLoop.bytes words) (UnalignedCopyData.lastPayload false) [125#8] := by
  simp only [CopyThreeExecute.memory,CopyLastResult.memory,bytes_length]

theorem written (ram : Word → BitVec 8) (sp dst : Word)
    (hd : Memory.Block UartPlatform.board dst 25) (hw : dst.toNat+25<2^32)
    (hn : WordRegions.Disjoint sp 16 dst 25) :
    Bytes.Span UartPlatform.board (CopyThreeExecute.memory ram sp dst) dst (ReplyJson.errorBody (UnalignedCopyData.error false)) := by
  have hp : Bytes.Span UartPlatform.board (CopyThreeExecute.prefixMemory ram sp dst) dst (AlignedCopyLoop.bytes words) :=
    AlignedCopyLoop.written (CopyInitData.byteRam ram sp) dst words
      (by rw [words_length];simpa only [BitVec.add_zero] using Memory.sub_block hd (off := 0) (m := 20) (by decide) (by decide))
      (by rw [words_length];omega)
  have hs : Bytes.Span UartPlatform.board (CopyThreeFinal.scratch (CopyThreeExecute.prefixMemory ram sp dst) sp) dst (AlignedCopyLoop.bytes words) := by
    apply ViewFrame.span hp
    intro i
    apply CopyScratchFrame.three
    intro j
    exact Ne.symm (hn j ⟨i.val,by have hi:=i.isLt;have hl:=bytes_length;omega⟩)
  have ht := CopyLastResult.written (CopyThreeFinal.scratch (CopyThreeExecute.prefixMemory ram sp dst) sp) dst (AlignedCopyLoop.bytes words) (UnalignedCopyData.lastPayload false) [125#8]
    (by simpa only [bytes_length,List.length_cons,List.length_nil,Nat.reduceAdd] using hd) (by rw [bytes_length];change dst.toNat+20+4+1<2^32;omega) hs
  rw [←memory_eq] at ht
  have he : ((AlignedCopyLoop.bytes words++WordBytes.bytes (UnalignedCopyData.lastPayload false))++[125#8])=ReplyJson.errorBody (UnalignedCopyData.error false) := by
    simpa only [words,List.append_assoc] using UnalignedCopyData.bytes false
  rw [he] at ht
  exact ht

theorem frame (ram : Word → BitVec 8) (sp dst x : Word)
    (hs : ∀ i : Fin 16, x≠sp+BitVec.ofNat 32 i.val)
    (hd : ∀ i : Fin 25, x≠dst+BitVec.ofNat 32 i.val) : CopyThreeExecute.memory ram sp dst x=ram x := by
  rw [memory_eq,CopyLastResult.frame _ _ _ _ _ _ (by
    intro i;exact hd ⟨i.val,by have hi:=i.isLt;change i.val<(AlignedCopyLoop.bytes words).length+4+1 at hi;have hl:=bytes_length;omega⟩)]
  rw [CopyScratchFrame.three _ _ _ hs]
  unfold CopyThreeExecute.prefixMemory
  rw [AlignedCopyLoop.frame _ _ _ _ (by
    intro i;exact hd ⟨i.val,by have hi:=i.isLt;change i.val<4*words.length at hi;have hl:=words_length;omega⟩)]
  exact CopyScratchFrame.initial_byte ram sp x hs
end E5R.Thermostat.CopyThreeResult
