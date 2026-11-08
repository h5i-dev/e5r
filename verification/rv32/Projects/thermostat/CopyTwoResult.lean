import Projects.thermostat.CopyScratchFrame
import Projects.thermostat.CopyLastResult
namespace E5R.Thermostat.CopyTwoResult
open E5R E5R.Thermostat

def words := UnalignedCopyLoop.mixes (UnalignedCopyData.initial true) (UnalignedCopyData.nexts true) (UnalignedCopyData.shift true) (UnalignedCopyData.comp true)

theorem words_length : words.length=7 := by rw [words,UnalignedCopyLoop.length];decide

theorem bytes_length : (AlignedCopyLoop.bytes words).length=28 := by rw [AlignedCopyLoop.bytes_length,words_length]

theorem memory_eq (ram : Word → BitVec 8) (sp dst : Word) :
    CopyTwoExecute.memory ram sp dst=CopyLastResult.memory (CopyTwoFinal.scratch (CopyTwoExecute.prefixMemory ram sp dst) sp)
      dst (AlignedCopyLoop.bytes words) (UnalignedCopyData.lastPayload true) [125#8] := by
  simp only [CopyTwoExecute.memory,CopyLastResult.memory,bytes_length]

theorem written (ram : Word → BitVec 8) (sp dst : Word)
    (hd : Memory.Block UartPlatform.board dst 33) (hw : dst.toNat+33<2^32)
    (hn : WordRegions.Disjoint sp 16 dst 33) :
    Bytes.Span UartPlatform.board (CopyTwoExecute.memory ram sp dst) dst (ReplyJson.errorBody (UnalignedCopyData.error true)) := by
  have hp : Bytes.Span UartPlatform.board (CopyTwoExecute.prefixMemory ram sp dst) dst (AlignedCopyLoop.bytes words) :=
    AlignedCopyLoop.written (CopyInitData.halfRam ram sp) dst words
      (by rw [words_length];simpa only [BitVec.add_zero] using Memory.sub_block hd (off := 0) (m := 28) (by decide) (by decide))
      (by rw [words_length];omega)
  have hs : Bytes.Span UartPlatform.board (CopyTwoFinal.scratch (CopyTwoExecute.prefixMemory ram sp dst) sp) dst (AlignedCopyLoop.bytes words) := by
    apply ViewFrame.span hp
    intro i
    apply CopyScratchFrame.two
    intro j
    exact Ne.symm (hn j ⟨i.val,by have hi:=i.isLt;have hl:=bytes_length;omega⟩)
  have ht := CopyLastResult.written (CopyTwoFinal.scratch (CopyTwoExecute.prefixMemory ram sp dst) sp) dst (AlignedCopyLoop.bytes words) (UnalignedCopyData.lastPayload true) [125#8]
    (by simpa only [bytes_length,List.length_cons,List.length_nil,Nat.reduceAdd] using hd) (by rw [bytes_length];change dst.toNat+28+4+1<2^32;omega) hs
  rw [←memory_eq] at ht
  have he : ((AlignedCopyLoop.bytes words++WordBytes.bytes (UnalignedCopyData.lastPayload true))++[125#8])=ReplyJson.errorBody (UnalignedCopyData.error true) := by
    simpa only [words,List.append_assoc] using UnalignedCopyData.bytes true
  rw [he] at ht
  exact ht

theorem frame (ram : Word → BitVec 8) (sp dst x : Word)
    (hs : ∀ i : Fin 16, x≠sp+BitVec.ofNat 32 i.val)
    (hd : ∀ i : Fin 33, x≠dst+BitVec.ofNat 32 i.val) : CopyTwoExecute.memory ram sp dst x=ram x := by
  rw [memory_eq,CopyLastResult.frame _ _ _ _ _ _ (by
    intro i;exact hd ⟨i.val,by have hi:=i.isLt;change i.val<(AlignedCopyLoop.bytes words).length+4+1 at hi;have hl:=bytes_length;omega⟩)]
  rw [CopyScratchFrame.two _ _ _ hs]
  unfold CopyTwoExecute.prefixMemory
  rw [AlignedCopyLoop.frame _ _ _ _ (by
    intro i;exact hd ⟨i.val,by have hi:=i.isLt;change i.val<4*words.length at hi;have hl:=words_length;omega⟩)]
  exact CopyScratchFrame.initial_half ram sp x hs
end E5R.Thermostat.CopyTwoResult
