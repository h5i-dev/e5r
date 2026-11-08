import Projects.thermostat.EncodeReplyConstruct
import Projects.thermostat.ViewFrame
namespace E5R.Thermostat.EncodeReplyConstruct
open E5R E5R.Thermostat

theorem words (ram : Word → BitVec 8) (sp reply modePtr modeLen : Word) :
    ramRead (memory ram sp reply modePtr modeLen) (sp+20#32) .w = modePtr ∧
    ramRead (memory ram sp reply modePtr modeLen) (sp+24#32) .w = modeLen ∧
    ramRead (memory ram sp reply modePtr modeLen) (sp+28#32) .w = reply+4#32 ∧
    ramRead (memory ram sp reply modePtr modeLen) (sp+32#32) .w = 0x80004e5e#32 ∧
    ramRead (memory ram sp reply modePtr modeLen) (sp+36#32) .w = reply+6#32 ∧
    ramRead (memory ram sp reply modePtr modeLen) (sp+40#32) .w = 0x80004e5e#32 ∧
    ramRead (memory ram sp reply modePtr modeLen) (sp+44#32) .w = reply+8#32 ∧
    ramRead (memory ram sp reply modePtr modeLen) (sp+48#32) .w = 0x80005112#32 ∧
    ramRead (memory ram sp reply modePtr modeLen) (sp+52#32) .w = reply ∧
    ramRead (memory ram sp reply modePtr modeLen) (sp+56#32) .w = 0x80005112#32 ∧
    ramRead (memory ram sp reply modePtr modeLen) (sp+60#32) .w = reply+1#32 ∧
    ramRead (memory ram sp reply modePtr modeLen) (sp+64#32) .w = 0x80005112#32 ∧
    ramRead (memory ram sp reply modePtr modeLen) (sp+68#32) .w = reply+2#32 ∧
    ramRead (memory ram sp reply modePtr modeLen) (sp+72#32) .w = 0x80005112#32 ∧
    ramRead (memory ram sp reply modePtr modeLen) (sp+76#32) .w = reply+3#32 ∧
    ramRead (memory ram sp reply modePtr modeLen) (sp+80#32) .w = 0x80005112#32 ∧
    ramRead (memory ram sp reply modePtr modeLen) (sp+84#32) .w = sp+20#32 ∧
    ramRead (memory ram sp reply modePtr modeLen) (sp+88#32) .w = 0x8000228c#32 := by
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ⟩
  · unfold memory
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 20 88 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 20 84 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 20 80 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 20 76 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 20 72 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 20 68 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 20 64 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 20 60 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 20 56 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 20 52 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 20 48 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 20 44 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 20 40 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 20 36 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 20 32 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 20 28 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 20 24 (by decide) (by decide) (by decide) (by decide) (by decide))]
    exact ramRead_ramWrite_w _ _ _
  · unfold memory
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 24 88 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 24 84 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 24 80 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 24 76 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 24 72 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 24 68 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 24 64 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 24 60 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 24 56 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 24 52 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 24 48 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 24 44 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 24 40 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 24 36 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 24 32 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 24 28 (by decide) (by decide) (by decide) (by decide) (by decide))]
    exact ramRead_ramWrite_w _ _ _
  · unfold memory
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 28 88 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 28 84 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 28 80 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 28 76 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 28 72 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 28 68 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 28 64 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 28 60 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 28 56 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 28 52 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 28 48 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 28 44 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 28 40 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 28 36 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 28 32 (by decide) (by decide) (by decide) (by decide) (by decide))]
    exact ramRead_ramWrite_w _ _ _
  · unfold memory
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 32 88 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 32 84 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 32 80 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 32 76 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 32 72 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 32 68 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 32 64 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 32 60 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 32 56 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 32 52 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 32 48 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 32 44 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 32 40 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 32 36 (by decide) (by decide) (by decide) (by decide) (by decide))]
    exact ramRead_ramWrite_w _ _ _
  · unfold memory
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 36 88 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 36 84 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 36 80 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 36 76 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 36 72 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 36 68 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 36 64 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 36 60 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 36 56 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 36 52 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 36 48 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 36 44 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 36 40 (by decide) (by decide) (by decide) (by decide) (by decide))]
    exact ramRead_ramWrite_w _ _ _
  · unfold memory
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 40 88 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 40 84 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 40 80 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 40 76 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 40 72 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 40 68 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 40 64 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 40 60 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 40 56 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 40 52 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 40 48 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 40 44 (by decide) (by decide) (by decide) (by decide) (by decide))]
    exact ramRead_ramWrite_w _ _ _
  · unfold memory
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 44 88 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 44 84 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 44 80 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 44 76 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 44 72 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 44 68 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 44 64 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 44 60 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 44 56 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 44 52 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 44 48 (by decide) (by decide) (by decide) (by decide) (by decide))]
    exact ramRead_ramWrite_w _ _ _
  · unfold memory
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 48 88 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 48 84 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 48 80 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 48 76 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 48 72 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 48 68 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 48 64 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 48 60 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 48 56 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 48 52 (by decide) (by decide) (by decide) (by decide) (by decide))]
    exact ramRead_ramWrite_w _ _ _
  · unfold memory
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 52 88 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 52 84 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 52 80 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 52 76 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 52 72 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 52 68 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 52 64 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 52 60 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 52 56 (by decide) (by decide) (by decide) (by decide) (by decide))]
    exact ramRead_ramWrite_w _ _ _
  · unfold memory
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 56 88 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 56 84 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 56 80 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 56 76 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 56 72 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 56 68 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 56 64 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 56 60 (by decide) (by decide) (by decide) (by decide) (by decide))]
    exact ramRead_ramWrite_w _ _ _
  · unfold memory
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 60 88 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 60 84 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 60 80 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 60 76 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 60 72 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 60 68 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 60 64 (by decide) (by decide) (by decide) (by decide) (by decide))]
    exact ramRead_ramWrite_w _ _ _
  · unfold memory
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 64 88 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 64 84 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 64 80 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 64 76 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 64 72 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 64 68 (by decide) (by decide) (by decide) (by decide) (by decide))]
    exact ramRead_ramWrite_w _ _ _
  · unfold memory
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 68 88 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 68 84 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 68 80 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 68 76 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 68 72 (by decide) (by decide) (by decide) (by decide) (by decide))]
    exact ramRead_ramWrite_w _ _ _
  · unfold memory
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 72 88 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 72 84 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 72 80 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 72 76 (by decide) (by decide) (by decide) (by decide) (by decide))]
    exact ramRead_ramWrite_w _ _ _
  · unfold memory
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 76 88 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 76 84 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 76 80 (by decide) (by decide) (by decide) (by decide) (by decide))]
    exact ramRead_ramWrite_w _ _ _
  · unfold memory
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 80 88 (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 80 84 (by decide) (by decide) (by decide) (by decide) (by decide))]
    exact ramRead_ramWrite_w _ _ _
  · unfold memory
    rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 84 88 (by decide) (by decide) (by decide) (by decide) (by decide))]
    exact ramRead_ramWrite_w _ _ _
  · unfold memory
    exact ramRead_ramWrite_w _ _ _

theorem frame (ram : Word → BitVec 8) (sp reply modePtr modeLen : Word) (x : Word)
    (hx : ∀ i : Fin 72, x ≠ (sp+20#32)+BitVec.ofNat 32 i.val) : memory ram sp reply modePtr modeLen x = ram x := by
  unfold memory
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;have hh := hx ⟨68+i,by omega⟩;change x ≠ (sp+20#32)+BitVec.ofNat 32 (68+i) at hh;simpa only [BitVec.add_assoc,←BitVec.ofNat_add,show 20+(68+i) = 88+i by omega] using hh)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;have hh := hx ⟨64+i,by omega⟩;change x ≠ (sp+20#32)+BitVec.ofNat 32 (64+i) at hh;simpa only [BitVec.add_assoc,←BitVec.ofNat_add,show 20+(64+i) = 84+i by omega] using hh)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;have hh := hx ⟨60+i,by omega⟩;change x ≠ (sp+20#32)+BitVec.ofNat 32 (60+i) at hh;simpa only [BitVec.add_assoc,←BitVec.ofNat_add,show 20+(60+i) = 80+i by omega] using hh)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;have hh := hx ⟨56+i,by omega⟩;change x ≠ (sp+20#32)+BitVec.ofNat 32 (56+i) at hh;simpa only [BitVec.add_assoc,←BitVec.ofNat_add,show 20+(56+i) = 76+i by omega] using hh)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;have hh := hx ⟨52+i,by omega⟩;change x ≠ (sp+20#32)+BitVec.ofNat 32 (52+i) at hh;simpa only [BitVec.add_assoc,←BitVec.ofNat_add,show 20+(52+i) = 72+i by omega] using hh)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;have hh := hx ⟨48+i,by omega⟩;change x ≠ (sp+20#32)+BitVec.ofNat 32 (48+i) at hh;simpa only [BitVec.add_assoc,←BitVec.ofNat_add,show 20+(48+i) = 68+i by omega] using hh)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;have hh := hx ⟨44+i,by omega⟩;change x ≠ (sp+20#32)+BitVec.ofNat 32 (44+i) at hh;simpa only [BitVec.add_assoc,←BitVec.ofNat_add,show 20+(44+i) = 64+i by omega] using hh)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;have hh := hx ⟨40+i,by omega⟩;change x ≠ (sp+20#32)+BitVec.ofNat 32 (40+i) at hh;simpa only [BitVec.add_assoc,←BitVec.ofNat_add,show 20+(40+i) = 60+i by omega] using hh)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;have hh := hx ⟨36+i,by omega⟩;change x ≠ (sp+20#32)+BitVec.ofNat 32 (36+i) at hh;simpa only [BitVec.add_assoc,←BitVec.ofNat_add,show 20+(36+i) = 56+i by omega] using hh)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;have hh := hx ⟨32+i,by omega⟩;change x ≠ (sp+20#32)+BitVec.ofNat 32 (32+i) at hh;simpa only [BitVec.add_assoc,←BitVec.ofNat_add,show 20+(32+i) = 52+i by omega] using hh)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;have hh := hx ⟨28+i,by omega⟩;change x ≠ (sp+20#32)+BitVec.ofNat 32 (28+i) at hh;simpa only [BitVec.add_assoc,←BitVec.ofNat_add,show 20+(28+i) = 48+i by omega] using hh)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;have hh := hx ⟨24+i,by omega⟩;change x ≠ (sp+20#32)+BitVec.ofNat 32 (24+i) at hh;simpa only [BitVec.add_assoc,←BitVec.ofNat_add,show 20+(24+i) = 44+i by omega] using hh)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;have hh := hx ⟨20+i,by omega⟩;change x ≠ (sp+20#32)+BitVec.ofNat 32 (20+i) at hh;simpa only [BitVec.add_assoc,←BitVec.ofNat_add,show 20+(20+i) = 40+i by omega] using hh)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;have hh := hx ⟨16+i,by omega⟩;change x ≠ (sp+20#32)+BitVec.ofNat 32 (16+i) at hh;simpa only [BitVec.add_assoc,←BitVec.ofNat_add,show 20+(16+i) = 36+i by omega] using hh)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;have hh := hx ⟨12+i,by omega⟩;change x ≠ (sp+20#32)+BitVec.ofNat 32 (12+i) at hh;simpa only [BitVec.add_assoc,←BitVec.ofNat_add,show 20+(12+i) = 32+i by omega] using hh)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;have hh := hx ⟨8+i,by omega⟩;change x ≠ (sp+20#32)+BitVec.ofNat 32 (8+i) at hh;simpa only [BitVec.add_assoc,←BitVec.ofNat_add,show 20+(8+i) = 28+i by omega] using hh)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;have hh := hx ⟨4+i,by omega⟩;change x ≠ (sp+20#32)+BitVec.ofNat 32 (4+i) at hh;simpa only [BitVec.add_assoc,←BitVec.ofNat_add,show 20+(4+i) = 24+i by omega] using hh)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;have hh := hx ⟨0+i,by omega⟩;change x ≠ (sp+20#32)+BitVec.ofNat 32 (0+i) at hh;simpa only [BitVec.add_assoc,←BitVec.ofNat_add,show 20+(0+i) = 20+i by omega] using hh)]
end E5R.Thermostat.EncodeReplyConstruct
