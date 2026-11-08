import Projects.thermostat.MainChunkLayout
import Projects.thermostat.MainChunkOutcome
import Projects.thermostat.AppState
import Projects.thermostat.ViewFrame
namespace E5R.Thermostat.MainChunkFrame
open E5R E5R.Thermostat

def BeforeAfter (before after : Word → BitVec 8) (sp : Word) : Prop :=
  ∀ x, (∀ i : Fin 32, x≠(sp+4864#32)+BitVec.ofNat 32 i.val) →
    (∀ i : Fin 36, x≠(sp+4824#32)+BitVec.ofNat 32 i.val) →
    (∀ i : Fin 4, x≠(sp+3656#32)+BitVec.ofNat 32 i.val) →
    (∀ i : Fin 32, x≠(sp+3680#32)+BitVec.ofNat 32 i.val) → after x=before x

theorem low {before after sp} (h : BeforeAfter before after sp) : ViewFrame.Region before after sp 3656 := by
  intro i
  refine h _ ?_ ?_ ?_ ?_
  · intro j
    simpa only [BitVec.add_zero] using FrameOffsets.ne sp 0 4864 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;omega) (by have := i.isLt;have := j.isLt;omega)
  · intro j
    simpa only [BitVec.add_zero] using FrameOffsets.ne sp 0 4824 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;omega) (by have := i.isLt;have := j.isLt;omega)
  · intro j
    simpa only [BitVec.add_zero] using FrameOffsets.ne sp 0 3656 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;omega) (by have := i.isLt;have := j.isLt;omega)
  · intro j
    simpa only [BitVec.add_zero] using FrameOffsets.ne sp 0 3680 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;omega) (by have := i.isLt;have := j.isLt;omega)

theorem word {before after sp} (h : BeforeAfter before after sp) (off : Nat) (hb : off+4≤3656) :
    ramRead after (sp+BitVec.ofNat 32 off) .w=ramRead before (sp+BitVec.ofNat 32 off) .w :=
  ViewFrame.word (low h) off hb

theorem layout {before after sp} (h : BeforeAfter before after sp) (hl : MainChunkLayout.At before sp) :
    MainChunkLayout.At after sp := MainChunkLayout.preserve hl (fun off _ hb => word h off hb)

theorem write_cursor {before after sp} (h : BeforeAfter before after sp) :
    ramRead after (sp+3660#32) .w=ramRead before (sp+3660#32) .w := by
  apply ramRead_w_congr
  intro k hk
  refine h _ ?_ ?_ ?_ ?_
  · intro j
    exact FrameOffsets.ne sp 3660 4864 k j.val (by omega) (by have := j.isLt;omega) (by have := j.isLt;omega)
  · intro j
    exact FrameOffsets.ne sp 3660 4824 k j.val (by omega) (by have := j.isLt;omega) (by have := j.isLt;omega)
  · intro j
    exact FrameOffsets.ne sp 3660 3656 k j.val (by omega) (by have := j.isLt;omega) (by have := j.isLt;omega)
  · intro j
    exact FrameOffsets.ne sp 3660 3680 k j.val (by omega) (by have := j.isLt;omega) (by have := j.isLt;omega)

theorem app {before after} (h : BeforeAfter before after 0x80ffeb90#32) (s : Spec.Snapshot)
    (hs : AppState.At before s) : AppState.At after s := by
  apply AppState.preserve before after s hs
  intro i
  have hi := i.isLt
  simpa only [BitVec.ofNat_add,←BitVec.add_assoc,
    show 0x80ffeb90#32+44#32=0x80ffebbc#32 by decide +kernel] using
    low h ⟨44+i.val,by omega⟩

end E5R.Thermostat.MainChunkFrame
