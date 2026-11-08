import Projects.thermostat.MainWritePost
set_option autoImplicit false
namespace E5R.Thermostat.MainFutureFrame
open E5R E5R.Thermostat

/-- Same scoped write/refusal frame as MainWritePost, with the actual caller's
    future address explicit instead of assuming the relay'sFA2C. -/
def At (future : Word) (before after : Word → BitVec 8) : Prop := ∀ x,
  (∀ i : Fin 416, x≠0x80ffe9f0#32+BitVec.ofNat 32 i.val) →
  (∀ i : Fin 832, x≠0x80fff4d4#32+BitVec.ofNat 32 i.val) →
  (∀ i : Fin 15, x≠0x80fffd38#32+BitVec.ofNat 32 i.val) →
  (∀ i : Fin 41, x≠future+BitVec.ofNat 32 i.val) →
  (∀ i : Fin 14, x≠0x80ffebbc#32+BitVec.ofNat 32 i.val) → after x=before x

theorem region {future before after obj size} (h : At future before after)
    (hs : WordRegions.Disjoint obj size 0x80ffe9f0#32 416)
    (hd : WordRegions.Disjoint obj size 0x80fff4d4#32 832)
    (ho : WordRegions.Disjoint obj size 0x80fffd38#32 15)
    (hf : WordRegions.Disjoint obj size future 41)
    (he : WordRegions.Disjoint obj size 0x80ffebbc#32 14) : ViewFrame.Region before after obj size :=
  fun i => h _ (hs i) (hd i) (ho i) (hf i) (he i)
end E5R.Thermostat.MainFutureFrame
