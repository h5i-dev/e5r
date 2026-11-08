import Projects.thermostat.WriteSuccess
import Projects.thermostat.AppState
namespace E5R.Thermostat.MainWritePost
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

structure At (c d : Core) (before after : Word → BitVec 8) (state : Spec.Snapshot) (payload : List (BitVec 8)) (status : Nat) : Prop where
  pc : d.pc=0x8000196c#32
  sp : d.get 2=0x80ffeb90#32
  fp : d.get 8=0x80fff814#32
  ready : d.get 18=1#32
  completion : d.get 22=1#32
  csr : d.sameCsr c
  app : AppState.At after state
  inv : Spec.Inv state
  response : BodyMemory.At after 0x80fffd38#32 0x800056a8#32 16#32 (BitVec.ofNat 32 payload.length) (BitVec.ofNat 32 status)
  body : Bytes.Span B after 0x80fff4d4#32 payload
  metadata : ViewFrame.Region before after 0x80fff814#32 532
  rx : ViewFrame.Region before after 0x80ffec14#32 2048

def Frame (before after : Word → BitVec 8) : Prop := ∀ x,
    (∀ i : Fin 416, x≠0x80ffe9f0#32+BitVec.ofNat 32 i.val) →
    (∀ i : Fin 832, x≠0x80fff4d4#32+BitVec.ofNat 32 i.val) →
    (∀ i : Fin 15, x≠0x80fffd38#32+BitVec.ofNat 32 i.val) →
    (∀ i : Fin 41, x≠0x80fffa2c#32+BitVec.ofNat 32 i.val) →
    (∀ i : Fin 14, x≠0x80ffebbc#32+BitVec.ofNat 32 i.val) → after x=before x

theorem keys {before after} (h : Frame before after) : ViewFrame.Region before after 0x80ffebcc#32 9 := by
  intro i
  exact h _ (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i)
    (WordRegions.before _ _ _ _ (by decide) (by decide) i)
    (WordRegions.before _ _ _ _ (by decide) (by decide) i)
    (WordRegions.before _ _ _ _ (by decide) (by decide) i)
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i)

theorem metadata {before after} (h : Frame before after) : ViewFrame.Region before after 0x80fff814#32 532 := by
  intro i
  exact h _ (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i)
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i)
    (WordRegions.before _ _ _ _ (by decide) (by decide) i)
    (WordRegions.before _ _ _ _ (by decide) (by decide) i)
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i)

theorem rx {before after} (h : Frame before after) : ViewFrame.Region before after 0x80ffec14#32 2048 := by
  intro i
  exact h _ (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i)
    (WordRegions.before _ _ _ _ (by decide) (by decide) i)
    (WordRegions.before _ _ _ _ (by decide) (by decide) i)
    (WordRegions.before _ _ _ _ (by decide) (by decide) i)
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i)

theorem app {before after state} (h : Frame before after) (hb : AppState.At before state)
    (next : Spec.Snapshot) (hs : Encoding.SnapshotAt after 0x80ffebc0#32 next) (havail : ramRead after 0x80ffebbc#32 .w=0#32) : AppState.At after next := by
  have k := keys h
  refine ⟨hs,havail,?_,?_,?_⟩
  · exact (ViewFrame.word k 0 (by decide)).trans hb.keyPtr
  · exact (ViewFrame.word k 4 (by decide)).trans hb.keyLen
  · exact (k ⟨8,by decide⟩).trans hb.principal
end E5R.Thermostat.MainWritePost
