import Projects.thermostat.MainRelayCapture
import Projects.thermostat.FrameOffsets
import Projects.thermostat.ViewFrame
import Projects.thermostat.WordRegions
set_option autoImplicit false
namespace E5R.Thermostat.MainRelayCapture
open E5R E5R.Thermostat

theorem first_word (ram : Word → BitVec 8) (params pathSize : Word) :
    ramRead (memory ram params pathSize) params .w=7#32 := by
  unfold memory
  have kept := FrameOffsets.word (ramWrite ram params 7#32 .w) params pathSize 0 4 .w (by decide) (by decide) (by decide)
  simp only [BitVec.add_zero] at kept
  rw [kept];exact ramRead_ramWrite_w _ _ _

theorem second_word (ram : Word → BitVec 8) (params pathSize : Word) :
    ramRead (memory ram params pathSize) (params+4#32) .w=pathSize := ramRead_ramWrite_w _ _ _

/-- The actual pair of capture stores touches exactly the first eight parameter
    bytes. In particular this preserves the saved matcher ABI and head fields. -/
theorem frame (ram : Word → BitVec 8) (params pathSize x : Word)
    (apart : ∀ i : Fin 8, x≠params+BitVec.ofNat 32 i.val) :
    memory ram params pathSize x=ram x := by
  unfold memory
  rw [StoreBytes.frame _ _ _ _ .w (fun j => by
    have h := apart ⟨4+j.val,by have := j.isLt;change j.val<4 at this;omega⟩
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using h)]
  apply StoreBytes.frame
  intro j
  exact apart ⟨j.val,by have := j.isLt;change j.val<4 at this;omega⟩

theorem region (ram : Word → BitVec 8) (params pathSize obj : Word) (size : Nat)
    (apart : WordRegions.Disjoint obj size params 8) :
    ViewFrame.Region ram (memory ram params pathSize) obj size := fun i => frame ram params pathSize _ (apart i)
end E5R.Thermostat.MainRelayCapture
