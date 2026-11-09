import Projects.thermostat.LoopKeepLayout
import Projects.thermostat.LoopMemmoveZero
import Projects.thermostat.WordRegions
set_option autoImplicit false
namespace E5R.Thermostat.LoopKeepFrames
open E5R E5R.Thermostat

theorem move_frame (ram : Word → BitVec 8) (dst src fp x : Word)
    (away : ∀ i : Fin 4, x≠0x80ffeb8c#32+BitVec.ofNat 32 i.val) :
    LoopMemmoveZero.memory ram dst src fp x=ram x := by
  unfold LoopMemmoveZero.memory
  exact StoreBytes.frame ram _ fp x .w away

theorem move_region (ram : Word → BitVec 8) (dst src fp p : Word) (n : Nat)
    (away : WordRegions.Disjoint p n 0x80ffeb8c#32 4) :
    ViewFrame.Region ram (LoopMemmoveZero.memory ram dst src fp) p n :=
  fun i => move_frame ram dst src fp _ (away i)

theorem rebuild_frame (ram : Word → BitVec 8) (used x : Word)
    (away : ∀ i : Fin 449, x≠0x80fff814#32+BitVec.ofNat 32 i.val) :
    LoopKeepRebuild.memory ram used x=ram x := by
  unfold LoopKeepRebuild.memory
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have bound : i.val<4 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add,Nat.add_assoc] using away ⟨112+i.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have bound : i.val<4 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add,Nat.add_assoc] using away ⟨108+i.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have bound : i.val<4 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add,Nat.add_assoc] using away ⟨104+i.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have bound : i.val<4 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add,Nat.add_assoc] using away ⟨100+i.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have bound : i.val<4 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add,Nat.add_assoc] using away ⟨84+i.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have bound : i.val<4 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add,Nat.add_assoc] using away ⟨432+i.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have bound : i.val<4 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add,Nat.add_assoc] using away ⟨428+i.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have bound : i.val<4 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add,Nat.add_assoc] using away ⟨424+i.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have bound : i.val<4 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add,Nat.add_assoc] using away ⟨420+i.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .b (by
    intro i
    have bound : i.val<1 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add,Nat.add_assoc] using away ⟨448+i.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have bound : i.val<4 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add,Nat.add_assoc] using away ⟨440+i.val,by omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by
    intro i
    have bound : i.val<4 := i.isLt
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add,Nat.add_assoc] using away ⟨436+i.val,by omega⟩)]

theorem rebuild_region (ram : Word → BitVec 8) (used p : Word) (n : Nat)
    (away : WordRegions.Disjoint p n 0x80fff814#32 449) :
    ViewFrame.Region ram (LoopKeepRebuild.memory ram used) p n :=
  fun i => rebuild_frame ram used _ (away i)
end E5R.Thermostat.LoopKeepFrames
