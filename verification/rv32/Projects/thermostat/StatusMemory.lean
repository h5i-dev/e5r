import Projects.thermostat.StatusResponse
import Projects.thermostat.StoreBytes
import Projects.thermostat.WordRegions
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.StatusMemory
open E5R E5R.Thermostat

def responseByte (status : Word) (i : Fin 15) : BitVec 8 :=
  if i.val = 0 then 1#8 else if i.val = 12 then byteOf status 0 else if i.val = 13 then byteOf status 1 else 0#8

def At (ram : Word → BitVec 8) (out status : Word) : Prop :=
  ∀ i : Fin 15, ram (out+BitVec.ofNat 32 i.val) = responseByte status i

theorem frame (ram : Word → BitVec 8) (out f status x : Word)
    (ho : ∀ i : Fin 15, x ≠ out+BitVec.ofNat 32 i.val)
    (hf : ∀ i : Fin 41, x ≠ f+BitVec.ofNat 32 i.val) : StatusResponse.memory ram out f status x = ram x := by
  unfold StatusResponse.memory
  rw [StoreBytes.frame _ _ _ _ .b (by intro i;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hf ⟨40+i.val,by have := i.isLt;change i.val < 1 at this;omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .b (by intro i;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact hf ⟨36+i.val,by have := i.isLt;change i.val < 1 at this;omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .b (by intro i;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact ho ⟨14+i.val,by have := i.isLt;change i.val < 1 at this;omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .h (by intro i;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact ho ⟨12+i.val,by have := i.isLt;change i.val < 2 at this;omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by intro i;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact ho ⟨8+i.val,by have := i.isLt;change i.val < 4 at this;omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by intro i;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact ho ⟨4+i.val,by have := i.isLt;change i.val < 4 at this;omega⟩)]
  rw [StoreBytes.frame _ _ _ _ .w (by intro i;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact ho ⟨0+i.val,by have := i.isLt;change i.val < 4 at this;omega⟩)]

theorem response (ram : Word → BitVec 8) (out f status : Word) (hs : WordRegions.Disjoint out 15 f 41) :
    At (StatusResponse.memory ram out f status) out status := by
  intro i
  have h40 : out+BitVec.ofNat 32 i.val ≠ f+40#32 := hs i ⟨40,by decide⟩
  have h36 : out+BitVec.ofNat 32 i.val ≠ f+36#32 := hs i ⟨36,by decide⟩
  have hi := i.isLt
  have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 ∨ i.val = 12 ∨ i.val = 13 ∨ i.val = 14 := by omega
  unfold StatusResponse.memory
  change ramPut (ramPut _ (f+36#32) _) (f+40#32) _ _ = _
  rw [ramPut_ne _ h40,ramPut_ne _ h36]
  rcases hc with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  all_goals simp [responseByte,h,ramWrite,ramPut,BitVec.add_assoc,BitVec.self_eq_add_right,BitVec.add_right_inj,byteOf]
theorem flags (ram : Word → BitVec 8) (out f status : Word) :
    StatusResponse.memory ram out f status (f+36#32) = 1#8 ∧
    StatusResponse.memory ram out f status (f+40#32) = 1#8 := by
  unfold StatusResponse.memory
  change ramPut (ramPut _ (f+36#32) 1#8) (f+40#32) 1#8 (f+36#32) = 1#8 ∧
    ramPut (ramPut _ (f+36#32) 1#8) (f+40#32) 1#8 (f+40#32) = 1#8
  constructor
  · rw [ramPut_ne _ (Bytes.offset_ne f 36 40 (by decide) (by decide) (by decide)),ramPut_eq]
  · exact ramPut_eq _ _ _
end E5R.Thermostat.StatusMemory
