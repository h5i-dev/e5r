import Projects.thermostat.HeadZero271
import Projects.thermostat.FrameOffsets
import Projects.thermostat.ViewFrame
namespace E5R.Thermostat.HeadZeroMemory
open E5R E5R.Thermostat

theorem frame (ram : Word → BitVec 8) (p x : Word)
    (hx : ∀ i : Fin 271, x≠p+BitVec.ofNat 32 i.val) : HeadZero271.memory ram p x=ram x := by
  unfold HeadZero271.memory HeadZeroTail3.memory
  rw [show (p+268#32)+1#32=p+269#32 by rw [BitVec.add_assoc];rfl,
    show (p+268#32)+2#32=p+270#32 by rw [BitVec.add_assoc];rfl]
  rw [StoreBytes.frame _ _ _ _ .b (by
    intro i;have hi : i.val<1 := i.isLt;have z : i.val=0 := by omega
    simpa only [z,BitVec.add_zero] using hx ⟨270,by decide⟩)]
  rw [StoreBytes.frame _ _ _ _ .b (by
    intro i;have hi : i.val<1 := i.isLt;have z : i.val=0 := by omega
    simpa only [z,BitVec.add_zero] using hx ⟨269,by decide⟩)]
  rw [StoreBytes.frame _ _ _ _ .b (by
    intro i;have hi : i.val<1 := i.isLt;have z : i.val=0 := by omega
    simpa only [z,BitVec.add_zero] using hx ⟨268,by decide⟩)]
  exact WordZero.frame ram p 67 x (fun i => hx ⟨i.val,by have hi := i.isLt;omega⟩)

theorem zero_bytes (ram : Word → BitVec 8) (p : Word) (htop : p.toNat+271<2^32) :
    ∀ i : Fin 271, HeadZero271.memory ram p (p+BitVec.ofNat 32 i.val)=0#8 := by
  intro i
  have hi := i.isLt
  by_cases first : i.val<268
  · unfold HeadZero271.memory HeadZeroTail3.memory
    rw [show (p+268#32)+1#32=p+269#32 by rw [BitVec.add_assoc];rfl,
      show (p+268#32)+2#32=p+270#32 by rw [BitVec.add_assoc];rfl]
    rw [StoreBytes.frame _ _ _ _ .b (by
      intro j;have hj : j.val<1 := j.isLt;have z : j.val=0 := by omega
      simpa only [z,BitVec.add_zero] using WordZero.offset_ne p i.val 270 (by omega) (by decide) (by omega))]
    rw [StoreBytes.frame _ _ _ _ .b (by
      intro j;have hj : j.val<1 := j.isLt;have z : j.val=0 := by omega
      simpa only [z,BitVec.add_zero] using WordZero.offset_ne p i.val 269 (by omega) (by decide) (by omega))]
    rw [StoreBytes.frame _ _ _ _ .b (by
      intro j;have hj : j.val<1 := j.isLt;have z : j.val=0 := by omega
      simpa only [z,BitVec.add_zero] using WordZero.offset_ne p i.val 268 (by omega) (by decide) (by omega))]
    exact WordZero.zero_bytes ram p 67 (by omega) ⟨i.val,first⟩
  · have cases : i.val=268 ∨ i.val=269 ∨ i.val=270 := by omega
    rcases cases with h|h|h
    all_goals simp [h,HeadZero271.memory,HeadZeroTail3.memory,ramWrite,ramPut,byteOf,BitVec.add_assoc,BitVec.add_right_inj,BitVec.self_eq_add_right]

theorem region (ram : Word → BitVec 8) (sp : Word) (off len : Nat)
    (hb : off+len≤4294967296) (hs : off+len≤56 ∨ 327≤off) :
    ViewFrame.Region ram (HeadZero271.memory ram (sp+56#32)) (sp+BitVec.ofNat 32 off) len := by
  intro i
  have hi := i.isLt
  apply frame
  intro j
  exact FrameOffsets.ne sp off 56 i.val j.val (by omega) (by have hj := j.isLt;omega) (by have hj := j.isLt;omega)
end E5R.Thermostat.HeadZeroMemory
