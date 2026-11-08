import Projects.thermostat.HeadHostFlag
import Projects.thermostat.HeadSavedTail
namespace E5R.Thermostat.HeadHostFlagMemory
open E5R E5R.Thermostat HttpRequestSpec

theorem region (ram : Word → BitVec 8) (sp : Word) (off len : Nat)
    (hb : off+len≤4294967296) (hs : off+len≤324 ∨ 325≤off) :
    ViewFrame.Region ram (HeadHostFlagStore.memory ram sp) (sp+BitVec.ofNat 32 off) len := by
  intro i
  unfold HeadHostFlagStore.memory
  exact StoreBytes.frame _ _ _ _ .b (fun j => FrameOffsets.ne sp off 324 i.val j.val
    (by have hi := i.isLt;omega) (by have hj : j.val<1 := j.isLt;omega) (by have hi := i.isLt;have hj : j.val<1 := j.isLt;omega))

theorem host (ram : Word → BitVec 8) (sp : Word) :
    HeadHostFlagStore.memory ram sp (sp+324#32)=HeadFieldsView.flag true := by
  simp [HeadHostFlagStore.memory,HeadFieldsView.flag,ramWrite,ramPut,byteOf]

theorem saved {ram sp values} (h : HeadSaved.At ram sp values) :
    HeadSaved.At (HeadHostFlagStore.memory ram sp) sp values :=
  HeadSavedTail.preserve h (region ram sp 332 52 (by decide) (by decide))

/-- The actual one-byte store changes only the represented Host flag. The
    header array, count, content length and other flags remain the same. -/
theorem fields {before : Word → BitVec 8} {sp : Word} {f : Fields} (h : HeadFieldsView.At before sp f) :
    HeadFieldsView.At (HeadHostFlagStore.memory before sp) sp {f with host := true} := by
  let after := HeadHostFlagStore.memory before sp
  have frame : ViewFrame.Region before after (sp+56#32) 268 := region before sp 56 268 (by decide) (by decide)
  have word (off : Nat) (ho : off+4≤268) := ViewFrame.word frame off ho
  have atCount : ramRead after (sp+320#32) .w=ramRead before (sp+320#32) .w := by
    simpa only [show (sp+56#32)+264#32=sp+320#32 by rw [BitVec.add_assoc];rfl] using word 264 (by decide)
  have atLow : ramRead after (sp+312#32) .w=ramRead before (sp+312#32) .w := by
    simpa only [show (sp+56#32)+256#32=sp+312#32 by rw [BitVec.add_assoc];rfl] using word 256 (by decide)
  have atHigh : ramRead after (sp+316#32) .w=ramRead before (sp+316#32) .w := by
    simpa only [show (sp+56#32)+260#32=sp+316#32 by rw [BitVec.add_assoc];rfl] using word 260 (by decide)
  refine ⟨h.count_bound,atCount.trans h.count,?_,atLow.trans h.clLow,atHigh.trans h.clHigh,?_,?_,?_⟩
  · intro i
    have bound : i.val<16 := Nat.lt_of_lt_of_le i.isLt h.count_bound
    have a4 : (sp+56#32)+BitVec.ofNat 32 (4+16*i.val)=(sp+60#32)+BitVec.ofNat 32 (16*i.val) := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,show (sp+56#32)+4#32=sp+60#32 by rw [BitVec.add_assoc];rfl]
    have a8 : (sp+56#32)+BitVec.ofNat 32 (8+16*i.val)=(sp+64#32)+BitVec.ofNat 32 (16*i.val) := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,show (sp+56#32)+8#32=sp+64#32 by rw [BitVec.add_assoc];rfl]
    have a12 : (sp+56#32)+BitVec.ofNat 32 (12+16*i.val)=(sp+68#32)+BitVec.ofNat 32 (16*i.val) := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,show (sp+56#32)+12#32=sp+68#32 by rw [BitVec.add_assoc];rfl]
    refine ⟨(word (16*i.val) (by omega)).trans (h.headers i).1,?_,?_,?_⟩
    · have w : ramRead after (sp+60#32+BitVec.ofNat 32 (16*i.val)) .w=ramRead before (sp+60#32+BitVec.ofNat 32 (16*i.val)) .w := by
        simpa only [a4] using word (4+16*i.val) (by omega)
      exact w.trans (h.headers i).2.1
    · have w : ramRead after (sp+64#32+BitVec.ofNat 32 (16*i.val)) .w=ramRead before (sp+64#32+BitVec.ofNat 32 (16*i.val)) .w := by
        simpa only [a8] using word (8+16*i.val) (by omega)
      exact w.trans (h.headers i).2.2.1
    · have w : ramRead after (sp+68#32+BitVec.ofNat 32 (16*i.val)) .w=ramRead before (sp+68#32+BitVec.ofNat 32 (16*i.val)) .w := by
        simpa only [a12] using word (12+16*i.val) (by omega)
      exact w.trans (h.headers i).2.2.2
  · exact host before sp
  · have b := region before sp 325 2 (by decide) (by decide) ⟨0,by decide⟩
    have b0 : after (sp+325#32)=before (sp+325#32) := by simpa only [BitVec.add_zero] using b
    exact b0.trans h.hasCl
  · have b := region before sp 325 2 (by decide) (by decide) ⟨1,by decide⟩
    have a : (sp+325#32)+1#32=sp+326#32 := by rw [BitVec.add_assoc];rfl
    simpa only [a] using b.trans (by simpa only [a] using h.te)
end E5R.Thermostat.HeadHostFlagMemory
