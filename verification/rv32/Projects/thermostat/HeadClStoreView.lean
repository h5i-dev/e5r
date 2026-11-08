import Projects.thermostat.HeadClStoreMemory
namespace E5R.Thermostat.HeadClStoreView
open E5R E5R.Thermostat HttpRequestSpec

theorem fields {before : Word → BitVec 8} {sp : Word} {f : Fields} (h : HeadFieldsView.At before sp f)
    (value : Nat) (bound : value≤1024) :
    HeadFieldsView.At (HeadClStoreRaw.memory before sp (BitVec.ofNat 32 value)) sp {f with hasCl := true, cl := value} := by
  let after := HeadClStoreRaw.memory before sp (BitVec.ofNat 32 value)
  have frame : ViewFrame.Region before after (sp+56#32) 256 := HeadClStoreMemory.region before sp _ 56 256 (by decide) (by decide) (by decide)
  have word (off : Nat) (ho : off+4≤256) := ViewFrame.word frame off ho
  have atCount : ramRead after (sp+320#32) .w=ramRead before (sp+320#32) .w := by
    have region := HeadClStoreMemory.region before sp (BitVec.ofNat 32 value) 320 4 (by decide) (by decide) (by decide)
    simpa only [BitVec.add_zero] using ViewFrame.word region 0 (by decide)
  have atLow : ramRead after (sp+312#32) .w=BitVec.ofNat 32 value := HeadClStoreMemory.low_word before sp _
  have atHigh : ramRead after (sp+316#32) .w=BitVec.ofNat 32 (value/4294967296) := by
    rw [Nat.div_eq_of_lt (by omega)]
    exact HeadClStoreMemory.high_word before sp _
  refine ⟨h.count_bound,atCount.trans h.count,?_,atLow,atHigh,?_,?_,?_⟩
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
  · have b := HeadClStoreMemory.region before sp (BitVec.ofNat 32 value) 324 1 (by decide) (by decide) (by decide) ⟨0,by decide⟩
    have b0 : after (sp+324#32)=before (sp+324#32) := by simpa only [BitVec.add_zero] using b
    exact b0.trans h.host
  · exact HeadClStoreMemory.hasCl before sp _
  · have b := HeadClStoreMemory.region before sp (BitVec.ofNat 32 value) 326 1 (by decide) (by decide) (by decide) ⟨0,by decide⟩
    have b0 : after (sp+326#32)=before (sp+326#32) := by simpa only [BitVec.add_zero] using b
    exact b0.trans h.te
end E5R.Thermostat.HeadClStoreView
