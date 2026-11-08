import Projects.thermostat.HeadHeaderCommitMemory
namespace E5R.Thermostat.HeadHeaderCommitView
open E5R E5R.Thermostat HttpRequestSpec

/-- All old headers, content-length words and flags retain their values; the
    five actual ordered stores append exactly the new represented field. -/
theorem append {ram : Word → BitVec 8} {sp : Word} {f : Fields} (entry : Field)
    (view : HeadFieldsView.At ram sp f) (room : f.headers.length<16) :
    HeadFieldsView.At (HeadHeaderCommitMemory.memory ram sp f.headers.length entry) sp {f with headers := f.headers++[entry]} := by
  let n := f.headers.length
  let after := HeadHeaderCommitMemory.memory ram sp n entry
  have oldRegion : ViewFrame.Region ram after (sp+56#32) (16*n) :=
    HeadHeaderCommitMemory.region ram sp n entry 56 (16*n) room (by omega) (by omega) (by omega)
  have word (off : Nat) (ho : off+4≤16*n) := ViewFrame.word oldRegion off ho
  have clRegion := HeadHeaderCommitMemory.region ram sp n entry 312 8 room (by decide) (by omega) (by decide)
  have flags := HeadHeaderCommitMemory.region ram sp n entry 324 3 room (by decide) (by omega) (by decide)
  have low : ramRead after (sp+312#32) .w=ramRead ram (sp+312#32) .w := by
    simpa only [BitVec.add_zero] using ViewFrame.word clRegion 0 (by decide)
  have high : ramRead after (sp+316#32) .w=ramRead ram (sp+316#32) .w := by
    have a : (sp+312#32)+4#32=sp+316#32 := by rw [BitVec.add_assoc];rfl
    simpa only [a] using ViewFrame.word clRegion 4 (by decide)
  have host : after (sp+324#32)=ram (sp+324#32) := by simpa only [BitVec.add_zero] using flags ⟨0,by decide⟩
  have hasCl : after (sp+325#32)=ram (sp+325#32) := by
    have a : (sp+324#32)+1#32=sp+325#32 := by rw [BitVec.add_assoc];rfl
    simpa only [a] using flags ⟨1,by decide⟩
  have te : after (sp+326#32)=ram (sp+326#32) := by
    have a : (sp+324#32)+2#32=sp+326#32 := by rw [BitVec.add_assoc];rfl
    simpa only [a] using flags ⟨2,by decide⟩
  refine ⟨?_,?_,?_,low.trans view.clLow,high.trans view.clHigh,host.trans view.host,hasCl.trans view.hasCl,te.trans view.te⟩
  · simp only [List.length_append,List.length_cons,List.length_nil]
    omega
  · simpa only [List.length_append,List.length_cons,List.length_nil] using HeadHeaderCommitMemory.count_word ram sp n entry
  · intro i
    by_cases old : i.val<n
    · let k : Fin f.headers.length := ⟨i.val,old⟩
      have item : (f.headers++[entry])[i]=f.headers[k] := by
        change (f.headers++[entry])[i.val]=f.headers[i.val]
        exact List.getElem_append_left old
      rw [item]
      have a4 : (sp+56#32)+BitVec.ofNat 32 (4+16*i.val)=(sp+60#32)+BitVec.ofNat 32 (16*i.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc,show (sp+56#32)+4#32=sp+60#32 by rw [BitVec.add_assoc];rfl]
      have a8 : (sp+56#32)+BitVec.ofNat 32 (8+16*i.val)=(sp+64#32)+BitVec.ofNat 32 (16*i.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc,show (sp+56#32)+8#32=sp+64#32 by rw [BitVec.add_assoc];rfl]
      have a12 : (sp+56#32)+BitVec.ofNat 32 (12+16*i.val)=(sp+68#32)+BitVec.ofNat 32 (16*i.val) := by
        rw [BitVec.ofNat_add,←BitVec.add_assoc,show (sp+56#32)+12#32=sp+68#32 by rw [BitVec.add_assoc];rfl]
      refine ⟨(word (16*i.val) (by omega)).trans (view.headers k).1,?_,?_,?_⟩
      · have w : ramRead after (sp+60#32+BitVec.ofNat 32 (16*i.val)) .w=ramRead ram (sp+60#32+BitVec.ofNat 32 (16*i.val)) .w := by
          simpa only [a4] using word (4+16*i.val) (by omega)
        exact w.trans (view.headers k).2.1
      · have w : ramRead after (sp+64#32+BitVec.ofNat 32 (16*i.val)) .w=ramRead ram (sp+64#32+BitVec.ofNat 32 (16*i.val)) .w := by
          simpa only [a8] using word (8+16*i.val) (by omega)
        exact w.trans (view.headers k).2.2.1
      · have w : ramRead after (sp+68#32+BitVec.ofNat 32 (16*i.val)) .w=ramRead ram (sp+68#32+BitVec.ofNat 32 (16*i.val)) .w := by
          simpa only [a12] using word (12+16*i.val) (by omega)
        exact w.trans (view.headers k).2.2.2
    · have ilt : i.val<n+1 := by simpa only [List.length_append,List.length_cons,List.length_nil] using i.isLt
      have last : i.val=n := by omega
      have item : (f.headers++[entry])[i]=entry := by
        change (f.headers++[entry])[i.val]=entry
        rw [List.getElem_append_right (by omega)]
        simp [n,last]
      rw [item]
      exact ⟨by simpa only [last,BitVec.ofNat_add,BitVec.add_assoc] using HeadHeaderCommitMemory.new_ns ram sp n entry room,
        by simpa only [last,BitVec.ofNat_add,BitVec.add_assoc] using HeadHeaderCommitMemory.new_ne ram sp n entry room,
        by simpa only [last,BitVec.ofNat_add,BitVec.add_assoc] using HeadHeaderCommitMemory.new_vs ram sp n entry room,
        by simpa only [last,BitVec.ofNat_add,BitVec.add_assoc] using HeadHeaderCommitMemory.new_ve ram sp n entry room⟩
end E5R.Thermostat.HeadHeaderCommitView
