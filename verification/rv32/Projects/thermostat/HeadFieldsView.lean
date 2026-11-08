import Projects.thermostat.HeadFieldsZero
import Projects.thermostat.HttpRequestSpec
namespace E5R.Thermostat.HeadFieldsView
open E5R E5R.Thermostat HttpRequestSpec

def flag (b : Bool) : BitVec 8 := if b then 1#8 else 0#8

/-- Observed scratch representation at stable header-loop boundaries.
    Sequential stores inside an update need not satisfy this representation. -/
structure At (ram : Word → BitVec 8) (sp : Word) (f : Fields) : Prop where
  count_bound : f.headers.length≤16
  count : ramRead ram (sp+320#32) .w=BitVec.ofNat 32 f.headers.length
  headers : ∀ i : Fin f.headers.length,
    ramRead ram (sp+56#32+BitVec.ofNat 32 (16*i.val)) .w=BitVec.ofNat 32 f.headers[i].ns ∧
    ramRead ram (sp+60#32+BitVec.ofNat 32 (16*i.val)) .w=BitVec.ofNat 32 f.headers[i].ne ∧
    ramRead ram (sp+64#32+BitVec.ofNat 32 (16*i.val)) .w=BitVec.ofNat 32 f.headers[i].vs ∧
    ramRead ram (sp+68#32+BitVec.ofNat 32 (16*i.val)) .w=BitVec.ofNat 32 f.headers[i].ve
  clLow : ramRead ram (sp+312#32) .w=BitVec.ofNat 32 f.cl
  clHigh : ramRead ram (sp+316#32) .w=BitVec.ofNat 32 (f.cl/4294967296)
  host : ram (sp+324#32)=flag f.host
  hasCl : ram (sp+325#32)=flag f.hasCl
  te : ram (sp+326#32)=flag f.te

/-- Preserve the stable fields representation when all 271 representation
    bytes retain their values. This does not assert an update is atomic. -/
theorem preserve {before after : Word → BitVec 8} {sp : Word} {f : Fields}
    (h : At before sp f) (frame : ViewFrame.Region before after (sp+56#32) 271) : At after sp f := by
  have word (off : Nat) (ho : off+4≤271) := ViewFrame.word frame off ho
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
  · have b := frame ⟨268,by decide⟩
    have a : (sp+56#32)+268#32=sp+324#32 := by rw [BitVec.add_assoc];rfl
    simpa only [a] using b.trans (by simpa only [a] using h.host)
  · have b := frame ⟨269,by decide⟩
    have a : (sp+56#32)+269#32=sp+325#32 := by rw [BitVec.add_assoc];rfl
    simpa only [a] using b.trans (by simpa only [a] using h.hasCl)
  · have b := frame ⟨270,by decide⟩
    have a : (sp+56#32)+270#32=sp+326#32 := by rw [BitVec.add_assoc];rfl
    simpa only [a] using b.trans (by simpa only [a] using h.te)

/-- No prior scratch contents are assumed: the real memset establishes every
    empty-fields flag, count and u64 content length in actual RAM. -/
theorem initial (B : Board) (ram : Word → BitVec 8) (sp : Word) (hm : Memory.Block B sp 5312) :
    At (HeadFieldsZero.memory ram sp) sp Fields.empty := by
  have bytes := HeadFieldsZero.zero_bytes B ram sp hm
  have region : ViewFrame.Region (fun _ => 0#8) (HeadFieldsZero.memory ram sp) (sp+56#32) 271 := bytes
  have word (off : Nat) (ho : off+4≤271) :
      ramRead (HeadFieldsZero.memory ram sp) ((sp+56#32)+BitVec.ofNat 32 off) .w=0#32 := by
    exact ViewFrame.word region off ho
  refine ⟨by decide,?_,fun i => Fin.elim0 i,?_,?_,?_,?_,?_⟩
  · simpa only [Fields.empty,List.length_nil,flag,Bool.false_eq_true,ite_false,Nat.zero_div,show (sp+56#32)+264#32=sp+320#32 by rw [BitVec.add_assoc];rfl] using word 264 (by decide)
  · simpa only [Fields.empty,List.length_nil,flag,Bool.false_eq_true,ite_false,Nat.zero_div,show (sp+56#32)+256#32=sp+312#32 by rw [BitVec.add_assoc];rfl] using word 256 (by decide)
  · simpa only [Fields.empty,List.length_nil,flag,Bool.false_eq_true,ite_false,Nat.zero_div,show (sp+56#32)+260#32=sp+316#32 by rw [BitVec.add_assoc];rfl] using word 260 (by decide)
  · simpa only [Fields.empty,List.length_nil,flag,Bool.false_eq_true,ite_false,Nat.zero_div,show (sp+56#32)+268#32=sp+324#32 by rw [BitVec.add_assoc];rfl] using bytes ⟨268,by decide⟩
  · simpa only [Fields.empty,List.length_nil,flag,Bool.false_eq_true,ite_false,Nat.zero_div,show (sp+56#32)+269#32=sp+325#32 by rw [BitVec.add_assoc];rfl] using bytes ⟨269,by decide⟩
  · simpa only [Fields.empty,List.length_nil,flag,Bool.false_eq_true,ite_false,Nat.zero_div,show (sp+56#32)+270#32=sp+326#32 by rw [BitVec.add_assoc];rfl] using bytes ⟨270,by decide⟩
end E5R.Thermostat.HeadFieldsView
