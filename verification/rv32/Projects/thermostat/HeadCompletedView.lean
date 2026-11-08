import Projects.thermostat.HeadDoneCommit
import Projects.thermostat.HeadDoneTag
import Projects.thermostat.HeadFieldsView
namespace E5R.Thermostat.HeadCompletedView
open E5R E5R.Thermostat HttpRequestSpec

def framingTag : Framing → Word
  | .empty => 0#32
  | .length _ => 1#32
  | .chunked => 2#32

/-- The complete successful parse_head object, including the actual copied
    header array and the framing payload. Unselected payload bytes are ignored. -/
structure At (ram : Word → BitVec 8) (dst : Word) (h : Head) : Prop where
  tag : ramRead ram dst .w=framingTag h.framing
  padding : ramRead ram (dst+4#32) .w=0#32
  framing : ∀ n, h.framing=.length n → ramRead ram (dst+8#32) .w=BitVec.ofNat 32 n ∧
    ramRead ram (dst+12#32) .w=BitVec.ofNat 32 (n/4294967296)
  methodStart : ramRead ram (dst+16#32) .w=BitVec.ofNat 32 h.method.1
  methodEnd : ramRead ram (dst+20#32) .w=BitVec.ofNat 32 h.method.2
  targetStart : ramRead ram (dst+24#32) .w=BitVec.ofNat 32 h.target.1
  targetEnd : ramRead ram (dst+28#32) .w=BitVec.ofNat 32 h.target.2
  count_bound : h.headers.length≤16
  count : ramRead ram (dst+288#32) .w=BitVec.ofNat 32 h.headers.length
  headers : ∀ i : Fin h.headers.length,
    ramRead ram ((dst+32#32)+BitVec.ofNat 32 (16*i.val)) .w=BitVec.ofNat 32 h.headers[i].ns ∧
    ramRead ram ((dst+36#32)+BitVec.ofNat 32 (16*i.val)) .w=BitVec.ofNat 32 h.headers[i].ne ∧
    ramRead ram ((dst+40#32)+BitVec.ofNat 32 (16*i.val)) .w=BitVec.ofNat 32 h.headers[i].vs ∧
    ramRead ram ((dst+44#32)+BitVec.ofNat 32 (16*i.val)) .w=BitVec.ofNat 32 h.headers[i].ve
  length : ramRead ram (dst+292#32) .w=BitVec.ofNat 32 h.len
  version : ram (dst+296#32)=BitVec.ofNat 8 h.minor

def head (method targetStart targetEnd len minor : Nat) (f : Fields) : Head :=
  ⟨(0,method),(targetStart,targetEnd),minor,f.headers,len,
    if f.te then .chunked else if f.hasCl then .length f.cl else .empty⟩

def memory (ram : Word → BitVec 8) (sp : Word) (method targetStart targetEnd len minor : Nat) (f : Fields) :=
  HeadDoneCommit.memory ram sp (HeadDoneTag.tag f.te f.hasCl) (BitVec.ofNat 32 f.cl) (BitVec.ofNat 32 (f.cl/4294967296))
    (BitVec.ofNat 32 method) (BitVec.ofNat 32 targetStart) (BitVec.ofNat 32 targetEnd) (BitVec.ofNat 32 f.headers.length) (BitVec.ofNat 32 len) (BitVec.ofNat 32 minor)

theorem stored (B : Board) (ram : Word → BitVec 8) (sp : Word) (method targetStart targetEnd len minor : Nat) (f : Fields)
    (view : HeadFieldsView.At ram sp f) (stack : Memory.Block B sp 5312) (version : minor≤1) :
    At (memory ram sp method targetStart targetEnd len minor f) (sp+4904#32) (head method targetStart targetEnd len minor f) := by
  let copied := HeadCopyHeader256.memory ram sp
  let after := memory ram sp method targetStart targetEnd len minor f
  have offset (a b : Nat) : (sp+BitVec.ofNat 32 a)+BitVec.ofNat 32 b=sp+BitVec.ofNat 32 (a+b) := by rw [BitVec.add_assoc,←BitVec.ofNat_add]
  have tag : framingTag (head method targetStart targetEnd len minor f).framing=HeadDoneTag.tag f.te f.hasCl := by
    cases ht : f.te <;> cases hc : f.hasCl <;> simp only [head,ht,hc,Bool.false_eq_true,ite_false,ite_true,framingTag,HeadDoneTag.tag]
  have headerFrame : ViewFrame.Region copied after (sp+4936#32) 256 :=
    HeadDoneMemory.region copied sp _ _ _ _ _ _ _ _ _ 4936 256 (by decide) (Or.inr (by decide)) (Or.inl (by decide))
  have word (k : Nat) (bound : k<64) :
      ramRead after ((sp+4936#32)+BitVec.ofNat 32 (4*k)) .w=ramRead ram ((sp+56#32)+BitVec.ofNat 32 (4*k)) .w :=
    (ViewFrame.word headerFrame (4*k) (by omega)).trans (HeadCopyHeader256.copied ram sp ⟨k,bound⟩ stack)
  have rawTag := HeadDoneMemory.tag_word copied sp (HeadDoneTag.tag f.te f.hasCl) (BitVec.ofNat 32 f.cl) (BitVec.ofNat 32 (f.cl/4294967296)) (BitVec.ofNat 32 method) (BitVec.ofNat 32 targetStart) (BitVec.ofNat 32 targetEnd) (BitVec.ofNat 32 f.headers.length) (BitVec.ofNat 32 len) (BitVec.ofNat 32 minor)
  refine ⟨rawTag.trans tag.symm,?_,?_,?_,?_,?_,?_,view.count_bound,?_,?_,?_,?_⟩
  · simpa only [offset,Nat.reduceAdd,head,memory,HeadDoneCommit.memory,copied,after] using HeadDoneMemory.pad_word copied sp _ _ _ _ _ _ _ _ _
  · intro n selected
    have payload : n=f.cl := by
      dsimp only [head] at selected
      cases ht : f.te <;> cases hc : f.hasCl <;> simp only [ht,hc,Bool.false_eq_true,ite_false,ite_true] at selected
      · cases selected
      · cases selected;rfl
      · cases selected
      · cases selected
    subst n
    exact ⟨by simpa only [offset,Nat.reduceAdd,head,memory,HeadDoneCommit.memory,copied,after] using HeadDoneMemory.low_word copied sp _ _ _ _ _ _ _ _ _,by simpa only [offset,Nat.reduceAdd,head,memory,HeadDoneCommit.memory,copied,after] using HeadDoneMemory.high_word copied sp _ _ _ _ _ _ _ _ _⟩
  · simpa only [offset,Nat.reduceAdd,head,memory,HeadDoneCommit.memory,copied,after] using HeadDoneMemory.methodStart_word copied sp _ _ _ _ _ _ _ _ _
  · simpa only [offset,Nat.reduceAdd,head,memory,HeadDoneCommit.memory,copied,after] using HeadDoneMemory.methodEnd_word copied sp _ _ _ _ _ _ _ _ _
  · simpa only [offset,Nat.reduceAdd,head,memory,HeadDoneCommit.memory,copied,after] using HeadDoneMemory.targetStart_word copied sp _ _ _ _ _ _ _ _ _
  · simpa only [offset,Nat.reduceAdd,head,memory,HeadDoneCommit.memory,copied,after] using HeadDoneMemory.targetEnd_word copied sp _ _ _ _ _ _ _ _ _
  · simpa only [offset,Nat.reduceAdd,head,memory,HeadDoneCommit.memory,copied,after] using HeadDoneMemory.count_word copied sp _ _ _ _ _ _ _ _ _
  · intro i
    have bound : i.val<16 := Nat.lt_of_lt_of_le i.isLt view.count_bound
    have shifted (p : Word) (q : Nat) : p+BitVec.ofNat 32 (4*(4*i.val+q))=(p+BitVec.ofNat 32 (4*q))+BitVec.ofNat 32 (16*i.val) := by
      rw [BitVec.add_assoc,←BitVec.ofNat_add,show 4*q+16*i.val=4*(4*i.val+q) by omega]
    refine ⟨?_,?_,?_,?_⟩
    · have h := word (4*i.val) (by omega)
      have addr (p : Word) : p+BitVec.ofNat 32 (4*(4*i.val))=p+BitVec.ofNat 32 (16*i.val) := by congr 2;omega
      simpa only [addr,offset,Nat.reduceAdd,head,memory,HeadDoneCommit.memory,copied,after] using h.trans (by simpa only [addr] using (view.headers i).1)
    · have h := word (4*i.val+1) (by omega)
      rw [shifted,shifted,show (sp+4936#32)+4#32=sp+4940#32 from offset 4936 4,show (sp+56#32)+4#32=sp+60#32 from offset 56 4] at h
      simpa only [offset,Nat.reduceAdd,head,memory,HeadDoneCommit.memory,copied,after] using h.trans (view.headers i).2.1
    · have h := word (4*i.val+2) (by omega)
      rw [shifted,shifted,show (sp+4936#32)+8#32=sp+4944#32 from offset 4936 8,show (sp+56#32)+8#32=sp+64#32 from offset 56 8] at h
      simpa only [offset,Nat.reduceAdd,head,memory,HeadDoneCommit.memory,copied,after] using h.trans (view.headers i).2.2.1
    · have h := word (4*i.val+3) (by omega)
      rw [shifted,shifted,show (sp+4936#32)+12#32=sp+4948#32 from offset 4936 12,show (sp+56#32)+12#32=sp+68#32 from offset 56 12] at h
      simpa only [offset,Nat.reduceAdd,head,memory,HeadDoneCommit.memory,copied,after] using h.trans (view.headers i).2.2.2
  · simpa only [offset,Nat.reduceAdd,head,memory,HeadDoneCommit.memory,copied,after] using HeadDoneMemory.length_word copied sp _ _ _ _ _ _ _ _ _
  · have h := HeadDoneMemory.minor_byte copied sp (HeadDoneTag.tag f.te f.hasCl) (BitVec.ofNat 32 f.cl) (BitVec.ofNat 32 (f.cl/4294967296)) (BitVec.ofNat 32 method) (BitVec.ofNat 32 targetStart) (BitVec.ofNat 32 targetEnd) (BitVec.ofNat 32 f.headers.length) (BitVec.ofNat 32 len) (BitVec.ofNat 32 minor)
    have value : byteOf (BitVec.ofNat 32 minor) 0=BitVec.ofNat 8 minor := by
      apply BitVec.eq_of_toNat_eq
      simp only [byteOf,BitVec.toNat_ofNat,Nat.pow_zero,Nat.div_one]
      omega
    simpa only [offset,Nat.reduceAdd,head,value,memory,HeadDoneCommit.memory,copied,after] using h
end E5R.Thermostat.HeadCompletedView
