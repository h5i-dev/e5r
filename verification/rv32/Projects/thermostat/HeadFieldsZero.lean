import Projects.thermostat.HeadFieldsCall
import Projects.thermostat.HeadZeroMemory
import Projects.thermostat.HeadSaved
import Projects.thermostat.HeadSavedTail
namespace E5R.Thermostat.HeadFieldsZero
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp : Word) := HeadZero271.memory ram (sp+56#32)

/-- Real header initializer call, complete 271-byte memset and return.
    The array lies below all saved ABI words and outside App/RX/metadata. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word)
    (hp : c.pc=0x80002f0e#32) (h2 : c.get 2=sp) (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) :
    ∃ d, Quiet.Steps B img 236 ⟨c,ram⟩ ⟨d,memory ram sp⟩ ∧ d.pc=0x80002f1e#32 ∧ d.get 2=sp ∧
      (∀ r : Reg, r≠1 → r≠10 → r≠11 → r≠12 → r≠13 → r≠14 → r≠15 → r≠16 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,call,pc,ptr,len,zero,ra,frame,csr⟩ := HeadFieldsCall.contract B c ram sp h2 hp
  have block : Memory.Block B (sp+56#32) 271 := Memory.sub_block hm (off := 56) (by decide) (by decide)
  have align : (sp+56#32).toNat%4=0 := Memory.word_aligned sp 14 ha
  have bound : sp.toNat+5312≤4294967296 := hm.2.2
  have top : (sp+56#32).toNat+271<2^32 := by
    rw [WordZero.add_nat sp 56 (by omega)]
    omega
  obtain ⟨d,clear,endPC,frame2,csr2⟩ := HeadZero271.contract B a ram (sp+56#32) pc ptr zero len align block top
  have source (r : Reg) (h1 : r≠1) (h10 : r≠10) (h11 : r≠11) (h12 : r≠12) (h13 : r≠13) (h14 : r≠14) (h15 : r≠15) (h16 : r≠16) : d.get r=c.get r :=
    (frame2 r h12 h13 h14 h15 h16).trans (frame r h10 h12 h11 h1)
  refine ⟨d,call.trans clear,?_,?_,source,csr2.trans csr⟩
  · exact endPC.trans (by rw [ra];decide +kernel)
  · exact (source 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2

theorem zero_bytes (B : Board) (ram : Word → BitVec 8) (sp : Word) (hm : Memory.Block B sp 5312) :
    ∀ i : Fin 271, memory ram sp (sp+56#32+BitVec.ofNat 32 i.val)=0#8 := by
  have bound : sp.toNat+5312≤4294967296 := hm.2.2
  have top : (sp+56#32).toNat+271<2^32 := by
    rw [WordZero.add_nat sp 56 (by omega)]
    omega
  exact HeadZeroMemory.zero_bytes ram (sp+56#32) top

theorem region (ram : Word → BitVec 8) (sp : Word) (off len : Nat)
    (hb : off+len≤4294967296) (hs : off+len≤56 ∨ 327≤off) :
    ViewFrame.Region ram (memory ram sp) (sp+BitVec.ofNat 32 off) len := HeadZeroMemory.region ram sp off len hb hs

theorem word_frame (ram : Word → BitVec 8) (sp : Word) (off : Nat)
    (hb : off+4≤4294967296) (hs : off+4≤56 ∨ 327≤off) :
    ramRead (memory ram sp) (sp+BitVec.ofNat 32 off) .w=ramRead ram (sp+BitVec.ofNat 32 off) .w := by
  simpa only [BitVec.add_zero] using ViewFrame.word (region ram sp off 4 hb hs) 0 (by decide)
theorem saved {ram sp values} (h : HeadSaved.At ram sp values) :
    HeadSaved.At (memory ram sp) sp values :=
  HeadSavedTail.preserve h (region ram sp 332 52 (by decide) (by decide))

end E5R.Thermostat.HeadFieldsZero
