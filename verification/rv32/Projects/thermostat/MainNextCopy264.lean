import Projects.thermostat.MainRamCopy
import Projects.thermostat.MainRamCopyByte
import Projects.thermostat.MainCopyView
namespace E5R.Thermostat.MainNextCopy264
open E5R E5R.Thermostat

def source (sp : Word) (off : Nat) := sp+BitVec.ofNat 32 off

def words (ram : Word → BitVec 8) (sp : Word) (off : Nat) := HeadRamCopyMemory.snapshot ram (source sp off) 66

def memory (ram : Word → BitVec 8) (sp : Word) (off : Nat) := AlignedCopyLoop.writes ram (sp+4904#32) (words ram sp off)

/-- Real aligned264-byte memcpy used by both fixed-length and empty Next
    construction. The source is actual RAM, with either emitted source offset. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (off : Nat)
    (selected : off=3352 ∨ off=4552)
    (hp : c.pc=0x80005182#32) (h2 : c.get 2=sp) (h10 : c.get 10=sp+4904#32)
    (h11 : c.get 11=source sp off) (h12 : c.get 12=264#32)
    (stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0) :
    ∃ d, Quiet.Steps B img 354 ⟨c,ram⟩ ⟨d,memory ram sp off⟩ ∧ FormatCursor.Returned c d ∧ d.get 10=sp+4904#32 := by
  have offBound : off+264≤4904 := by rcases selected with h|h <;> omega
  have bound := stack.2.2
  have srcNat := WordZero.add_nat sp off (by omega)
  have dstNat := WordZero.add_nat sp 4904 (by omega)
  have srcAligned : (source sp off).toNat%4=0 := by
    rcases selected with h|h <;> subst off
    · exact Memory.word_aligned sp 838 aligned
    · exact Memory.word_aligned sp 1138 aligned
  have sourceBlock : Memory.Block B (source sp off) 264 := Memory.sub_block stack (off := off) (m := 264) (by omega) (by omega)
  have destination : Memory.Block B (sp+4904#32) 264 := Memory.sub_block stack (off := 4904) (m := 264) (by decide) (by decide)
  have hs := HeadRamCopyMemory.source B ram (source sp off) 66 srcAligned sourceBlock
  have hsp : c.get 2=(sp+0xfffffff0#32)+16#32 := by rw [h2,BitVec.add_assoc,show 0xfffffff0#32+16#32=0#32 by decide +kernel,BitVec.add_zero]
  obtain ⟨d,steps,ret,d10,_,_⟩ := MainRamCopy.contract B c ram (sp+0xfffffff0#32) (source sp off) (sp+4904#32) (words ram sp off)
    hp hsp h10 h11 (by simpa only [words,HeadRamCopyMemory.snapshot_length] using h12)
    (by simp only [words,HeadRamCopyMemory.snapshot_length];decide) hs
    (by apply Or.inl;rw [words,HeadRamCopyMemory.snapshot_length,source,srcNat,dstNat];omega)
    (Memory.word_aligned sp 1226 aligned) (by simpa only [words,HeadRamCopyMemory.snapshot_length] using destination)
    (by rw [words,HeadRamCopyMemory.snapshot_length,dstNat];omega)
    (by simp only [words,HeadRamCopyMemory.snapshot_length];decide +kernel)
  exact ⟨d,by simpa only [memory,words,HeadRamCopyMemory.snapshot_length,show 24+5*66=354 from rfl] using steps,ret,d10⟩

theorem bytes (ram : Word → BitVec 8) (sp : Word) (off : Nat) (stack : Memory.Block B sp 5232) :
    MainCopyView.At ram (memory ram sp off) (source sp off) (sp+4904#32) 264 := by
  intro i
  apply MainRamCopyByte.copied
  have bound := stack.2.2
  rw [WordZero.add_nat sp 4904 (by omega)]
  omega

theorem frame (ram : Word → BitVec 8) (sp : Word) (off region size : Nat) (bound : region+size≤5232)
    (apart : region+size≤4904 ∨ 5168≤region) : ViewFrame.Region ram (memory ram sp off) (sp+BitVec.ofNat 32 region) size := by
  intro i
  apply AlignedCopyLoop.frame
  intro j eq
  have hi := i.isLt
  have hj : j.val<264 := by simpa only [words,HeadRamCopyMemory.snapshot_length] using j.isLt
  rw [BitVec.add_assoc,BitVec.add_assoc,←BitVec.ofNat_add,←BitVec.ofNat_add] at eq
  exact WordZero.offset_ne sp (region+i.val) (4904+j.val) (by omega) (by omega) (by rcases apart with h|h <;> omega) eq
end E5R.Thermostat.MainNextCopy264
