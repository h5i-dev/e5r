import Projects.thermostat.HeadRamCopyMemory
import Projects.thermostat.ViewFrame
namespace E5R.Thermostat.HeadCopyHeader256
open E5R E5R.Thermostat

def words (ram : Word → BitVec 8) (sp : Word) := HeadRamCopyMemory.snapshot ram (sp+56#32) 64

def memory (ram : Word → BitVec 8) (sp : Word) := AlignedCopyLoop.writes ram (sp+4936#32) (words ram sp)

/-- The exact real 256-byte parse_head copy, including memcpy entry and return.
    The source and destination are derived subregions of the actual stack. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word)
    (hp : c.pc=0x80005182#32) (h2 : c.get 2=sp) (h10 : c.get 10=sp+4936#32)
    (h11 : c.get 11=sp+56#32) (h12 : c.get 12=256#32)
    (stack : Memory.Block B sp 5312) (aligned : sp.toNat%4=0) :
    ∃ d, Quiet.Steps B img 344 ⟨c,ram⟩ ⟨d,memory ram sp⟩ ∧ FormatCursor.Returned c d ∧ d.get 10=sp+4936#32 := by
  have bound := stack.2.2
  have srcNat := WordZero.add_nat sp 56 (by omega)
  have dstNat := WordZero.add_nat sp 4936 (by omega)
  have source : Memory.Block B (sp+56#32) 256 := Memory.sub_block stack (by decide) (by decide)
  have destination : Memory.Block B (sp+4936#32) 256 := Memory.sub_block stack (by decide) (by decide)
  have hs := HeadRamCopyMemory.source B ram (sp+56#32) 64 (Memory.word_aligned sp 14 aligned) source
  have hsp : c.get 2=(sp+0xfffffff0#32)+16#32 := by rw [h2,BitVec.add_assoc,show 0xfffffff0#32+16#32=0#32 by decide +kernel,BitVec.add_zero]
  obtain ⟨d,steps,ret,d10,_,_⟩ := HeadRamCopy.contract B c ram (sp+0xfffffff0#32) (sp+56#32) (sp+4936#32) (words ram sp)
    hp hsp h10 h11 (by simpa only [words,HeadRamCopyMemory.snapshot_length] using h12)
    (by simp only [words,HeadRamCopyMemory.snapshot_length];decide) hs
    (by rw [words,HeadRamCopyMemory.snapshot_length,srcNat,dstNat];omega)
    (Memory.word_aligned sp 1234 aligned) (by simpa only [words,HeadRamCopyMemory.snapshot_length] using destination)
    (by rw [words,HeadRamCopyMemory.snapshot_length,dstNat];omega)
    (by simp only [words,HeadRamCopyMemory.snapshot_length];decide +kernel)
  exact ⟨d,by simpa only [memory,words,HeadRamCopyMemory.snapshot_length,show 24+5*64=344 from rfl] using steps,ret,d10⟩

theorem copied (ram : Word → BitVec 8) (sp : Word) (i : Fin 64) (stack : Memory.Block B sp 5312) :
    ramRead (memory ram sp) ((sp+4936#32)+BitVec.ofNat 32 (4*i.val)) .w=
      ramRead ram ((sp+56#32)+BitVec.ofNat 32 (4*i.val)) .w := by
  apply HeadRamCopyMemory.copied
  have bound := stack.2.2
  rw [WordZero.add_nat sp 4936 (by omega)]
  omega

theorem frame (ram : Word → BitVec 8) (sp : Word) (off len : Nat) (bound : off+len≤5312)
    (apart : off+len≤4936 ∨ 5192≤off) : ViewFrame.Region ram (memory ram sp) (sp+BitVec.ofNat 32 off) len := by
  intro i
  apply AlignedCopyLoop.frame
  intro j eq
  have hi := i.isLt
  have hj : j.val<256 := by simpa only [words,HeadRamCopyMemory.snapshot_length] using j.isLt
  rw [BitVec.add_assoc,BitVec.add_assoc,←BitVec.ofNat_add,←BitVec.ofNat_add] at eq
  exact WordZero.offset_ne sp (off+i.val) (4936+j.val) (by omega) (by omega) (by rcases apart with h|h <;> omega) eq
end E5R.Thermostat.HeadCopyHeader256
