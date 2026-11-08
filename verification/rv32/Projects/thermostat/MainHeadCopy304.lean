import Projects.thermostat.MainRamCopy
import Projects.thermostat.MainRamCopyByte
import Projects.thermostat.MainCopyView
namespace E5R.Thermostat.MainHeadCopy304
open E5R E5R.Thermostat

def words (ram : Word → BitVec 8) (sp : Word) := HeadRamCopyMemory.snapshot ram (sp+4520#32) 76

def memory (ram : Word → BitVec 8) (sp : Word) := AlignedCopyLoop.writes ram (sp+3320#32) (words ram sp)

/-- Actual aligned304-byte Head copy used by main, destination below source.
    Entry, all76 RAM word turns and the real memcpy return are included. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word)
    (hp : c.pc=0x80005182#32) (h2 : c.get 2=sp) (h10 : c.get 10=sp+3320#32)
    (h11 : c.get 11=sp+4520#32) (h12 : c.get 12=304#32)
    (stack : Memory.Block B sp 4928) (aligned : sp.toNat%4=0) :
    ∃ d, Quiet.Steps B img 404 ⟨c,ram⟩ ⟨d,memory ram sp⟩ ∧ FormatCursor.Returned c d ∧ d.get 10=sp+3320#32 := by
  have bound := stack.2.2
  have srcNat := WordZero.add_nat sp 4520 (by omega)
  have dstNat := WordZero.add_nat sp 3320 (by omega)
  have source : Memory.Block B (sp+4520#32) 304 := Memory.sub_block stack (off := 4520) (m := 304) (by decide) (by decide)
  have destination : Memory.Block B (sp+3320#32) 304 := Memory.sub_block stack (off := 3320) (m := 304) (by decide) (by decide)
  have hs := HeadRamCopyMemory.source B ram (sp+4520#32) 76 (Memory.word_aligned sp 1130 aligned) source
  have hsp : c.get 2=(sp+0xfffffff0#32)+16#32 := by rw [h2,BitVec.add_assoc,show 0xfffffff0#32+16#32=0#32 by decide +kernel,BitVec.add_zero]
  obtain ⟨d,steps,ret,d10,_,_⟩ := MainRamCopy.contract B c ram (sp+0xfffffff0#32) (sp+4520#32) (sp+3320#32) (words ram sp)
    hp hsp h10 h11 (by simpa only [words,HeadRamCopyMemory.snapshot_length] using h12)
    (by simp only [words,HeadRamCopyMemory.snapshot_length];decide) hs
    (by apply Or.inr;rw [words,HeadRamCopyMemory.snapshot_length,srcNat,dstNat];omega)
    (Memory.word_aligned sp 830 aligned) (by simpa only [words,HeadRamCopyMemory.snapshot_length] using destination)
    (by rw [words,HeadRamCopyMemory.snapshot_length,dstNat];omega)
    (by simp only [words,HeadRamCopyMemory.snapshot_length];decide +kernel)
  exact ⟨d,by simpa only [memory,words,HeadRamCopyMemory.snapshot_length,show 24+5*76=404 from rfl] using steps,ret,d10⟩

theorem bytes (ram : Word → BitVec 8) (sp : Word) (stack : Memory.Block B sp 4928) :
    MainCopyView.At ram (memory ram sp) (sp+4520#32) (sp+3320#32) 304 := by
  intro i
  apply MainRamCopyByte.copied
  have bound := stack.2.2
  rw [WordZero.add_nat sp 3320 (by omega)]
  omega

theorem head (ram : Word → BitVec 8) (sp : Word) (value : HttpRequestSpec.Head) (stack : Memory.Block B sp 4928)
    (view : HeadCompletedView.At ram (sp+4520#32) value) : HeadCompletedView.At (memory ram sp) (sp+3320#32) value :=
  MainCopyView.head (bytes ram sp stack) value view

theorem frame (ram : Word → BitVec 8) (sp : Word) (off len : Nat) (bound : off+len≤4928)
    (apart : off+len≤3320 ∨ 3624≤off) : ViewFrame.Region ram (memory ram sp) (sp+BitVec.ofNat 32 off) len := by
  intro i
  apply AlignedCopyLoop.frame
  intro j eq
  have hi := i.isLt
  have hj : j.val<304 := by simpa only [words,HeadRamCopyMemory.snapshot_length] using j.isLt
  rw [BitVec.add_assoc,BitVec.add_assoc,←BitVec.ofNat_add,←BitVec.ofNat_add] at eq
  exact WordZero.offset_ne sp (off+i.val) (3320+j.val) (by omega) (by omega) (by rcases apart with h|h <;> omega) eq
end E5R.Thermostat.MainHeadCopy304
