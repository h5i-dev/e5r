import Projects.thermostat.MainRamCopy
import Projects.thermostat.MainRamCopyByte
import Projects.thermostat.MainCopyView
namespace E5R.Thermostat.MainRamCopy264
open E5R E5R.Thermostat

def addr (sp : Word) (index : Nat) := sp+BitVec.ofNat 32 (4*index)
def words (ram : Word → BitVec 8) (sp : Word) (src : Nat) := HeadRamCopyMemory.snapshot ram (addr sp src) 66

def memory (ram : Word → BitVec 8) (sp : Word) (src dst : Nat) := AlignedCopyLoop.writes ram (addr sp dst) (words ram sp src)

/-- The actual264-byte RAM memcpy at any emitted aligned, separated stack
    pair, including the two common Next/Request staging copies in either order. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (src dst : Nat)
    (sourceBound : 4*src+264≤5232) (destinationBound : 4*dst+264<5232)
    (apart : 4*src+264≤4*dst ∨ 4*dst+264≤4*src)
    (hp : c.pc=0x80005182#32) (h2 : c.get 2=sp) (h10 : c.get 10=addr sp dst)
    (h11 : c.get 11=addr sp src) (h12 : c.get 12=264#32)
    (stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0) :
    ∃ d, Quiet.Steps B img 354 ⟨c,ram⟩ ⟨d,memory ram sp src dst⟩ ∧ FormatCursor.Returned c d ∧ d.get 10=addr sp dst := by
  have bound := stack.2.2
  have srcNat := WordZero.add_nat sp (4*src) (by omega)
  have dstNat := WordZero.add_nat sp (4*dst) (by omega)
  have source : Memory.Block B (addr sp src) 264 := Memory.sub_block stack (off := 4*src) (m := 264) (by omega) sourceBound
  have destination : Memory.Block B (addr sp dst) 264 := Memory.sub_block stack (off := 4*dst) (m := 264) (by omega) (by omega)
  have hs := HeadRamCopyMemory.source B ram (addr sp src) 66 (Memory.word_aligned sp src aligned) source
  have hsp : c.get 2=(sp+0xfffffff0#32)+16#32 := by rw [h2,BitVec.add_assoc,show 0xfffffff0#32+16#32=0#32 by decide +kernel,BitVec.add_zero]
  have separated : MainRamCopySource.Apart (addr sp src) (addr sp dst) (words ram sp src).length := by
    simp only [words,HeadRamCopyMemory.snapshot_length,MainRamCopySource.Apart,addr,srcNat,dstNat]
    rcases apart with a|a <;> omega
  obtain ⟨d,steps,ret,d10,_,_⟩ := MainRamCopy.contract B c ram (sp+0xfffffff0#32) (addr sp src) (addr sp dst) (words ram sp src)
    hp hsp h10 h11 (by simpa only [words,HeadRamCopyMemory.snapshot_length] using h12)
    (by simp only [words,HeadRamCopyMemory.snapshot_length];decide) hs separated
    (Memory.word_aligned sp dst aligned) (by simpa only [words,HeadRamCopyMemory.snapshot_length] using destination)
    (by rw [words,HeadRamCopyMemory.snapshot_length,addr,dstNat];omega)
    (by simp only [words,HeadRamCopyMemory.snapshot_length];decide +kernel)
  exact ⟨d,by simpa only [memory,words,HeadRamCopyMemory.snapshot_length,show 24+5*66=354 from rfl] using steps,ret,d10⟩

theorem bytes (ram : Word → BitVec 8) (sp : Word) (src dst : Nat) (bound : 4*dst+264<5232) (stack : Memory.Block B sp 5232) :
    MainCopyView.At ram (memory ram sp src dst) (addr sp src) (addr sp dst) 264 := by
  intro i
  apply MainRamCopyByte.copied
  have stackBound := stack.2.2
  rw [addr,WordZero.add_nat sp (4*dst) (by omega)]
  omega

theorem frame (ram : Word → BitVec 8) (sp : Word) (src dst off size : Nat) (bound : off+size≤5232) (destinationBound : 4*dst+264≤5232)
    (apart : off+size≤4*dst ∨ 4*dst+264≤off) : ViewFrame.Region ram (memory ram sp src dst) (sp+BitVec.ofNat 32 off) size := by
  intro i
  apply AlignedCopyLoop.frame
  intro j eq
  have hi := i.isLt
  have hj : j.val<264 := by simpa only [words,HeadRamCopyMemory.snapshot_length] using j.isLt
  change (sp+BitVec.ofNat 32 off)+BitVec.ofNat 32 i.val=(sp+BitVec.ofNat 32 (4*dst))+BitVec.ofNat 32 j.val at eq
  rw [BitVec.add_assoc,BitVec.add_assoc,←BitVec.ofNat_add,←BitVec.ofNat_add] at eq
  exact WordZero.offset_ne sp (off+i.val) (4*dst+j.val) (by omega) (by omega) (by rcases apart with h|h <;> omega) eq
end E5R.Thermostat.MainRamCopy264
