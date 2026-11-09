import Projects.thermostat.ChunkCallerFrame
import Projects.thermostat.MainChunkInitFrame
import Projects.thermostat.MainChunkLoopInvariant
namespace E5R.Thermostat.ChunkCallerStart
open E5R E5R.Thermostat HttpRequestSpec

/-- The actual Chunked branch establishes the full body-loop invariant.
    Parsed-head bounds and the live future layout are explicit upstream inputs. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word)
    (start filled : Nat)
    (hp : c.pc=0x80000e54#32) (h2 : c.get 2=sp) (h8 : c.get 8=sp+3204#32)
    (h23 : c.get 23=sp+3680#32) (h20 : c.get 20=BitVec.ofNat 32 start)
    (h22 : c.get 22=1#32) (h19 : c.get 19=0x10000000#32) (hmask : c.mie_=false)
    (hm : Memory.Block B sp 4928) (ha : sp.toNat%4=0) (hl : MainChunkLayout.At ram sp)
    (hf : ramRead ram (sp+3288#32) .w=BitVec.ofNat 32 filled)
    (hstart : start≤filled) (hcap : filled≤2048) :
    ∃ d after, Quiet.Steps B img 12 ⟨c,ram⟩ ⟨d,after⟩ ∧
      MainChunkLoopInvariant.At B d after sp start start start filled cStart ∧ ChunkCallerFrame.At c d ram after sp ∧ ViewFrame.Region ram after (sp+132#32) 2048 := by
  have statePtr : c.get 23=(sp+3204#32)+476#32 := by
    simpa only [BitVec.add_assoc,show 3204#32+476#32=3680#32 by decide +kernel] using h23
  obtain ⟨d,trace,pc,cursor,regs,csr⟩ := MainChunkInit.contract B c ram (sp+3204#32) (BitVec.ofNat 32 start)
    h8 statePtr h20 (Memory.sub_block hm (off := 3204) (by decide) (by decide)) (Memory.word_aligned sp 801 ha) hp
  let after := MainChunkInit.memory ram (sp+3204#32) (BitVec.ofNat 32 start)
  refine ⟨d,after,trace,?_,?_,?_⟩
  constructor
  · exact pc
  · exact (regs 2 (by decide)).trans h2
  · exact (regs 8 (by decide)).trans h8
  · exact (regs 23 (by decide)).trans h23
  · exact cursor
  · exact (regs 22 (by decide)).trans h22
  · exact (regs 19 (by decide)).trans h19
  · exact MainChunkCoreFrame.masked csr hmask
  · exact hm
  · exact ha
  · exact MainChunkInitFrame.layout hl
  · exact (ViewFrame.word (MainChunkInitFrame.low_sp ram sp (BitVec.ofNat 32 start)) 3288 (by decide)).trans hf
  · have h := MainChunkInitData.cursor452 ram (sp+3204#32) (BitVec.ofNat 32 start)
    simpa only [BitVec.add_assoc,show 3204#32+452#32=3656#32 by decide +kernel] using h
  · have h := MainChunkInitData.cursor456 ram (sp+3204#32) (BitVec.ofNat 32 start)
    simpa only [BitVec.add_assoc,show 3204#32+456#32=3660#32 by decide +kernel] using h
  · have h := MainChunkInitData.initial ram (sp+3204#32) (BitVec.ofNat 32 start)
    simpa only [BitVec.add_assoc,show 3204#32+476#32=3680#32 by decide +kernel] using h
  · simpa only [Nat.sub_self] using ChunkDecodedInvariant.initial 1024
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · exact hstart
  · exact hcap

  · refine ⟨?_,ViewFrame.shrink (MainChunkInitFrame.low_sp ram sp (BitVec.ofNat 32 start)) (by decide),?_,
      HeadRegionFrame.sub (MainChunkInitFrame.low_sp ram sp (BitVec.ofNat 32 start)) 3204 84 (by decide),
      HeadRegionFrame.sub (MainChunkInitFrame.low_sp ram sp (BitVec.ofNat 32 start)) 3292 364 (by decide),csr⟩
    · intro rr safe
      have ne : ∀ rr : Reg, MainChunkCoreFrame.Kept rr → rr≠24 := by decide +kernel
      exact regs rr (ne rr safe)
    · intro off safe
      have bound := MainServeLayout.bounds off safe
      have word := ViewFrame.word (MainChunkInitFrame.low_sp ram sp (BitVec.ofNat 32 start)) (3204+off) (by omega)
      simpa only [BitVec.ofNat_add,BitVec.add_assoc] using word
  · exact HeadRegionFrame.sub (MainChunkInitFrame.low_sp ram sp (BitVec.ofNat 32 start)) 132 2048 (by decide)

end E5R.Thermostat.ChunkCallerStart
