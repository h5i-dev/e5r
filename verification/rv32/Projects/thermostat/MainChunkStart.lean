import Projects.thermostat.MainChunkInitData
import Projects.thermostat.ChunkSpecInvariant
namespace E5R.Thermostat.MainChunkStart
open E5R E5R.Thermostat HttpRequestSpec

/-- The actual Chunked dispatch initializes the persisted decoder and both
    in-place cursors. Bounds on the parsed head remain an upstream obligation. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (fp start : Word)
    (h8 : c.get 8=fp) (h23 : c.get 23=fp+476#32) (h20 : c.get 20=start)
    (hm : Memory.Block B fp 508) (ha : fp.toNat%4=0) (hp : c.pc=0x80000e54#32) :
    ∃ d after, Quiet.Steps B img 12 ⟨c,ram⟩ ⟨d,after⟩ ∧ d.pc=0x80000e9a#32 ∧
      d.get 24=start ∧ ChunkLayout.At after (fp+476#32) cStart ∧
      ramRead after (fp+452#32) .w=start ∧ ramRead after (fp+456#32) .w=start ∧
      (∀ maxBody, ChunkSpecInvariant.Inv maxBody cStart) ∧
      (∀ r : Reg, r≠24 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨d,trace,pc,cursor,regs,csr⟩ := MainChunkInit.contract B c ram fp start h8 h23 h20 hm ha hp
  exact ⟨d,MainChunkInit.memory ram fp start,trace,pc,cursor,
    MainChunkInitData.initial ram fp start,MainChunkInitData.cursor452 ram fp start,
    MainChunkInitData.cursor456 ram fp start,ChunkSpecInvariant.initial,regs,csr⟩

end E5R.Thermostat.MainChunkStart
