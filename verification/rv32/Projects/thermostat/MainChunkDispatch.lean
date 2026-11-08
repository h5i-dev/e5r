import Projects.thermostat.MainChunkNothing
import Projects.thermostat.MainChunkDataBranch
import Projects.thermostat.MainChunkEndBranch
import Projects.thermostat.ChunkOutputView
namespace E5R.Thermostat.MainChunkDispatch
open E5R E5R.Thermostat HttpRequestSpec

def continuation : COut → Word
  | .nothing => 0x80000e9a#32
  | .data => 0x80000f6a#32
  | .done | .reject _ => 0x8000106c#32

/-- All four actual outcome tags are derived from the decoder's byte-level
    specification, then dispatched by the two real main branches. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (out : COut)
    (hp : c.pc=0x80000f62#32) (h10 : c.get 10=ChunkOutputView.tag out) (h22 : c.get 22=1#32) :
    ∃ n d, 1≤n ∧ n≤2 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=continuation out ∧ (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  cases out with
  | nothing =>
    have htag : c.get 10=0#32 := by simpa [ChunkOutputView.tag,ChunkLayout.outTag] using h10
    obtain ⟨d,trace,pc,regs,csr⟩ := MainChunkNothing.contract B c ram htag hp
    exact ⟨1,d,by decide,by decide,trace,pc,regs,csr⟩
  | data =>
    have htag : c.get 10=1#32 := by simpa [ChunkOutputView.tag,ChunkLayout.outTag] using h10
    obtain ⟨d,trace,pc,regs,csr⟩ := MainChunkDataBranch.contract B c ram htag h22 hp
    exact ⟨2,d,by decide,by decide,trace,pc,regs,csr⟩
  | done =>
    have htag : c.get 10=2#32 := by simpa [ChunkOutputView.tag,ChunkLayout.outTag] using h10
    obtain ⟨d,trace,pc,regs,csr⟩ := MainChunkEndBranch.contract B c ram 2#32 htag h22 (Or.inl rfl) hp
    exact ⟨2,d,by decide,by decide,trace,pc,regs,csr⟩
  | reject status =>
    have htag : c.get 10=3#32 := by simpa [ChunkOutputView.tag,ChunkLayout.outTag] using h10
    obtain ⟨d,trace,pc,regs,csr⟩ := MainChunkEndBranch.contract B c ram 3#32 htag h22 (Or.inr rfl) hp
    exact ⟨2,d,by decide,by decide,trace,pc,regs,csr⟩

end E5R.Thermostat.MainChunkDispatch
