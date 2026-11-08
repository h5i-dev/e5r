import Projects.thermostat.StatusMemory
import Projects.thermostat.OuterReturn
import Projects.thermostat.ViewFrame
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.StatusReturn
open E5R E5R.Thermostat

/-- Exact no-body Response bytes and two completion flags, then real outer
    epilogue restores every saved register and the caller's stack pointer. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (out f status : Word)
    (hp : c.pc = 0x800005aa#32) (h8 : c.get 8 = f) (h9 : c.get 9 = out)
    (h10 : c.get 10 = 0#32) (h18 : c.get 18 = 0#32) (h20 : c.get 20 = status) (h22 : c.get 22 = 1#32)
    (ho : Memory.Block B out 15) (ha : out.toNat%4 = 0) (hf : Memory.Block B f 41)
    (hst : Memory.Block B (c.get 2) 96) (hsa : (c.get 2).toNat%4 = 0)
    (hso : WordRegions.Disjoint (c.get 2) 96 out 15) (hsf : WordRegions.Disjoint (c.get 2) 96 f 41)
    (hof : WordRegions.Disjoint out 15 f 41) :
    ∃ d, DetSteps B img 23 ⟨c,ram⟩ ⟨d,StatusResponse.memory ram out f status⟩ ∧
      d.pc = ramRead ram (c.get 2+92#32) .w &&& ~~~1 ∧ d.get 2 = c.get 2+96#32 ∧ d.sameCsr c ∧
      OuterReturn.Restored c d ram ∧ StatusMemory.At (StatusResponse.memory ram out f status) out status ∧
      StatusResponse.memory ram out f status (f+36#32) = 1#8 ∧
      StatusResponse.memory ram out f status (f+40#32) = 1#8 := by
  obtain ⟨a,ta,apc,aframe,acsr⟩ := StatusResponse.contract B c ram out f status hp h8 h9 h10 h18 h20 h22 ho ha hf
  have asp : a.get 2 = c.get 2 := aframe 2 (by decide)
  have hr : ViewFrame.Region ram (StatusResponse.memory ram out f status) (c.get 2) 96 := by
    intro i
    exact StatusMemory.frame ram out f status _ (hso i) (hsf i)
  have hw (k : Nat) (hk : k+4 ≤ 96) :
      ramRead (StatusResponse.memory ram out f status) (a.get 2+BitVec.ofNat 32 k) .w =
        ramRead ram (c.get 2+BitVec.ofNat 32 k) .w := by
    rw [asp];exact ViewFrame.word hr k hk
  obtain ⟨d,td,dpc,dsp,dcsr,dsaved⟩ := OuterReturn.contract B a (StatusResponse.memory ram out f status) apc
    (by simpa only [asp] using hst) (by simpa only [asp] using hsa)
  refine ⟨d,ta.trans td,?_,by simpa only [asp] using dsp,dcsr.trans acsr,?_,StatusMemory.response ram out f status hof,
    (StatusMemory.flags ram out f status).1,(StatusMemory.flags ram out f status).2⟩
  · rw [dpc,hw 92 (by decide)]
  · constructor
    · exact dsaved.x1 |>.trans (hw 92 (by decide))
    · exact dsaved.x8 |>.trans (hw 88 (by decide))
    · exact dsaved.x9 |>.trans (hw 84 (by decide))
    · exact dsaved.x18 |>.trans (hw 80 (by decide))
    · exact dsaved.x19 |>.trans (hw 76 (by decide))
    · exact dsaved.x20 |>.trans (hw 72 (by decide))
    · exact dsaved.x21 |>.trans (hw 68 (by decide))
    · exact dsaved.x22 |>.trans (hw 64 (by decide))
    · exact dsaved.x23 |>.trans (hw 60 (by decide))
    · exact dsaved.x24 |>.trans (hw 56 (by decide))
    · exact dsaved.x25 |>.trans (hw 52 (by decide))
    · exact dsaved.x26 |>.trans (hw 48 (by decide))
    · exact dsaved.x27 |>.trans (hw 44 (by decide))
end E5R.Thermostat.StatusReturn
