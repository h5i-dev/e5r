import Projects.thermostat.ChunkPhase2SmallSpec
import Projects.thermostat.ChunkNumberMath
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace E5R.Thermostat.ChunkPhase2SmallFull
open E5R E5R.Thermostat HttpRequestSpec

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst : Word)
    (s : CState) (b : BitVec 8) (maxBody : Nat)
    (h : ChunkLayout.At ram src s) (hphase : s.phase=2) 
    (hn : s.size<4294967296) (hsize : s.size≤1)
    (h10 : c.get 10=dst) (h11 : c.get 11=src)
    (h12 : c.get 12=BitVec.ofNat 32 b.toNat) (h13 : c.get 13=BitVec.ofNat 32 maxBody)
    (hsm : Memory.Block B src 32) (hdm : Memory.Block B dst 36)
    (hsa : src.toNat%4=0) (hda : dst.toNat%4=0) (hp : c.pc=0x80002998#32) :
    ∃ d after, Quiet.Steps B img 30 ⟨c,ram⟩ ⟨d,after⟩ ∧
      d.pc=c.get 1 &&& ~~~1 ∧
      ChunkLayout.At after dst (chunkStep s b.toNat maxBody).1 ∧
      ChunkLayout.OutAt after dst (chunkStep s b.toNat maxBody).2 ∧
      (∀ x, (∀ i : Fin 36, x≠dst+BitVec.ofNat 32 i.val) → after x=ram x) ∧
      (∀ r : Reg, r=1 ∨ r=2 ∨ r=8 ∨ r=9 ∨ 18≤r.val → d.get r=c.get r) ∧ d.sameCsr c := by
  have hph : ram (src+24#32)=2#8 := by simpa only [hphase] using h.2
  have hbr4 : taken .eq (alu .and (alu .sltu (extend .w true (ramRead ram (src+4#32) .w)) 0x00000001#32) (alu .sltu (extend .w true (ramRead ram (src+0#32) .w)) 0x00000002#32)) (0#32)=false := by
    simp only [ChunkWordMath.extend_word,ChunkMath.read0 h,ChunkMath.read4 h]
    rw [ChunkNumberMath.small_guard _ hn]
    simp [show ¬2≤s.size by omega]
  obtain ⟨d,trace,ret,regs,csr⟩ := ChunkPhase2Small.contract B c ram src dst (BitVec.ofNat 32 b.toNat)
    (BitVec.ofNat 32 maxBody) h10 h11 h12 h13 hsm hdm hsa hda hph (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hbr4 hp
  have spec := ChunkPhase2SmallSpec.representation c ram src dst (BitVec.ofNat 32 b.toNat) (BitVec.ofNat 32 maxBody) s h
  have pure : chunkStep s b.toNat maxBody = ({s with phase := 3, size := 0},.data) := by
    simp [chunkStep,hphase,hsize]
  rw [pure]
  refine ⟨d,ChunkPhase2Small.memory c ram src dst (BitVec.ofNat 32 b.toNat) (BitVec.ofNat 32 maxBody),trace,ret,spec.1,spec.2,?_,?_,csr⟩
  · exact ChunkPhase2SmallData.frame c ram src dst (BitVec.ofNat 32 b.toNat) (BitVec.ofNat 32 maxBody)
  · intro r hr
    apply regs r <;> (intro he;subst r;revert hr;decide +kernel)
end E5R.Thermostat.ChunkPhase2SmallFull
