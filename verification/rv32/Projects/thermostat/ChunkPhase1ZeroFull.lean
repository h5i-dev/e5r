import Projects.thermostat.ChunkPhase1ZeroSpec
import Projects.thermostat.ChunkNumberMath
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace E5R.Thermostat.ChunkPhase1ZeroFull
open E5R E5R.Thermostat HttpRequestSpec

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst : Word)
    (s : CState) (b : BitVec 8) (maxBody : Nat)
    (h : ChunkLayout.At ram src s) (hphase : s.phase=1) (hbyte : b.toNat=10)
    (hn : s.size<4294967296) (hsize : s.size=0)
    (h10 : c.get 10=dst) (h11 : c.get 11=src)
    (h12 : c.get 12=BitVec.ofNat 32 b.toNat) (h13 : c.get 13=BitVec.ofNat 32 maxBody)
    (hsm : Memory.Block B src 32) (hdm : Memory.Block B dst 36)
    (hsa : src.toNat%4=0) (hda : dst.toNat%4=0) (hp : c.pc=0x80002998#32) :
    ∃ d after, Quiet.Steps B img 24 ⟨c,ram⟩ ⟨d,after⟩ ∧
      d.pc=c.get 1 &&& ~~~1 ∧
      ChunkLayout.At after dst (chunkStep s b.toNat maxBody).1 ∧
      ChunkLayout.OutAt after dst (chunkStep s b.toNat maxBody).2 ∧
      (∀ x, (∀ i : Fin 36, x≠dst+BitVec.ofNat 32 i.val) → after x=ram x) ∧
      (∀ r : Reg, r=1 ∨ r=2 ∨ r=8 ∨ r=9 ∨ 18≤r.val → d.get r=c.get r) ∧ d.sameCsr c := by
  have hph : ram (src+24#32)=1#8 := by simpa only [hphase] using h.2
  have hbr3 : taken .ne (BitVec.ofNat 32 b.toNat) (alu .add (0#32) 0x0000000a#32)=false := by
    change taken .ne (BitVec.ofNat 32 b.toNat) (BitVec.ofNat 32 10)=false
    rw [ChunkMath.ne_guard _ _ (by have := b.isLt;omega) (by decide)]
    simp [hbyte]
  have hbr4 : taken .eq (alu .or (extend .w true (ramRead ram (src+0#32) .w)) (extend .w true (ramRead ram (src+4#32) .w))) (0#32)=true := by
    simp only [ChunkWordMath.extend_word,ChunkMath.read0 h,ChunkMath.read4 h]
    rw [ChunkNumberMath.zero_size _ hn]
    simp [hsize]
  obtain ⟨d,trace,ret,regs,csr⟩ := ChunkPhase1Zero.contract B c ram src dst (BitVec.ofNat 32 b.toNat)
    (BitVec.ofNat 32 maxBody) h10 h11 h12 h13 hsm hdm hsa hda hph (by decide +kernel) (by decide +kernel) (by decide +kernel) hbr3 hbr4 hp
  have spec := ChunkPhase1ZeroSpec.representation c ram src dst (BitVec.ofNat 32 b.toNat) (BitVec.ofNat 32 maxBody) s h
  have pure : chunkStep s b.toNat maxBody = ({s with phase := 5, digits := 0},.nothing) := by
    simp [chunkStep,hphase,hsize,hbyte]
  rw [pure]
  refine ⟨d,ChunkPhase1Zero.memory c ram src dst (BitVec.ofNat 32 b.toNat) (BitVec.ofNat 32 maxBody),trace,ret,spec.1,spec.2,?_,?_,csr⟩
  · exact ChunkPhase1ZeroData.frame c ram src dst (BitVec.ofNat 32 b.toNat) (BitVec.ofNat 32 maxBody)
  · intro r hr
    apply regs r <;> (intro he;subst r;revert hr;decide +kernel)
end E5R.Thermostat.ChunkPhase1ZeroFull
