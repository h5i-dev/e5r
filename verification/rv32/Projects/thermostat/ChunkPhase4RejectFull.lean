import Projects.thermostat.ChunkPhase4RejectSpec
import Projects.thermostat.ChunkMath
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace E5R.Thermostat.ChunkPhase4RejectFull
open E5R E5R.Thermostat HttpRequestSpec

/-- Actual entry-to-RET execution, with the pure byte transition and exact
    RAM frame. Progress here concerns one supplied byte, not its arrival. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst : Word)
    (s : CState) (b : BitVec 8) (maxBody : Nat)
    (h : ChunkLayout.At ram src s) (hphase : s.phase=4) (hbyte : b.toNat≠10)
    (h10 : c.get 10=dst) (h11 : c.get 11=src)
    (h12 : c.get 12=BitVec.ofNat 32 b.toNat) (h13 : c.get 13=BitVec.ofNat 32 maxBody)
    (hsm : Memory.Block B src 32) (hdm : Memory.Block B dst 36)
    (hsa : src.toNat%4=0) (hda : dst.toNat%4=0) (hp : c.pc=0x80002998#32) :
    ∃ d after, Quiet.Steps B img 27 ⟨c,ram⟩ ⟨d,after⟩ ∧
      d.pc=c.get 1 &&& ~~~1 ∧
      ChunkLayout.At after dst (chunkStep s b.toNat maxBody).1 ∧
      ChunkLayout.OutAt after dst (chunkStep s b.toNat maxBody).2 ∧
      (∀ x, (∀ i : Fin 36, x≠dst+BitVec.ofNat 32 i.val) → after x=ram x) ∧
      (∀ r : Reg, r=1 ∨ r=2 ∨ r=8 ∨ r=9 ∨ 18≤r.val → d.get r=c.get r) ∧ d.sameCsr c := by
  have hph : ram (src+24#32)=4#8 := by simpa only [hphase] using h.2
  have hbr4 : taken .eq (BitVec.ofNat 32 b.toNat) (alu .add (0#32) 0x0000000a#32)=false := by
    change taken .eq (BitVec.ofNat 32 b.toNat) (BitVec.ofNat 32 10) = false
    rw [ChunkMath.eq_guard _ _ (by have := b.isLt;omega) (by decide)]
    simp [hbyte]
  obtain ⟨d,trace,ret,regs,csr⟩ := ChunkPhase4Reject.contract B c ram src dst (BitVec.ofNat 32 b.toNat)
    (BitVec.ofNat 32 maxBody) h10 h11 h12 h13 hsm hdm hsa hda hph (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hbr4 hp
  have spec := ChunkPhase4RejectSpec.representation c ram src dst (BitVec.ofNat 32 b.toNat) (BitVec.ofNat 32 maxBody) s h
  have pure : chunkStep s b.toNat maxBody = ({s with phase := 4, size := 0},.reject 400) := by
    simp [chunkStep,expectStep,hphase,hbyte]
  rw [pure] at ⊢
  refine ⟨d,ChunkPhase4Reject.memory c ram src dst (BitVec.ofNat 32 b.toNat) (BitVec.ofNat 32 maxBody),trace,ret,spec.1,spec.2,?_,?_,csr⟩
  · exact ChunkPhase4RejectData.frame c ram src dst (BitVec.ofNat 32 b.toNat) (BitVec.ofNat 32 maxBody)
  · intro r hr
    apply regs r <;> (intro he;subst r;revert hr;decide +kernel)
end E5R.Thermostat.ChunkPhase4RejectFull
