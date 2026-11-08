import Projects.thermostat.ChunkSizeInvalidByteSpec
import Projects.thermostat.ChunkByteFacts
import Projects.thermostat.ChunkCapacityMath
import Projects.thermostat.ChunkSpecInvariant
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ChunkSizeInvalidByteFull
open E5R E5R.Thermostat HttpRequestSpec

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst : Word)
    (s : CState) (b : BitVec 8) (maxBody : Nat)
    (h : ChunkLayout.At ram src s) (hinv : ChunkSpecInvariant.Inv maxBody s)
    (hmax : maxBody<4294967296) (hphase : s.phase=0) (hhex : ¬hexv b.toNat<16) (hbyte : b.toNat≠13)  
    (h10 : c.get 10=dst) (h11 : c.get 11=src)
    (h12 : c.get 12=BitVec.ofNat 32 b.toNat) (h13 : c.get 13=BitVec.ofNat 32 maxBody)
    (hsm : Memory.Block B src 32) (hdm : Memory.Block B dst 36)
    (hsa : src.toNat%4=0) (hda : dst.toNat%4=0)  (hp : c.pc=0x80002998#32) :
    ∃ d after, Quiet.Steps B img 37 ⟨c,ram⟩ ⟨d,after⟩ ∧
      d.pc=c.get 1 &&& ~~~1 ∧
      ChunkLayout.At after dst (chunkStep s b.toNat maxBody).1 ∧
      ChunkLayout.OutAt after dst (chunkStep s b.toNat maxBody).2 ∧
      (∀ x, (∀ i : Fin 36, x≠dst+BitVec.ofNat 32 i.val) → after x=ram x) ∧
      (∀ r : Reg, r=1 ∨ r=2 ∨ r=8 ∨ r=9 ∨ 18≤r.val → d.get r=c.get r) ∧ d.sameCsr c := by
  have hph : ram (src+24#32)=0#8 := by simpa only [hphase] using h.2
  have hd := hinv.digits
  have ht := hinv.total
  have hn := hinv.size
  have hncls := mt (ChunkByteFacts.classes b).mp hhex
  have hnotDecimal : ¬(48≤b.toNat ∧ b.toNat≤57) := fun h => hncls (Or.inl h)
  have hnotLower : ¬(97≤b.toNat ∧ b.toNat≤102) := fun h => hncls (Or.inr (Or.inl h))
  have hnotUpper : ¬(65≤b.toNat ∧ b.toNat≤70) := fun h => hncls (Or.inr (Or.inr h))
  have hbr2 : taken .ltu (alu .and (alu .add (BitVec.ofNat 32 b.toNat) 0xffffffd0#32) 0x000000ff#32) (alu .add (0#32) 0x0000000a#32)=false := by
    change taken .ltu (alu .and (alu .add (BitVec.ofNat 32 b.toNat) 0xffffffd0#32) 0x000000ff#32) (0x0000000a#32)=false
    rw [ChunkByteFacts.decimal_guard b]
    simp [hnotDecimal,hnotLower,hnotUpper]
  have hbr3 : taken .geu (alu .and (alu .add (BitVec.ofNat 32 b.toNat) 0xffffff9f#32) 0x000000ff#32) (alu .add (0#32) 0x00000006#32)=true := by
    change taken .geu (alu .and (alu .add (BitVec.ofNat 32 b.toNat) 0xffffff9f#32) 0x000000ff#32) (0x00000006#32)=true
    rw [ChunkByteFacts.lower_guard b]
    simp [hnotDecimal,hnotLower,hnotUpper]
  have hbr4 : taken .geu (alu .and (alu .add (BitVec.ofNat 32 b.toNat) 0xffffffbf#32) 0x000000ff#32) (alu .add (0#32) 0x00000006#32)=true := by
    change taken .geu (alu .and (alu .add (BitVec.ofNat 32 b.toNat) 0xffffffbf#32) 0x000000ff#32) (0x00000006#32)=true
    rw [ChunkByteFacts.upper_guard b]
    simp [hnotDecimal,hnotLower,hnotUpper]
  have hbr5 : taken .ne (BitVec.ofNat 32 b.toNat) (alu .add (0#32) 0x0000000d#32)=true := by
    change taken .ne (BitVec.ofNat 32 b.toNat) (0x0000000d#32)=true
    rw [ChunkMath.ne_guard _ _ (by have := b.isLt;omega) (by decide)]
    simp [hbyte]
  obtain ⟨d,trace,ret,regs,csr⟩ := ChunkSizeInvalidByte.contract B c ram src dst (BitVec.ofNat 32 b.toNat)
    (BitVec.ofNat 32 maxBody) h10 h11 h12 h13 hsm hdm hsa hda hph (by decide +kernel) (by decide +kernel) hbr2 hbr3 hbr4 hbr5 hp
  have spec := ChunkSizeInvalidByteSpec.representation c ram src dst (BitVec.ofNat 32 b.toNat) (BitVec.ofNat 32 maxBody) s h
  have pure : chunkStep s b.toNat maxBody = (s,.reject 400) := by
    simp [chunkStep,sizeStep,hphase,hhex,hbyte]
  rw [pure]
  refine ⟨d,ChunkSizeInvalidByte.memory c ram src dst (BitVec.ofNat 32 b.toNat) (BitVec.ofNat 32 maxBody),trace,ret,spec.1,spec.2,?_,?_,csr⟩
  · exact ChunkSizeInvalidByteData.frame c ram src dst (BitVec.ofNat 32 b.toNat) (BitVec.ofNat 32 maxBody)
  · intro r hr
    apply regs r <;> (intro he;subst r;revert hr;decide +kernel)
end E5R.Thermostat.ChunkSizeInvalidByteFull
