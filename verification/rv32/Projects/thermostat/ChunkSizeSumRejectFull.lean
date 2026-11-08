import Projects.thermostat.ChunkSizeSumRejectSpec
import Projects.thermostat.ChunkByteFacts
import Projects.thermostat.ChunkCapacityMath
import Projects.thermostat.ChunkSpecInvariant
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ChunkSizeSumRejectFull
open E5R E5R.Thermostat HttpRequestSpec

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst : Word)
    (s : CState) (b : BitVec 8) (maxBody : Nat)
    (h : ChunkLayout.At ram src s) (hinv : ChunkSpecInvariant.Inv maxBody s)
    (hmax : maxBody<4294967296) (hphase : s.phase=0) (hbyte : b.toNat=13) (hdigits : 0<s.digits) (hsum : maxBody-s.total<s.size)
    (h10 : c.get 10=dst) (h11 : c.get 11=src)
    (h12 : c.get 12=BitVec.ofNat 32 b.toNat) (h13 : c.get 13=BitVec.ofNat 32 maxBody)
    (hsm : Memory.Block B src 32) (hdm : Memory.Block B dst 36)
    (hsa : src.toNat%4=0) (hda : dst.toNat%4=0)  (hp : c.pc=0x80002998#32) :
    ∃ d after, Quiet.Steps B img 56 ⟨c,ram⟩ ⟨d,after⟩ ∧
      d.pc=c.get 1 &&& ~~~1 ∧
      ChunkLayout.At after dst (chunkStep s b.toNat maxBody).1 ∧
      ChunkLayout.OutAt after dst (chunkStep s b.toNat maxBody).2 ∧
      (∀ x, (∀ i : Fin 36, x≠dst+BitVec.ofNat 32 i.val) → after x=ram x) ∧
      (∀ r : Reg, r=1 ∨ r=2 ∨ r=8 ∨ r=9 ∨ 18≤r.val → d.get r=c.get r) ∧ d.sameCsr c := by
  have hph : ram (src+24#32)=0#8 := by simpa only [hphase] using h.2
  have hd := hinv.digits
  have ht := hinv.total
  have hn := hinv.size
  have hhex : ¬hexv b.toNat<16 := by rw [hbyte];decide +kernel
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
  have hbr5 : taken .ne (BitVec.ofNat 32 b.toNat) (alu .add (0#32) 0x0000000d#32)=false := by
    change taken .ne (BitVec.ofNat 32 b.toNat) (0x0000000d#32)=false
    rw [ChunkMath.ne_guard _ _ (by have := b.isLt;omega) (by decide)]
    simp [hbyte]
  have hbr6 : taken .eq (alu .or (extend .w true (ramRead ram (src+8#32) .w)) (extend .w true (ramRead ram (src+12#32) .w))) (0#32)=false := by
    simp only [ChunkWordMath.extend_word,ChunkMath.read0 h,ChunkMath.read4 h,ChunkMath.read8 h,
      ChunkMath.read12 h,ChunkMath.read16 h,ChunkMath.read20 h]
    rw [ChunkNumberMath.zero_size _ (by omega)]
    simp [hdigits,show s.digits≠0 by omega]
  have hbr7 : taken .ne (alu .or (alu .sltu (BitVec.ofNat 32 maxBody) (extend .w true (ramRead ram (src+16#32) .w))) (alu .sltu (0#32) (extend .w true (ramRead ram (src+20#32) .w)))) (0#32)=false := by
    simp only [ChunkWordMath.extend_word,ChunkMath.read0 h,ChunkMath.read4 h,ChunkMath.read8 h,
      ChunkMath.read12 h,ChunkMath.read16 h,ChunkMath.read20 h]
    rw [ChunkNumberMath.less maxBody s.total hmax (by omega)]
    simp [show ¬maxBody<s.total by omega,alu,taken]
  have hbr8 : taken .eq (extend .w true (ramRead ram (src+4#32) .w)) (alu .sub (alu .sub (0#32) (extend .w true (ramRead ram (src+20#32) .w))) (alu .sltu (BitVec.ofNat 32 maxBody) (extend .w true (ramRead ram (src+16#32) .w))))=true := by
    simp only [ChunkWordMath.extend_word,ChunkMath.read0 h,ChunkMath.read4 h,ChunkMath.read8 h,
      ChunkMath.read12 h,ChunkMath.read16 h,ChunkMath.read20 h]
    rw [ChunkNumberMath.less maxBody s.total hmax (by omega)]
    simp [show ¬maxBody<s.total by omega,alu,taken]
  have hbr9 : taken .eq (alu .sltu (alu .sub (BitVec.ofNat 32 maxBody) (extend .w true (ramRead ram (src+16#32) .w))) (extend .w true (ramRead ram (src+0#32) .w))) (0#32)=false := by
    simp only [ChunkWordMath.extend_word,ChunkMath.read0 h,ChunkMath.read4 h,ChunkMath.read8 h,
      ChunkMath.read12 h,ChunkMath.read16 h,ChunkMath.read20 h]
    rw [ChunkCapacityMath.sub maxBody s.total hmax ht,ChunkNumberMath.less (maxBody-s.total) s.size (by omega) hn]
    simp [hsum,taken]
  obtain ⟨d,trace,ret,regs,csr⟩ := ChunkSizeSumReject.contract B c ram src dst (BitVec.ofNat 32 b.toNat)
    (BitVec.ofNat 32 maxBody) h10 h11 h12 h13 hsm hdm hsa hda hph (by decide +kernel) (by decide +kernel) hbr2 hbr3 hbr4 hbr5 hbr6 hbr7 hbr8 hbr9 hp
  have spec := ChunkSizeSumRejectSpec.representation c ram src dst (BitVec.ofNat 32 b.toNat) (BitVec.ofNat 32 maxBody) s h
  have pure : chunkStep s b.toNat maxBody = (s,.reject 413) := by
    simp [chunkStep,sizeStep,hexv,hphase,hhex,hbyte,hdigits,hsum,show ¬maxBody<s.total by omega]
  rw [pure]
  refine ⟨d,ChunkSizeSumReject.memory c ram src dst (BitVec.ofNat 32 b.toNat) (BitVec.ofNat 32 maxBody),trace,ret,spec.1,spec.2,?_,?_,csr⟩
  · exact ChunkSizeSumRejectData.frame c ram src dst (BitVec.ofNat 32 b.toNat) (BitVec.ofNat 32 maxBody)
  · intro r hr
    apply regs r <;> (intro he;subst r;revert hr;decide +kernel)
end E5R.Thermostat.ChunkSizeSumRejectFull
