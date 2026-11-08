import Projects.thermostat.ChunkHexLowerAcceptSpec
import Projects.thermostat.ChunkByteFacts
import Projects.thermostat.ChunkSizeMath
import Projects.thermostat.ChunkSpecInvariant
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ChunkHexLowerAcceptFull
open E5R E5R.Thermostat HttpRequestSpec

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst : Word)
    (s : CState) (b : BitVec 8) (maxBody : Nat)
    (h : ChunkLayout.At ram src s) (hinv : ChunkSpecInvariant.Inv maxBody s)
    (hphase : s.phase=0) (hb : 97≤b.toNat ∧ b.toNat≤102)
    (hdigits : s.digits<8) (hsize : s.size≤268435455)
    (h10 : c.get 10=dst) (h11 : c.get 11=src)
    (h12 : c.get 12=BitVec.ofNat 32 b.toNat) (h13 : c.get 13=BitVec.ofNat 32 maxBody)
    (hsm : Memory.Block B src 32) (hdm : Memory.Block B dst 36)
    (hsa : src.toNat%4=0) (hda : dst.toNat%4=0) (hp : c.pc=0x80002998#32) :
    ∃ d after, Quiet.Steps B img 46 ⟨c,ram⟩ ⟨d,after⟩ ∧
      d.pc=c.get 1 &&& ~~~1 ∧
      ChunkLayout.At after dst (chunkStep s b.toNat maxBody).1 ∧
      ChunkLayout.OutAt after dst (chunkStep s b.toNat maxBody).2 ∧
      (∀ x, (∀ i : Fin 36, x≠dst+BitVec.ofNat 32 i.val) → after x=ram x) ∧
      (∀ r : Reg, r=1 ∨ r=2 ∨ r=8 ∨ r=9 ∨ 18≤r.val → d.get r=c.get r) ∧ d.sameCsr c := by
  have hph : ram (src+24#32)=0#8 := by simpa only [hphase] using h.2
  have hd := hinv.digits
  have hn := hinv.size
  have hv : hexv b.toNat<16 := (ChunkByteFacts.classes b).mp (Or.inr (Or.inl hb))
  have hnotDecimal : ¬(48≤b.toNat ∧ b.toNat≤57) := by omega
  have hbr2 : taken .ltu (alu .and (alu .add (BitVec.ofNat 32 b.toNat) 0xffffffd0#32) 0x000000ff#32) (alu .add (0#32) 0x0000000a#32)=false := by
    change taken .ltu (alu .and (alu .add (BitVec.ofNat 32 b.toNat) 0xffffffd0#32) 0x000000ff#32) (0x0000000a#32)=false
    rw [ChunkByteFacts.decimal_guard b]
    simp [hb,hnotDecimal]
  have hbr3 : taken .geu (alu .and (alu .add (BitVec.ofNat 32 b.toNat) 0xffffff9f#32) 0x000000ff#32) (alu .add (0#32) 0x00000006#32)=false := by
    change taken .geu (alu .and (alu .add (BitVec.ofNat 32 b.toNat) 0xffffff9f#32) 0x000000ff#32) (0x00000006#32)=false
    rw [ChunkByteFacts.lower_guard b]
    simp [hb,hnotDecimal]
  have hbr4 : taken .eq (alu .and (alu .sltu (extend .w true (ramRead ram (src+12#32) .w)) 0x00000001#32) (alu .sltu (extend .w true (ramRead ram (src+8#32) .w)) 0x00000008#32)) (0#32)=false := by
    simp only [ChunkWordMath.extend_word,ChunkMath.read0 h,ChunkMath.read4 h,ChunkMath.read8 h,ChunkMath.read12 h]
    rw [ChunkSizeMath.digits_guard _ (by omega)]
    simp [hdigits,show ¬8≤s.digits by omega]
  have hbr5 : taken .ne (alu .or (extend .w true (ramRead ram (src+4#32) .w)) (alu .srl (extend .w true (ramRead ram (src+0#32) .w)) 0x0000001c#32)) (0#32)=false := by
    simp only [ChunkWordMath.extend_word,ChunkMath.read0 h,ChunkMath.read4 h,ChunkMath.read8 h,ChunkMath.read12 h]
    rw [ChunkSizeMath.size_guard _ hn]
    simp [hsize,show ¬268435455<s.size by omega]
  obtain ⟨d,trace,ret,regs,csr⟩ := ChunkHexLowerAccept.contract B c ram src dst (BitVec.ofNat 32 b.toNat)
    (BitVec.ofNat 32 maxBody) h10 h11 h12 h13 hsm hdm hsa hda hph (by decide +kernel) (by decide +kernel) hbr2 hbr3 hbr4 hbr5 hp
  have spec := ChunkHexLowerAcceptSpec.representation c ram src dst (BitVec.ofNat 32 maxBody) s b h hb hsize hdigits
  have pure : chunkStep s b.toNat maxBody = ({s with phase := 0,size := s.size*16+hexv b.toNat,digits := s.digits+1},.nothing) := by
    simp [chunkStep,sizeStep,hphase,hv,hdigits,hsize,show ¬8≤s.digits by omega,show ¬268435455<s.size by omega]
  rw [pure]
  refine ⟨d,ChunkHexLowerAccept.memory c ram src dst (BitVec.ofNat 32 b.toNat) (BitVec.ofNat 32 maxBody),trace,ret,spec.1,spec.2,?_,?_,csr⟩
  · exact ChunkHexLowerAcceptData.frame c ram src dst (BitVec.ofNat 32 b.toNat) (BitVec.ofNat 32 maxBody)
  · intro r hr
    apply regs r <;> (intro he;subst r;revert hr;decide +kernel)
end E5R.Thermostat.ChunkHexLowerAcceptFull
