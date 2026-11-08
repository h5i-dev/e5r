import Projects.thermostat.ChunkHexDecimalAcceptFull
import Projects.thermostat.ChunkHexDecimalDigitsRejectFull
import Projects.thermostat.ChunkHexDecimalSizeRejectFull
import Projects.thermostat.ChunkHexLowerAcceptFull
import Projects.thermostat.ChunkHexLowerDigitsRejectFull
import Projects.thermostat.ChunkHexLowerSizeRejectFull
import Projects.thermostat.ChunkHexUpperAcceptFull
import Projects.thermostat.ChunkHexUpperDigitsRejectFull
import Projects.thermostat.ChunkHexUpperSizeRejectFull
import Projects.thermostat.ChunkPhase1DataFull
import Projects.thermostat.ChunkPhase1RejectFull
import Projects.thermostat.ChunkPhase1ZeroFull
import Projects.thermostat.ChunkPhase2DecrementFull
import Projects.thermostat.ChunkPhase2SmallFull
import Projects.thermostat.ChunkPhase3AcceptFull
import Projects.thermostat.ChunkPhase3RejectFull
import Projects.thermostat.ChunkPhase4AcceptFull
import Projects.thermostat.ChunkPhase4RejectFull
import Projects.thermostat.ChunkPhase5AcceptFull
import Projects.thermostat.ChunkPhase5RejectFull
import Projects.thermostat.ChunkPhase6AcceptFull
import Projects.thermostat.ChunkPhase6RejectFull
import Projects.thermostat.ChunkPhase7RejectFull
import Projects.thermostat.ChunkSizeAcceptFull
import Projects.thermostat.ChunkSizeEmptyFull
import Projects.thermostat.ChunkSizeInvalidByteFull
import Projects.thermostat.ChunkSizeSumRejectFull
namespace E5R.Thermostat.ChunkStep
open E5R E5R.Thermostat HttpRequestSpec

structure Pre (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst : Word)
    (s : CState) (b : BitVec 8) (maxBody : Nat) : Prop where
  pc : c.pc=0x80002998#32
  out : c.get 10=dst
  state : c.get 11=src
  byte : c.get 12=BitVec.ofNat 32 b.toNat
  limit : c.get 13=BitVec.ofNat 32 maxBody
  srcRam : Memory.Block B src 32
  dstRam : Memory.Block B dst 36
  srcAlign : src.toNat%4=0
  dstAlign : dst.toNat%4=0
  object : ChunkLayout.At ram src s
  inv : ChunkSpecInvariant.Inv maxBody s
  limitBound : maxBody<4294967296

def Post (c d : Core) (ram after : Word → BitVec 8) (dst : Word)
    (next : CState) (out : COut) : Prop :=
  d.pc=c.get 1 &&& ~~~1 ∧ ChunkLayout.At after dst next ∧ ChunkLayout.OutAt after dst out ∧
  (∀ x, (∀ i : Fin 36, x≠dst+BitVec.ofNat 32 i.val) → after x=ram x) ∧
  (∀ r : Reg, r=1 ∨ r=2 ∨ r=8 ∨ r=9 ∨ 18≤r.val → d.get r=c.get r) ∧ d.sameCsr c

theorem bounded {B c ram dst s maxBody n} {b : BitVec 8}
    (hn : 24≤n ∧ n≤56)
    (h : ∃ d after, Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      Post c d ram after dst (chunkStep s b.toNat maxBody).1 (chunkStep s b.toNat maxBody).2) :
    ∃ n d after, 24≤n ∧ n≤56 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      Post c d ram after dst (chunkStep s b.toNat maxBody).1 (chunkStep s b.toNat maxBody).2 := by
  obtain ⟨d,after,ht,hp⟩ := h
  exact ⟨n,d,after,hn.1,hn.2,ht,hp⟩

/-- The actual loop-free decoder, from its ELF entry through RET, for every
    input byte and every reachable representation state. Accepted MMIO reads
    and writes are absent. This does not assume byte arrival or UART progress. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst : Word)
    (s : CState) (b : BitVec 8) (maxBody : Nat) (h : Pre B c ram src dst s b maxBody) :
    ∃ n d after, 24≤n ∧ n≤56 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      Post c d ram after dst (chunkStep s b.toNat maxBody).1 (chunkStep s b.toNat maxBody).2 ∧
      ChunkSpecInvariant.Inv maxBody (chunkStep s b.toNat maxBody).1 := by
  suffices run : ∃ n d after, 24≤n ∧ n≤56 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      Post c d ram after dst (chunkStep s b.toNat maxBody).1 (chunkStep s b.toNat maxBody).2 by
    obtain ⟨n,d,after,hlo,hn,ht,hp⟩ := run
    exact ⟨n,d,after,hlo,hn,ht,hp,ChunkSpecInvariant.preserved s b.toNat maxBody h.inv h.limitBound⟩
  have ph := h.inv.phase
  have cases : s.phase=0 ∨ s.phase=1 ∨ s.phase=2 ∨ s.phase=3 ∨ s.phase=4 ∨ s.phase=5 ∨ s.phase=6 ∨ s.phase=7 := by omega
  rcases cases with h0|h1|h2|h3|h4|h5|h6|h7
  · by_cases hd : 48≤b.toNat ∧ b.toNat≤57
    · by_cases digits : 8≤s.digits
      · apply bounded (n := 34) (by decide)
        exact ChunkHexDecimalDigitsRejectFull.contract B c ram src dst s b maxBody h.object h.inv h0 hd digits h.out h.state h.byte h.limit h.srcRam h.dstRam h.srcAlign h.dstAlign h.pc
      · by_cases size : 268435455<s.size
        · apply bounded (n := 39) (by decide)
          exact ChunkHexDecimalSizeRejectFull.contract B c ram src dst s b maxBody h.object h.inv h0 hd (by omega) size h.out h.state h.byte h.limit h.srcRam h.dstRam h.srcAlign h.dstAlign h.pc
        · apply bounded (n := 40) (by decide)
          exact ChunkHexDecimalAcceptFull.contract B c ram src dst s b maxBody h.object h.inv h0 hd (by omega) (by omega) h.out h.state h.byte h.limit h.srcRam h.dstRam h.srcAlign h.dstAlign h.pc
    · by_cases hLower : 97≤b.toNat ∧ b.toNat≤102
      · by_cases digits : 8≤s.digits
        · apply bounded (n := 40) (by decide)
          exact ChunkHexLowerDigitsRejectFull.contract B c ram src dst s b maxBody h.object h.inv h0 hLower digits h.out h.state h.byte h.limit h.srcRam h.dstRam h.srcAlign h.dstAlign h.pc
        · by_cases size : 268435455<s.size
          · apply bounded (n := 45) (by decide)
            exact ChunkHexLowerSizeRejectFull.contract B c ram src dst s b maxBody h.object h.inv h0 hLower (by omega) size h.out h.state h.byte h.limit h.srcRam h.dstRam h.srcAlign h.dstAlign h.pc
          · apply bounded (n := 46) (by decide)
            exact ChunkHexLowerAcceptFull.contract B c ram src dst s b maxBody h.object h.inv h0 hLower (by omega) (by omega) h.out h.state h.byte h.limit h.srcRam h.dstRam h.srcAlign h.dstAlign h.pc
      · by_cases hUpper : 65≤b.toNat ∧ b.toNat≤70
        · by_cases digits : 8≤s.digits
          · apply bounded (n := 42) (by decide)
            exact ChunkHexUpperDigitsRejectFull.contract B c ram src dst s b maxBody h.object h.inv h0 hUpper digits h.out h.state h.byte h.limit h.srcRam h.dstRam h.srcAlign h.dstAlign h.pc
          · by_cases size : 268435455<s.size
            · apply bounded (n := 47) (by decide)
              exact ChunkHexUpperSizeRejectFull.contract B c ram src dst s b maxBody h.object h.inv h0 hUpper (by omega) size h.out h.state h.byte h.limit h.srcRam h.dstRam h.srcAlign h.dstAlign h.pc
            · apply bounded (n := 48) (by decide)
              exact ChunkHexUpperAcceptFull.contract B c ram src dst s b maxBody h.object h.inv h0 hUpper (by omega) (by omega) h.out h.state h.byte h.limit h.srcRam h.dstRam h.srcAlign h.dstAlign h.pc
        · have hhex : ¬hexv b.toNat<16 := by
            intro hv
            rcases (ChunkByteFacts.classes b).mpr hv with hv|hv|hv
            · exact hd hv
            · exact hLower hv
            · exact hUpper hv
          by_cases hb : b.toNat=13
          · by_cases digits : s.digits=0
            · apply bounded (n := 41) (by decide)
              exact ChunkSizeEmptyFull.contract B c ram src dst s b maxBody h.object h.inv h.limitBound h0 hb digits h.out h.state h.byte h.limit h.srcRam h.dstRam h.srcAlign h.dstAlign h.pc
            · by_cases size : s.size≤maxBody-s.total
              · apply bounded (n := 51) (by decide)
                exact ChunkSizeAcceptFull.contract B c ram src dst s b maxBody h.object h.inv h.limitBound h0 hb (by omega) size h.out h.state h.byte h.limit h.srcRam h.dstRam h.srcAlign h.dstAlign h.pc
              · apply bounded (n := 56) (by decide)
                exact ChunkSizeSumRejectFull.contract B c ram src dst s b maxBody h.object h.inv h.limitBound h0 hb (by omega) (by omega) h.out h.state h.byte h.limit h.srcRam h.dstRam h.srcAlign h.dstAlign h.pc
          · apply bounded (n := 37) (by decide)
            exact ChunkSizeInvalidByteFull.contract B c ram src dst s b maxBody h.object h.inv h.limitBound h0 hhex hb h.out h.state h.byte h.limit h.srcRam h.dstRam h.srcAlign h.dstAlign h.pc
  · by_cases hb : b.toNat=10
    · by_cases size : s.size=0
      · apply bounded (n := 24) (by decide)
        exact ChunkPhase1ZeroFull.contract B c ram src dst s b maxBody h.object h1 hb h.inv.size size h.out h.state h.byte h.limit h.srcRam h.dstRam h.srcAlign h.dstAlign h.pc
      · apply bounded (n := 25) (by decide)
        exact ChunkPhase1DataFull.contract B c ram src dst s b maxBody h.object h1 hb h.inv.size size h.out h.state h.byte h.limit h.srcRam h.dstRam h.srcAlign h.dstAlign h.pc
    · apply bounded (n := 28) (by decide)
      exact ChunkPhase1RejectFull.contract B c ram src dst s b maxBody h.object h1 hb h.out h.state h.byte h.limit h.srcRam h.dstRam h.srcAlign h.dstAlign h.pc
  · by_cases size : s.size≤1
    · apply bounded (n := 30) (by decide)
      exact ChunkPhase2SmallFull.contract B c ram src dst s b maxBody h.object h2 h.inv.size size h.out h.state h.byte h.limit h.srcRam h.dstRam h.srcAlign h.dstAlign h.pc
    · apply bounded (n := 32) (by decide)
      exact ChunkPhase2DecrementFull.contract B c ram src dst s b maxBody h.object h2 h.inv.size (by omega) h.out h.state h.byte h.limit h.srcRam h.dstRam h.srcAlign h.dstAlign h.pc
  · by_cases hb : b.toNat=13
    · apply bounded (n := 27) (by decide)
      exact ChunkPhase3AcceptFull.contract B c ram src dst s b maxBody h.object h3 hb h.out h.state h.byte h.limit h.srcRam h.dstRam h.srcAlign h.dstAlign h.pc
    · apply bounded (n := 29) (by decide)
      exact ChunkPhase3RejectFull.contract B c ram src dst s b maxBody h.object h3 hb h.out h.state h.byte h.limit h.srcRam h.dstRam h.srcAlign h.dstAlign h.pc
  · by_cases hb : b.toNat=10
    · apply bounded (n := 24) (by decide)
      exact ChunkPhase4AcceptFull.contract B c ram src dst s b maxBody h.object h4 hb h.out h.state h.byte h.limit h.srcRam h.dstRam h.srcAlign h.dstAlign h.pc
    · apply bounded (n := 27) (by decide)
      exact ChunkPhase4RejectFull.contract B c ram src dst s b maxBody h.object h4 hb h.out h.state h.byte h.limit h.srcRam h.dstRam h.srcAlign h.dstAlign h.pc
  · by_cases hb : b.toNat=13
    · apply bounded (n := 26) (by decide)
      exact ChunkPhase5AcceptFull.contract B c ram src dst s b maxBody h.object h5 hb h.out h.state h.byte h.limit h.srcRam h.dstRam h.srcAlign h.dstAlign h.pc
    · apply bounded (n := 29) (by decide)
      exact ChunkPhase5RejectFull.contract B c ram src dst s b maxBody h.object h5 hb h.out h.state h.byte h.limit h.srcRam h.dstRam h.srcAlign h.dstAlign h.pc
  · by_cases hb : b.toNat=10
    · apply bounded (n := 28) (by decide)
      exact ChunkPhase6AcceptFull.contract B c ram src dst s b maxBody h.object h6 hb h.out h.state h.byte h.limit h.srcRam h.dstRam h.srcAlign h.dstAlign h.pc
    · apply bounded (n := 31) (by decide)
      exact ChunkPhase6RejectFull.contract B c ram src dst s b maxBody h.object h6 hb h.out h.state h.byte h.limit h.srcRam h.dstRam h.srcAlign h.dstAlign h.pc
  · apply bounded (n := 29) (by decide)
    exact ChunkPhase7RejectFull.contract B c ram src dst s b maxBody h.object h7 h.out h.state h.byte h.limit h.srcRam h.dstRam h.srcAlign h.dstAlign h.pc
end E5R.Thermostat.ChunkStep
