import Projects.thermostat.HeadRamWordTurn
import Projects.thermostat.HeadCopyRamSource
import Projects.thermostat.AlignedCopyLoop
open E5R E5R.Thermostat
namespace E5R.Thermostat.HeadRamCopyLoop
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst : Word) (ws : List Word)
    (hn : 0<ws.length) (hp : c.pc = 0x80005212#32) (h16 : c.get 16 = src) (h14 : c.get 14 = dst)
    (h13 : c.get 13 = dst+BitVec.ofNat 32 (4*ws.length))
    (hs : HeadCopyRamSource.Source B ram src ws) (apart : src.toNat+4*ws.length≤dst.toNat) (ha : dst.toNat%4=0)
    (hm : Memory.Block B dst (4*ws.length)) (htop : dst.toNat+4*ws.length<2^32) :
    ∃ d, Quiet.Steps B img (5*ws.length) ⟨c,ram⟩ ⟨d,AlignedCopyLoop.writes ram dst ws⟩ ∧ d.pc = 0x80005222#32 ∧
      d.get 14 = dst+BitVec.ofNat 32 (4*ws.length) ∧ d.get 16 = src+BitVec.ofNat 32 (4*ws.length) ∧
      (∀ r : Reg, r ≠ 14 → r ≠ 16 → r ≠ 17 → d.get r = c.get r) ∧ d.sameCsr c := by
  induction ws generalizing c ram src dst with
  | nil => simp only [List.length_nil] at hn;omega
  | cons w ws ih =>
    have hlen : (w::ws).length = ws.length+1 := rfl
    have hram : B.inRam dst 4 = true := by
      simpa only [BitVec.add_zero] using Memory.block_access hm (off := 0) (by decide) (by rw [hlen];omega)
    have hnext : (dst+4#32).toNat = dst.toNat+4 := WordZero.add_nat dst 4 (by rw [hlen] at htop;omega)
    have hend := WordZero.add_nat dst (4*(w::ws).length) htop
    have ht : taken .ltu (dst+4#32) (dst+BitVec.ofNat 32 (4*(w::ws).length)) = decide (0<ws.length) := by
      change decide ((dst+4#32).toNat < (dst+BitVec.ofNat 32 (4*(w::ws).length)).toNat) = _
      rw [hnext,hend,hlen]
      have hh : dst.toNat+4 < dst.toNat+4*(ws.length+1) ↔ 0<ws.length := by omega
      simp only [hh]
    have hhead := HeadCopyRamSource.head hs
    obtain ⟨a,ta,apc,a14,a16,ar,ac⟩ := HeadRamWordTurn.contract B c ram src dst _ w (decide (0<ws.length))
      hp h16 h14 h13 hs.aligned ha hhead.1 hhead.2 hram ht
    by_cases hz : ws=[]
    · subst ws
      refine ⟨a,?_,?_,?_,?_,ar,ac⟩
      · simpa only [AlignedCopyLoop.writes,List.length_cons,List.length_nil,Nat.mul_one] using ta
      · simpa only [List.length_nil,show decide (0<0)=false by decide,Bool.false_eq_true,ite_false] using apc
      · exact a14
      · exact a16
    · have hpos : 0<ws.length := List.length_pos_iff.mpr hz
      have heq (p : Word) : (p+4#32)+BitVec.ofNat 32 (4*ws.length) = p+BitVec.ofNat 32 (4*(w::ws).length) := by
        rw [BitVec.add_assoc,←BitVec.ofNat_add,hlen,show 4+4*ws.length=4*(ws.length+1) by omega]
      have hm' : Memory.Block B (dst+4#32) (4*ws.length) := Memory.sub_block hm (by omega) (by rw [hlen];omega)
      obtain ⟨d,td,dpc,d14,d16,dr,dc⟩ := ih a (ramWrite ram dst w .w) (src+4#32) (dst+4#32) hpos
        (by simpa only [decide_eq_true hpos,ite_true] using apc) a16 a14
        (by rw [ar 13 (by decide) (by decide) (by decide),h13,heq])
        (HeadCopyRamSource.tail_after hs dst w hpos apart (by omega)) (by
          have snext := WordZero.add_nat src 4 (by have := dst.isLt;rw [hlen] at apart;omega)
          rw [snext,hnext];rw [hlen] at apart;omega) (by rw [hnext];omega) hm' (by rw [hnext,hlen] at *;omega)
      refine ⟨d,?_,dpc,d14.trans (heq dst),d16.trans (heq src),?_,dc.trans ac⟩
      · have hh := ta.trans td
        simpa only [AlignedCopyLoop.writes,hlen,Nat.mul_add,Nat.mul_one,Nat.add_comm] using hh
      · intro reg h14 h16 h17
        exact (dr reg h14 h16 h17).trans (ar reg h14 h16 h17)

end E5R.Thermostat.HeadRamCopyLoop
