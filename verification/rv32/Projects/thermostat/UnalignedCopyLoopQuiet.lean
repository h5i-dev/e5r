-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.UnalignedCopyLoop
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.UnalignedCopyTurnQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.UnalignedCopyLoop
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst previous shift comp : Word) (nexts : List Word)
    (hn : 0<nexts.length) (hp : c.pc=0x8000525e#32)
    (h6 : c.get 6=src) (h7 : c.get 7=comp) (h13 : c.get 13=dst+BitVec.ofNat 32 (4*(nexts.length+1)))
    (h14 : c.get 14=dst) (h16 : c.get 16=shift) (h17 : c.get 17=previous)
    (hs : AlignedSource.Source B (src+4#32) nexts) (ha : dst.toNat%4=0)
    (hm : Memory.Block B dst (4*(nexts.length+1))) (hw : dst.toNat+4*(nexts.length+1)<2^32) :
    ∃ d, Quiet.Steps B img (10*nexts.length) ⟨c,ram⟩ ⟨d,AlignedCopyLoop.writes ram dst (mixes previous nexts shift comp)⟩ ∧
      d.pc=0x80005280#32 ∧ d.get 6=src+BitVec.ofNat 32 (4*nexts.length) ∧ d.get 14=dst+BitVec.ofNat 32 (4*nexts.length) ∧
      d.get 17=lastWord previous nexts ∧
      (∀ r : Reg, r≠6 → r≠14 → r≠17 → r≠28 → r≠29 → d.get r=c.get r) ∧ d.sameCsr c := by
  induction nexts generalizing c ram src dst previous with
  | nil => simp only [List.length_nil] at hn;omega
  | cons w ws ih =>
    have hlen : (w::ws).length=ws.length+1 := rfl
    have hnext4 : (dst+4#32).toNat=dst.toNat+4 := WordZero.add_nat dst 4 (by rw [hlen] at hw;omega)
    have hnext8 : (dst+8#32).toNat=dst.toNat+8 := WordZero.add_nat dst 8 (by rw [hlen] at hw;omega)
    have hend := WordZero.add_nat dst (4*((w::ws).length+1)) hw
    have ht : taken .ltu (dst+8#32) (dst+BitVec.ofNat 32 (4*((w::ws).length+1)))=decide (0<ws.length) := by
      change decide ((dst+8#32).toNat < (dst+BitVec.ofNat 32 (4*((w::ws).length+1))).toNat)=_
      rw [hnext8,hend,hlen]
      have hh : dst.toNat+8<dst.toNat+4*(ws.length+1+1) ↔ 0<ws.length := by omega
      simp only [hh]
    have hhead := AlignedSource.head hs
    obtain ⟨a,ta,apc,a6,a14,a17,ar,ac⟩ := E5R.Thermostat.UnalignedCopyTurn.contract_quiet B c ram src dst _ previous w shift comp (decide (0<ws.length))
      hp h6 h7 h13 h14 h16 h17 hs.aligned ha hhead.1 hhead.2
      (by simpa only [BitVec.add_zero] using Memory.block_access hm (off := 0) (by decide) (by rw [hlen];omega)) ht
    by_cases hz : ws=[]
    · subst ws
      refine ⟨a,?_,?_,?_,?_,a17,ar,ac⟩
      · simpa only [mixes,AlignedCopyLoop.writes,List.length_cons,List.length_nil,Nat.mul_one] using ta
      · simpa only [List.length_nil,show decide (0<0)=false by decide,Bool.false_eq_true,ite_false] using apc
      · exact a6
      · exact a14
    · have hpos : 0<ws.length := List.length_pos_iff.mpr hz
      have end_eq : (dst+4#32)+BitVec.ofNat 32 (4*(ws.length+1))=dst+BitVec.ofNat 32 (4*((w::ws).length+1)) := by
        rw [BitVec.add_assoc,←BitVec.ofNat_add,hlen,show 4+4*(ws.length+1)=4*(ws.length+1+1) by omega]
      have ptr_eq (p : Word) : (p+4#32)+BitVec.ofNat 32 (4*ws.length)=p+BitVec.ofNat 32 (4*(w::ws).length) := by
        rw [BitVec.add_assoc,←BitVec.ofNat_add,hlen,show 4+4*ws.length=4*(ws.length+1) by omega]
      obtain ⟨d,td,dpc,d6,d14,d17,dr,dc⟩ := ih a (ramWrite ram dst (UnalignedCopyTurn.mix previous w shift comp) .w) (src+4#32) (dst+4#32) w hpos
        (by simpa only [decide_eq_true hpos,ite_true] using apc) a6
        ((ar 7 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h7)
        (by rw [ar 13 (by decide) (by decide) (by decide) (by decide) (by decide),h13,end_eq]) a14
        ((ar 16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h16) a17
        (AlignedSource.tail hs) (by rw [hnext4];omega)
        (Memory.sub_block hm (off := 4) (m := 4*(ws.length+1)) (by omega) (by rw [hlen];omega))
        (by rw [hnext4];rw [hlen] at hw;omega)
      refine ⟨d,?_,dpc,d6.trans (ptr_eq src),d14.trans (ptr_eq dst),d17,?_,dc.trans ac⟩
      · have hh := ta.trans td
        simpa only [mixes,AlignedCopyLoop.writes,hlen,Nat.mul_add,Nat.mul_one,Nat.add_comm] using hh
      · intro reg h6 h14 h17 h28 h29
        exact (dr reg h6 h14 h17 h28 h29).trans (ar reg h6 h14 h17 h28 h29)

end E5R.Thermostat.UnalignedCopyLoop
