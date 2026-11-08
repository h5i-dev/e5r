import Projects.thermostat.HttpPutGuard
import Projects.thermostat.HttpPutSetup
import Projects.thermostat.HttpPutLoop
import Projects.thermostat.HttpPutReturn
import Projects.thermostat.HttpPutEmpty
import Projects.thermostat.CopyRegs
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.HttpPutCopy
open E5R E5R.Thermostat

def Frame (c d : Core) : Prop := ∀ r : Reg, r≠5 → r≠10 → r≠11 → r≠13 → r≠15 → r≠16 → r≠17 → d.get r=c.get r

theorem returned {c d} (hp : d.pc=c.get 1 &&& ~~~1) (hc : d.sameCsr c) (hf : Frame c d) :
    FormatCursor.Returned c d := by
  apply CopyRegs.returned hp (hf 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hc
  intro r hr
  exact hf r (CopyRegs.ne_low r 5 hr (by decide) (by decide) (by decide) (by decide))
    (CopyRegs.ne_low r 10 hr (by decide) (by decide) (by decide) (by decide))
    (CopyRegs.ne_low r 11 hr (by decide) (by decide) (by decide) (by decide))
    (CopyRegs.ne_low r 13 hr (by decide) (by decide) (by decide) (by decide))
    (CopyRegs.ne_low r 15 hr (by decide) (by decide) (by decide) (by decide))
    (CopyRegs.ne_low r 16 hr (by decide) (by decide) (by decide) (by decide))
    (CopyRegs.ne_low r 17 hr (by decide) (by decide) (by decide) (by decide))

/-- Complete actual put for every nonempty checked byte slice that fits. -/
theorem nonempty (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst cap : Word)
    (pos : Nat) (xs : List (BitVec 8)) (hn : xs≠[]) (hc : pos+xs.length≤cap.toNat)
    (hp : c.pc=0x80004122#32) (h10 : c.get 10=dst) (h11 : c.get 11=cap)
    (h12 : c.get 12=BitVec.ofNat 32 pos) (h13 : c.get 13=src) (h14 : c.get 14=BitVec.ofNat 32 xs.length)
    (hs : ReadBytes.Span B img ram src xs) (hd : Memory.Block B (dst+BitVec.ofNat 32 pos) xs.length)
    (hsep : WordRegions.Disjoint src xs.length (dst+BitVec.ofNat 32 pos) xs.length) :
    ∃ d, Quiet.Steps B img (7*xs.length+15) ⟨c,ram⟩ ⟨d,ByteWrite.write ram (dst+BitVec.ofNat 32 pos) xs⟩ ∧
      FormatCursor.Returned c d ∧ d.get 10=1#32 ∧ d.get 11=BitVec.ofNat 32 (pos+xs.length) ∧ Frame c d := by
  obtain ⟨a,ta,pa,a15,a16,a17,ar,ac⟩ := HttpPutGuard.contract B c ram cap pos xs.length hc h11 h12 h14 hp
  obtain ⟨b,tb,pb,b16,b15,br,bc⟩ := HttpPutSetup.contract B a ram src cap pos xs.length hc (List.length_pos_iff.mpr hn)
    ((ar 12 (by decide) (by decide) (by decide)).trans h12)
    ((ar 13 (by decide) (by decide) (by decide)).trans h13)
    ((ar 14 (by decide) (by decide) (by decide)).trans h14) a15 pa
  have af : Frame c a := fun r h5 h10 h11 h13 h15 h16 h17 => ar r h15 h16 h17
  have bf : Frame c b := fun r h5 h10 h11 h13 h15 h16 h17 => (br r h16 h15).trans (af r h5 h10 h11 h13 h15 h16 h17)
  obtain ⟨u,tu,pu,u13,u15,ur,uc⟩ := HttpPutLoop.contract B b ram src dst cap pos xs hn hc pb
    ((br 10 (by decide) (by decide)).trans ((ar 10 (by decide) (by decide) (by decide)).trans h10))
    ((br 11 (by decide) (by decide)).trans ((ar 11 (by decide) (by decide) (by decide)).trans h11))
    ((br 13 (by decide) (by decide)).trans ((ar 13 (by decide) (by decide) (by decide)).trans h13)) b15 b16 hs hd hsep
  have uf : Frame c u := fun r h5 h10 h11 h13 h15 h16 h17 => (ur r h5 h13 h15 h17).trans (bf r h5 h10 h11 h13 h15 h16 h17)
  have u12 : u.get 12=BitVec.ofNat 32 pos :=
    (ur 12 (by decide) (by decide) (by decide) (by decide)).trans ((br 12 (by decide) (by decide)).trans ((ar 12 (by decide) (by decide) (by decide)).trans h12))
  have u14 : u.get 14=BitVec.ofNat 32 xs.length :=
    (ur 14 (by decide) (by decide) (by decide) (by decide)).trans ((br 14 (by decide) (by decide)).trans ((ar 14 (by decide) (by decide) (by decide)).trans h14))
  obtain ⟨d,td,pd,d10,d11,dr,dc⟩ := HttpPutReturn.contract B u _ _ _ pu u12 u14
  have df : Frame c d := fun r h5 h10 h11 h13 h15 h16 h17 => (dr r h10 h11).trans (uf r h5 h10 h11 h13 h15 h16 h17)
  refine ⟨d,?_,returned ?_ (dc.trans (uc.trans (bc.trans ac))) df,d10,?_,df⟩
  · have tt := ((ta.trans tb).trans tu).trans td
    rw [show ((5+7)+7*xs.length)+3=7*xs.length+15 by omega] at tt
    exact tt
  · rw [pd,uf 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rw [d11,←BitVec.ofNat_add,Nat.add_comm]
/-- Empty put returns successfully without dereferencing either slice. -/
theorem empty (B : Board) (c : Core) (ram : Word → BitVec 8) (cap : Word) (pos : Nat)
    (hc : pos≤cap.toNat) (hp : c.pc=0x80004122#32)
    (h11 : c.get 11=cap) (h12 : c.get 12=BitVec.ofNat 32 pos) (h14 : c.get 14=0#32) :
    ∃ d, Quiet.Steps B img 9 ⟨c,ram⟩ ⟨d,ram⟩ ∧ FormatCursor.Returned c d ∧
      d.get 10=1#32 ∧ d.get 11=BitVec.ofNat 32 pos ∧ Frame c d := by
  obtain ⟨a,ta,pa,a15,a16,a17,ar,ac⟩ := HttpPutGuard.contract B c ram cap pos 0 (by omega) h11 h12 h14 hp
  have a14 : a.get 14=0#32 := (ar 14 (by decide) (by decide) (by decide)).trans h14
  have a12 : a.get 12=BitVec.ofNat 32 pos := (ar 12 (by decide) (by decide) (by decide)).trans h12
  have tu := HttpPutEmpty.contract B a ram pa a14
  obtain ⟨d,td,pd,d10,d11,dr,dc⟩ := HttpPutReturn.contract B (a.goto 0x80004166#32) ram _ _ rfl a12 a14
  have df : Frame c d := fun r h5 h10 h11 h13 h15 h16 h17 => (dr r h10 h11).trans (ar r h15 h16 h17)
  refine ⟨d,(ta.trans tu).trans td,returned ?_ (dc.trans ac) df,d10,?_,df⟩
  · rw [pd]
    change a.get 1 &&& ~~~1=c.get 1 &&& ~~~1
    rw [ar 1 (by decide) (by decide) (by decide)]
  · rw [d11,BitVec.zero_add]
end E5R.Thermostat.HttpPutCopy
