import Projects.thermostat.HttpPutCopy
import Projects.thermostat.HttpPutReject
namespace E5R.Thermostat.HttpPut
open E5R E5R.Thermostat

def duration (cap pos n : Nat) : Nat := if pos+n≤cap then if n=0 then 9 else 7*n+15 else 7

def memory (ram : Word → BitVec 8) (dst cap : Word) (pos : Nat) (xs : List (BitVec 8)) :=
  if pos+xs.length≤cap.toNat then ByteWrite.write ram (dst+BitVec.ofNat 32 pos) xs else ram

/-- Every capacity outcome of the real HTTP header append routine. Invalid
    or empty slices are never dereferenced on the corresponding paths. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst cap : Word)
    (pos : Nat) (xs : List (BitVec 8)) (hp32 : pos<2^32) (hn32 : xs.length<2^32)
    (hp : c.pc=0x80004122#32) (h10 : c.get 10=dst) (h11 : c.get 11=cap)
    (h12 : c.get 12=BitVec.ofNat 32 pos) (h13 : c.get 13=src) (h14 : c.get 14=BitVec.ofNat 32 xs.length)
    (hs : pos+xs.length≤cap.toNat → xs≠[] → ReadBytes.Span B img ram src xs)
    (hd : pos+xs.length≤cap.toNat → xs≠[] → Memory.Block B (dst+BitVec.ofNat 32 pos) xs.length)
    (hsep : pos+xs.length≤cap.toNat → xs≠[] → WordRegions.Disjoint src xs.length (dst+BitVec.ofNat 32 pos) xs.length) :
    ∃ d, Quiet.Steps B img (duration cap.toNat pos xs.length) ⟨c,ram⟩ ⟨d,memory ram dst cap pos xs⟩ ∧
      FormatCursor.Returned c d ∧ d.get 10=(if pos+xs.length≤cap.toNat then 1#32 else 0#32) ∧
      (pos+xs.length≤cap.toNat → d.get 11=BitVec.ofNat 32 (pos+xs.length)) ∧ HttpPutCopy.Frame c d := by
  by_cases hc : pos+xs.length≤cap.toNat
  · by_cases hz : xs=[]
    · subst xs
      simp only [List.length_nil] at hc
      obtain ⟨d,td,hr,d10,d11,hf⟩ := HttpPutCopy.empty B c ram cap pos (by simpa using hc) hp h11 h12 h14
      refine ⟨d,?_,hr,?_,?_,hf⟩
      · simpa only [duration,memory,hc,ite_true,List.length_nil,ByteWrite.write] using td
      · simpa only [List.length_nil,hc,ite_true] using d10
      · intro _;simpa only [List.length_nil,Nat.add_zero] using d11
    · obtain ⟨d,td,hr,d10,d11,hf⟩ := HttpPutCopy.nonempty B c ram src dst cap pos xs hz hc hp h10 h11 h12 h13 h14 (hs hc hz) (hd hc hz) (hsep hc hz)
      refine ⟨d,?_,hr,?_,fun _ => d11,hf⟩
      · simpa only [duration,memory,hc,ite_true,List.length_eq_zero_iff,if_neg hz] using td
      · simpa only [List.length_nil,hc,ite_true] using d10
  · obtain ⟨d,td,pd,d15,d16,d17,d10,dr,dc⟩ := HttpPutReject.contract B c ram cap pos xs.length hp32 hn32 hc h11 h12 h14 hp
    have hf : HttpPutCopy.Frame c d := fun r h5 h10 h11 h13 h15 h16 h17 => dr r h15 h16 h17 h10
    refine ⟨d,?_,HttpPutCopy.returned pd dc hf,?_,fun hh => False.elim (hc hh),hf⟩
    · simpa only [duration,memory,hc,ite_false] using td
    · simpa only [hc,ite_false] using d10

theorem bytes {B ram dst cap pos xs}
    (hc : pos+xs.length≤cap.toNat) (hm : Memory.Block B (dst+BitVec.ofNat 32 pos) xs.length)
    (hl : xs.length<2^32) : Bytes.Span B (memory ram dst cap pos xs) (dst+BitVec.ofNat 32 pos) xs := by
  rw [memory,if_pos hc]
  exact ByteWrite.span hm hl
end E5R.Thermostat.HttpPut
