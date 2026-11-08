import Projects.thermostat.OutputEffect
import Projects.thermostat.HttpPut
namespace E5R.Thermostat.HttpPutEffect
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp src dst : Word)
    (pos : Nat) (xs : List (BitVec 8)) (hf : pos+xs.length≤192)
    (hp : c.pc=0x80004122#32) (h10 : c.get 10=dst) (h11 : c.get 11=192#32)
    (h12 : c.get 12=BitVec.ofNat 32 pos) (h13 : c.get 13=src) (h14 : c.get 14=BitVec.ofNat 32 xs.length)
    (hs : ReadBytes.Span B img ram src xs) (hm : Memory.Block B dst 192)
    (hd : WordRegions.Disjoint src xs.length dst 192) :
    ∃ d, Quiet.Steps B img (HttpPut.duration 192 pos xs.length) ⟨c,ram⟩ ⟨d,HttpPut.memory ram dst 192#32 pos xs⟩ ∧
      FormatCursor.Returned c d ∧ d.get 10=1#32 ∧ d.get 11=BitVec.ofNat 32 (pos+xs.length) ∧
      OutputEffect.Effect B ram (HttpPut.memory ram dst 192#32 pos xs) sp dst 0 pos xs := by
  obtain ⟨d,td,hr,d10,d11,_⟩ := HttpPut.contract B c ram src dst 192#32 pos xs (by omega) (by omega) hp h10 h11 h12 h13 h14
    (fun _ _ => hs) (fun _ hn => Memory.sub_block hm (List.length_pos_iff.mpr hn) hf)
    (fun _ _ => fun i => Subregion.right hd pos xs.length hf i)
  have hfc : pos+xs.length≤(192#32).toNat := hf
  have he : HttpPut.memory ram dst 192#32 pos xs=ByteWrite.write ram (dst+BitVec.ofNat 32 pos) xs := by
    rw [HttpPut.memory,if_pos hfc]
  refine ⟨d,td,hr,?_,d11 hf,?_,?_⟩
  · simpa only [hfc,ite_true] using d10
  · rw [he]
    by_cases hz : xs=[]
    · subst xs;exact Bytes.empty B ram _
    · exact ByteWrite.span (Memory.sub_block hm (List.length_pos_iff.mpr hz) hf) (by omega)
  · intro x _ ho
    rw [he]
    exact ByteWrite.frame ram _ x xs ho
end E5R.Thermostat.HttpPutEffect
