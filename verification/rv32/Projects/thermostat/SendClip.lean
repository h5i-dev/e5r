import Projects.thermostat.SendClipBig
import Projects.thermostat.SendClipSmall
namespace E5R.Thermostat.SendClip
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (body : Nat) (hbody : body<2^32)
    (h20 : c.get 20=832#32) (h11 : c.get 11=BitVec.ofNat 32 body) (hp : c.pc=0x8000039c#32) :
    ∃ d n, n≤2 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800003a2#32 ∧
      d.get 20=BitVec.ofNat 32 (min 832 body) ∧ (∀ r : Reg, r≠20 → d.get r=c.get r) ∧ d.sameCsr c := by
  by_cases hb : 832<body
  · obtain ⟨d,td,pd,fd,kd⟩ := SendClipBig.contract B c ram body hbody hb h20 h11 hp
    refine ⟨d,1,by decide,td,pd,?_,fun r _ => fd r,kd⟩
    rw [Nat.min_eq_left (by omega)]
    exact (fd 20).trans h20
  · obtain ⟨d,td,pd,d20,fd,kd⟩ := SendClipSmall.contract B c ram body hbody hb h20 h11 hp
    refine ⟨d,2,by decide,td,pd,?_,fd,kd⟩
    rw [Nat.min_eq_right (by omega)]
    exact d20
end E5R.Thermostat.SendClip
