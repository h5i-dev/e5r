import Projects.thermostat.ReadBytes
import Projects.thermostat.SendBodyHead
import Projects.thermostat.SendBodyPayload
namespace E5R.Thermostat.SendSelect
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (payload : List (BitVec 8)) (status : Nat) (head : Bool)
    (hlo : 200≤status) (hhi : status≤599) (h10 : c.get 10=1#32)
    (h20 : c.get 20=BitVec.ofNat 32 payload.length) (h21 : c.get 21=BitVec.ofNat 32 status)
    (h23 : c.get 23=ResponseHeadBodyMath.boolWord head) (hp : c.pc=0x800003c0#32) :
    ∃ d n, n≤12 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80000408#32 ∧
      d.get 10=BitVec.ofNat 32 (ResponseHeadSpec.body status head payload).length ∧
      (∀ r : Reg, r≠12 → r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  cases head
  · obtain ⟨d,td,pd,d12,d10,fd,kd⟩ := SendBodyPayload.contract B c ram (BitVec.ofNat 32 payload.length) status hlo hhi h10 h20 h21 h23 hp
    refine ⟨d,12,by decide,td,pd,?_,fd,kd⟩
    cases hh : ResponseHeadSpec.hasBody status <;> simpa [ResponseHeadSpec.body,hh] using d10
  · obtain ⟨d,td,pd,d12,d10,fd,kd⟩ := SendBodyHead.contract B c ram (BitVec.ofNat 32 payload.length) status hlo hhi h10 h20 h21 h23 hp
    exact ⟨d,4,by decide,td,pd,by simpa [ResponseHeadSpec.body] using d10,fd,kd⟩

theorem length (payload : List (BitVec 8)) (status : Nat) (head : Bool) :
    (ResponseHeadSpec.body status head payload).length≤payload.length := by
  unfold ResponseHeadSpec.body
  split
  · simp
  · exact Nat.le_refl _

theorem span {B ram p payload status head} (h : ReadBytes.Span B img ram p payload) :
    ReadBytes.Span B img ram p (ResponseHeadSpec.body status head payload) := by
  unfold ResponseHeadSpec.body
  split
  · refine ⟨by decide,?_,?_⟩
    · have := p.isLt;change p.toNat+0≤2^32;omega
    · intro i;have := i.isLt;simp at this
  · exact h
end E5R.Thermostat.SendSelect
