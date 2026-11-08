import Projects.thermostat.ResponseHeadSetupCLEnd
import Projects.thermostat.HttpPutEffect
import Projects.thermostat.ResponseHeadCallee
set_option maxRecDepth 5000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.ResponseHeadAppendCLEnd
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (frame dst src count : Word) (pos : Nat) (xs : List (BitVec 8))
    (h2 : c.get 2=frame+16#32)  (h23 : c.get 23=dst) (hm : Memory.Block B frame 96) (ha : frame.toNat%4=0) (hc : ramRead ram (frame+40#32) .w=192#32) (h25 : c.get 25=count) (h19 : c.get 19=src) (h12 : c.get 12=BitVec.ofNat 32 pos) (hlen : count <<< 1=BitVec.ofNat 32 xs.length) (hfit : pos+xs.length≤192) (hs : ReadBytes.Span B img ram (src) xs) (hd : Memory.Block B dst 192) (hsep : WordRegions.Disjoint (src) xs.length dst 192) (hp : c.pc=0x800040ac#32) :
    ∃ d, Quiet.Steps B img (6+HttpPut.duration 192 pos xs.length) ⟨c,ram⟩ ⟨d,HttpPut.memory ram dst 192#32 pos xs⟩ ∧
      d.pc=0x800040be#32 ∧ ResponseHeadCallee.Keep c d [] ∧ d.sameCsr c ∧ d.get 10=1#32 ∧ d.get 11=BitVec.ofNat 32 (pos+xs.length) ∧ OutputEffect.Effect B ram (HttpPut.memory ram dst 192#32 pos xs) frame dst 0 pos xs := by
  obtain ⟨a,ta,pa,a11,a10,a14,a13,a1,fa,ka⟩ := ResponseHeadSetupCLEnd.contract B c ram frame dst (c.get 11) src count h2 (by rfl) h23 hm ha hc h25 h19 hp
  obtain ⟨d,td,hr,d10,d11,he⟩ := HttpPutEffect.contract B a ram frame (src) dst pos xs hfit pa a10 a11 ((fa 12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h12) a13 (a14.trans hlen) hs hd hsep
  refine ⟨d,ta.trans td,?_, ?_ ,?_ ,d10,d11,he⟩
  · rw [hr.pc,a1];decide +kernel
  · intro r hreg hnot
    apply (ResponseHeadCallee.returned hr r hreg).trans
    apply fa r
    · intro heq;subst r;simp [ResponseHeadCallee.Registers] at hreg
    · intro heq;subst r;simp [ResponseHeadCallee.Registers] at hreg
    · intro heq;subst r;simp [ResponseHeadCallee.Registers] at hreg
    · intro heq;subst r;simp [ResponseHeadCallee.Registers] at hreg
    · intro heq;subst r;simp [ResponseHeadCallee.Registers] at hreg
  · exact hr.csr.trans ka
end E5R.Thermostat.ResponseHeadAppendCLEnd
