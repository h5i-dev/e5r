import Projects.thermostat.ResponseHeadNoDecimal
import Projects.thermostat.ResponseHeadSelectYes
import Projects.thermostat.ResponseHeadSetupDecResume
import Projects.thermostat.HttpDecEffect
import Projects.thermostat.ResponseHeadEnvelope
import Projects.thermostat.ResponseHeadPlan
namespace E5R.Thermostat.ResponseHeadDecimal
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (frame dst : Word) (pos status body : Nat) :=
  if ResponseHeadSpec.hasBody status then HttpDecMemory.memory ram frame dst pos body else ram

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (frame dst : Word) (pos status body : Nat)
    (hstatus : status≤599) (hbody : body≤832) (hpos : pos≤94)
    (h2 : c.get 2=frame+16#32) (h11 : c.get 11=BitVec.ofNat 32 pos) (h10 : c.get 10=1#32)
    (h18 : c.get 18=1#32) (h23 : c.get 23=dst) (hm : Memory.Block B frame 96) (ha : frame.toNat%4=0)
    (hd : Memory.Block B dst 192) (hsep : WordRegions.Disjoint frame 96 dst 192)
    (hc : ramRead ram (frame+40#32) .w=192#32) (hs : ramRead ram (frame+36#32) .w=BitVec.ofNat 32 status)
    (hb : ramRead ram (frame+28#32) .w=BitVec.ofNat 32 body) (hp : c.pc=0x80004076#32) :
    ∃ d n, n≤143 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,memory ram frame dst pos status body⟩ ∧
      d.pc=0x800040ac#32 ∧ d.get 12=BitVec.ofNat 32 (pos+(ResponseHeadPlan.decimal status body).length) ∧
      ResponseHeadCallee.Keep c d [] ∧ d.sameCsr c ∧
      OutputEffect.Effect B ram (memory ram frame dst pos status body) frame dst 16 pos (ResponseHeadPlan.decimal status body) := by
  cases hhas : ResponseHeadSpec.hasBody status with
  | false =>
    obtain ⟨d,n,hn,td,pd,v12,fd,kd⟩ := ResponseHeadNoDecimal.contract B c ram frame dst (BitVec.ofNat 32 pos) (BitVec.ofNat 32 body)
      status hstatus hhas h2 h11 h10 h18 h23 hm ha hc hs hb hp
    refine ⟨d,n,by omega,?_,pd,?_,fd,kd,?_⟩
    · simpa only [memory,hhas,Bool.false_eq_true,ite_false] using td
    · simpa only [ResponseHeadPlan.decimal,hhas,Bool.false_eq_true,ite_false,List.length_nil,Nat.add_zero] using v12
    · simp only [memory,ResponseHeadPlan.decimal,hhas,Bool.false_eq_true,ite_false]
      exact ⟨Bytes.empty B ram _,fun _ _ _ => rfl⟩
  | true =>
    have ht : 200≤status ∧ status≠204 ∧ status≠304 := of_decide_eq_true hhas
    obtain ⟨a,ta,pa,a12,a11,a10,a13,a1,fa,ka⟩ := ResponseHeadSelectYes.contract B c ram frame dst (BitVec.ofNat 32 pos) (BitVec.ofNat 32 body)
      status hstatus h2 h11 h10 h18 h23 hm ha hc hs hb (by omega) ht.2.2 ht.2.1 hp
    have a2 := (fa 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2
    obtain ⟨b,tb,hret,b10,b11,he⟩ := HttpDecEffect.contract B a ram frame dst pos body hbody hpos pa a2 a10 a11 a12 a13
      (by simpa only [BitVec.add_zero] using Memory.sub_block (off := 0) hm (by decide : 0<16) (by decide : 0+16≤96))
      ha hd (WordRegions.shrink hsep (by decide) (by decide))
    have pb : b.pc=0x800040a4#32 := by rw [hret.pc,a1];decide +kernel
    have be : ResponseHeadEnvelope.Frame ram (HttpDecMemory.memory ram frame dst pos body) frame dst :=
      ResponseHeadEnvelope.effect he (by decide) (by have hh := ReplyJsonBounds.decimal_length 3 body (by decide) (by change body<1000;omega);omega)
    have bcap := (ResponseHeadEnvelope.word be hsep 40 (by decide) (by decide)).trans hc
    have b2 := hret.sp.trans a2
    have b23 := hret.x23.trans ((fa 23 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h23)
    obtain ⟨d,tc,pd,d13,d12,fc,kc⟩ := ResponseHeadSetupDecResume.contract B b (HttpDecMemory.memory ram frame dst pos body) frame dst
      (BitVec.ofNat 32 (pos+(ReplyJson.decimal body).length)) 0#32 0#32 b2 b11 b23 hm ha bcap b10 pb
    refine ⟨d,14+HttpDec.time body+3,by have hh := HttpDec.time_bound body hbody;omega,?_,pd,?_,?_,kc.trans (hret.csr.trans ka),?_⟩
    · simpa only [memory,hhas,ite_true] using (ta.trans tb).trans tc
    · simpa only [ResponseHeadPlan.decimal,hhas,ite_true] using d12
    · intro r hr _
      apply (fc r ?_ ?_).trans
      apply (ResponseHeadCallee.returned hret r hr).trans
      apply fa r
      all_goals intro heq;subst r;simp [ResponseHeadCallee.Registers] at hr
    · simpa only [memory,ResponseHeadPlan.decimal,hhas,ite_true] using he
end E5R.Thermostat.ResponseHeadDecimal
