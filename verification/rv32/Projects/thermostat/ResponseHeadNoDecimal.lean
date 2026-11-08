import Projects.thermostat.ResponseHeadSelectEarly
import Projects.thermostat.ResponseHeadSelect304
import Projects.thermostat.ResponseHeadSelect204
import Projects.thermostat.ResponseHeadCallee
import Projects.thermostat.ResponseHeadBodyMath
namespace E5R.Thermostat.ResponseHeadNoDecimal
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (frame dst pos body : Word)
    (status : Nat) (hstatus : status≤599) (hbody : ResponseHeadSpec.hasBody status=false)
    (h2 : c.get 2=frame+16#32) (h11 : c.get 11=pos) (h10 : c.get 10=1#32)
    (h18 : c.get 18=1#32) (h23 : c.get 23=dst) (hm : Memory.Block B frame 96) (ha : frame.toNat%4=0)
    (hc : ramRead ram (frame+40#32) .w=192#32) (hs : ramRead ram (frame+36#32) .w=BitVec.ofNat 32 status)
    (hb : ramRead ram (frame+28#32) .w=body) (hp : c.pc=0x80004076#32) :
    ∃ d n, n≤9 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800040ac#32 ∧
      d.get 12=pos ∧ ResponseHeadCallee.Keep c d [] ∧ d.sameCsr c := by
  have hn : ¬(200≤status ∧ status≠204 ∧ status≠304) := by
    intro hh
    have ht : ResponseHeadSpec.hasBody status=true := by simp [ResponseHeadSpec.hasBody,hh]
    rw [hbody] at ht;contradiction
  by_cases hsmall : status<200
  · obtain ⟨d,td,pd,v12,v11,v10,fd,kd⟩ := ResponseHeadSelectEarly.contract B c ram frame dst pos body status hstatus h2 h11 h10 h18 h23 hm ha hc hs hb hsmall hp
    refine ⟨d,5,by decide,td,pd,v12,?_,kd⟩
    intro r hr _
    apply fd r
    · intro he;subst r;simp [ResponseHeadCallee.Registers] at hr
    · intro he;subst r;simp [ResponseHeadCallee.Registers] at hr
    · intro he;subst r;simp [ResponseHeadCallee.Registers] at hr
  · by_cases heq : status=304
    · obtain ⟨d,td,pd,v12,v11,v10,fd,kd⟩ := ResponseHeadSelect304.contract B c ram frame dst pos body status hstatus h2 h11 h10 h18 h23 hm ha hc hs hb hsmall heq hp
      refine ⟨d,7,by decide,td,pd,v12,?_,kd⟩
      intro r hr _
      apply fd r
      · intro he;subst r;simp [ResponseHeadCallee.Registers] at hr
      · intro he;subst r;simp [ResponseHeadCallee.Registers] at hr
      · intro he;subst r;simp [ResponseHeadCallee.Registers] at hr
    · obtain ⟨d,td,pd,v12,v11,v10,fd,kd⟩ := ResponseHeadSelect204.contract B c ram frame dst pos body status hstatus h2 h11 h10 h18 h23 hm ha hc hs hb hsmall heq (by omega) hp
      refine ⟨d,9,by decide,td,pd,v12,?_,kd⟩
      intro r hr _
      apply fd r
      · intro he;subst r;simp [ResponseHeadCallee.Registers] at hr
      · intro he;subst r;simp [ResponseHeadCallee.Registers] at hr
      · intro he;subst r;simp [ResponseHeadCallee.Registers] at hr
end E5R.Thermostat.ResponseHeadNoDecimal
