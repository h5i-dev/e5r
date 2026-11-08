import Projects.thermostat.HttpDecHundredsSmall
import Projects.thermostat.HttpDecHundredsBig
import Projects.thermostat.HttpDecSmallQuotient
import Projects.thermostat.HttpDecOneChoice
import Projects.thermostat.HttpDecTwoChoice
import Projects.thermostat.HttpDecBigTens
import Projects.thermostat.HttpDecTensStore
import Projects.thermostat.HttpDecOnes
import Projects.thermostat.HttpDecDigitsData
set_option maxRecDepth 5000
namespace E5R.Thermostat.HttpDecDigits
open E5R E5R.Thermostat

def Frame (c d : Core) : Prop := ∀ r : Reg, r≠5 → r≠6 → r≠13 → r≠14 → r≠15 → r≠16 → r≠17 → d.get r=c.get r

def duration (n : Nat) := if n<10 then 28 else if n<100 then 32 else 37

/-- Actual digit assembly, including all skip branches and the real scratch
    stores. The final RAM bytes are the independent ordinary decimal encoding. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (n : Nat)
    (hn : n≤832) (hp : c.pc=0x800044e0#32) (h2 : c.get 2=sp)
    (h13 : c.get 13=BitVec.ofNat 32 n) (h14 : c.get 14=BitVec.ofNat 32 (n/100))
    (hm : Memory.Block B sp 16) :
    ∃ d, Quiet.Steps B img (duration n) ⟨c,ram⟩ ⟨d,ByteWrite.write ram (sp+4#32) (ReplyJson.decimal n)⟩ ∧
      d.pc=0x800043d6#32 ∧ d.get 2=sp ∧ d.get 14=0#32 ∧
      d.get 15=BitVec.ofNat 32 ((ReplyJson.decimal n).length-1) ∧ Frame c d ∧ d.sameCsr c := by
  by_cases hsmall : n<100
  · by_cases hone : n<10
    ·
      obtain ⟨a1,t1,p1,f1,k1⟩ := HttpDecHundredsSmall.contract B c ram n hn (h14) hsmall hp
      obtain ⟨a2,t2,p2,v2_15,v2_16,v2_17,f2,k2⟩ := HttpDecSmallQuotient.contract B a1 ram n hsmall ((f1 13 ).trans (h13)) p1
      obtain ⟨a3,t3,p3,f3,k3⟩ := HttpDecOneChoice.contract B a2 ram n hn (v2_16) hone p2
      let m4 := HttpDecOnes.memory ram sp n 0
      obtain ⟨a4,t4,p4,v4_14,v4_16,v4_17,v4_13,f4,k4⟩ := HttpDecOnes.contract B a3 ram sp n 0 hn (by decide) ((f3 2 ).trans ((f2 2 (by decide) (by decide) (by decide)).trans ((f1 2 ).trans (h2)))) ((f3 13 ).trans ((f2 13 (by decide) (by decide) (by decide)).trans ((f1 13 ).trans (h13)))) ((f3 15 ).trans (v2_15)) hm p3
      refine ⟨a4,?_, p4,((f4 2 (by decide) (by decide) (by decide) (by decide)).trans ((f3 2 ).trans ((f2 2 (by decide) (by decide) (by decide)).trans ((f1 2 ).trans (h2))))),(v4_14),?_,?_, k4.trans (k3.trans (k2.trans (k1)))⟩
      · have tt := (((t1).trans t2).trans t3).trans t4
        have he : m4=ByteWrite.write ram (sp+4#32) (ReplyJson.decimal n) := HttpDecDigitsData.one ram sp n hone
        change Quiet.Steps B img _ ⟨c,ram⟩ ⟨a4,m4⟩ at tt
        rw [he] at tt
        simpa only [duration,hone,ite_true] using tt
      · rw [HttpDecDigitsSpec.length n hn]
        simpa only [hone,ite_true] using (f4 15 (by decide) (by decide) (by decide) (by decide)).trans ((f3 15 ).trans (v2_15))
      · intro r h5 h6 h13 h14 h15 h16 h17
        exact (f4 r h14 h16 h17 h13).trans ((f3 r ).trans ((f2 r h15 h16 h17).trans ((f1 r ))))
    ·
      obtain ⟨a1,t1,p1,f1,k1⟩ := HttpDecHundredsSmall.contract B c ram n hn (h14) hsmall hp
      obtain ⟨a2,t2,p2,v2_15,v2_16,v2_17,f2,k2⟩ := HttpDecSmallQuotient.contract B a1 ram n hsmall ((f1 13 ).trans (h13)) p1
      obtain ⟨a3,t3,p3,f3,k3⟩ := HttpDecTwoChoice.contract B a2 ram n hn (v2_16) (by omega) p2
      let m4 := HttpDecTensStore.memory ram sp n 0
      obtain ⟨a4,t4,p4,v4_15,v4_16,f4,k4⟩ := HttpDecTensStore.contract B a3 ram sp n 0 (by decide) ((f3 2 ).trans ((f2 2 (by decide) (by decide) (by decide)).trans ((f1 2 ).trans (h2)))) (by rw [(f3 14 ).trans ((f2 14 (by decide) (by decide) (by decide)).trans ((f1 14 ).trans (h14))),show n/100=0 by omega]) (by rw [Nat.mod_eq_of_lt (show n/10<10 by omega)];exact (f3 16 ).trans (v2_16)) hm p3
      let m5 := HttpDecOnes.memory m4 sp n 1
      obtain ⟨a5,t5,p5,v5_14,v5_16,v5_17,v5_13,f5,k5⟩ := HttpDecOnes.contract B a4 m4 sp n 1 hn (by decide) ((f4 2 (by decide) (by decide)).trans ((f3 2 ).trans ((f2 2 (by decide) (by decide) (by decide)).trans ((f1 2 ).trans (h2))))) ((f4 13 (by decide) (by decide)).trans ((f3 13 ).trans ((f2 13 (by decide) (by decide) (by decide)).trans ((f1 13 ).trans (h13))))) (v4_15) hm p4
      refine ⟨a5,?_, p5,((f5 2 (by decide) (by decide) (by decide) (by decide)).trans ((f4 2 (by decide) (by decide)).trans ((f3 2 ).trans ((f2 2 (by decide) (by decide) (by decide)).trans ((f1 2 ).trans (h2)))))),(v5_14),?_,?_, k5.trans (k4.trans (k3.trans (k2.trans (k1))))⟩
      · have tt := ((((t1).trans t2).trans t3).trans t4).trans t5
        have he : m5=ByteWrite.write ram (sp+4#32) (ReplyJson.decimal n) := HttpDecDigitsData.two ram sp n (by omega) hsmall
        change Quiet.Steps B img _ ⟨c,ram⟩ ⟨a5,m5⟩ at tt
        rw [he] at tt
        simpa only [duration,show ¬n<10 by omega,hsmall,ite_false,ite_true] using tt
      · rw [HttpDecDigitsSpec.length n hn]
        simpa only [show ¬n<10 by omega,hsmall,ite_false,ite_true] using (f5 15 (by decide) (by decide) (by decide) (by decide)).trans (v4_15)
      · intro r h5 h6 h13 h14 h15 h16 h17
        exact (f5 r h14 h16 h17 h13).trans ((f4 r h15 h16).trans ((f3 r ).trans ((f2 r h15 h16 h17).trans ((f1 r )))))
  ·
    obtain ⟨a1,t1,p1,v1_15,f1,k1⟩ := HttpDecHundredsBig.contract B c ram n hn (h14) (by omega) hp
    let m2 := HttpDecBigTens.memory ram sp n
    obtain ⟨a2,t2,p2,v2_16,v2_17,v2_5,v2_14,v2_6,f2,k2⟩ := HttpDecBigTens.contract B a1 ram sp n hn (by omega) ((f1 2 (by decide)).trans (h2)) ((f1 13 (by decide)).trans (h13)) ((f1 14 (by decide)).trans (h14)) (v1_15) hm p1
    let m3 := HttpDecTensStore.memory m2 sp n 1
    obtain ⟨a3,t3,p3,v3_15,v3_16,f3,k3⟩ := HttpDecTensStore.contract B a2 m2 sp n 1 (by decide) ((f2 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((f1 2 (by decide)).trans (h2))) (v2_14) (by rw [v2_16,HttpDecTensMath.value n hn]) hm p2
    let m4 := HttpDecOnes.memory m3 sp n 2
    obtain ⟨a4,t4,p4,v4_14,v4_16,v4_17,v4_13,f4,k4⟩ := HttpDecOnes.contract B a3 m3 sp n 2 hn (by decide) ((f3 2 (by decide) (by decide)).trans ((f2 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((f1 2 (by decide)).trans (h2)))) ((f3 13 (by decide) (by decide)).trans ((f2 13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((f1 13 (by decide)).trans (h13)))) (v3_15) hm p3
    refine ⟨a4,?_, p4,((f4 2 (by decide) (by decide) (by decide) (by decide)).trans ((f3 2 (by decide) (by decide)).trans ((f2 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((f1 2 (by decide)).trans (h2))))),(v4_14),?_,?_, k4.trans (k3.trans (k2.trans (k1)))⟩
    · have tt := (((t1).trans t2).trans t3).trans t4
      have he : m4=ByteWrite.write ram (sp+4#32) (ReplyJson.decimal n) := HttpDecDigitsData.three ram sp n (by omega) hn
      change Quiet.Steps B img _ ⟨c,ram⟩ ⟨a4,m4⟩ at tt
      rw [he] at tt
      simpa only [duration,show ¬n<10 by omega,hsmall,ite_false] using tt
    · rw [HttpDecDigitsSpec.length n hn]
      simpa only [show ¬n<10 by omega,hsmall,ite_false] using (f4 15 (by decide) (by decide) (by decide) (by decide)).trans (v3_15)
    · intro r h5 h6 h13 h14 h15 h16 h17
      exact (f4 r h14 h16 h17 h13).trans ((f3 r h15 h16).trans ((f2 r h16 h17 h5 h14 h6).trans ((f1 r h15))))
end E5R.Thermostat.HttpDecDigits
