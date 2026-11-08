import Projects.thermostat.ResponseHeadFieldEmpty
import Projects.thermostat.ResponseHeadFieldEnter
import Projects.thermostat.ResponseFieldLoop
import Projects.thermostat.ResponseHeadCTNoneClose
import Projects.thermostat.ResponseHeadCTNoneKeep
import Projects.thermostat.ResponseHeadCTSomeClose
import Projects.thermostat.ResponseHeadCTSomeKeep
import Projects.thermostat.ResponseHeadSources
namespace E5R.Thermostat.ResponseHeadField
open E5R E5R.Thermostat

def Frame (c d : Core) := ∀ r : Reg, r≠9 → r≠6 → r≠18 → r≠21 → r≠7 → r≠28 → r≠29 → r≠30 → r≠17 → r≠31 → r≠20 → r≠24 → r≠8 → d.get r=c.get r

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (ptr : Word) (ct : List (BitVec 8)) (close : Bool)
    (hlen : ct.length≤16) (h13 : c.get 13=ptr) (h14 : c.get 14=BitVec.ofNat 32 ct.length)
    (h16 : c.get 16=ResponseHeadBodyMath.boolWord close) (hs : ReadBytes.Span B img ram ptr ct) (hf : ResponseHeadSpec.Field ct)
    (hp : c.pc=0x80003e82#32) :
    ∃ d n, n≤130 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80003ee2#32 ∧
      d.get 9=1#32 ∧ d.get 8=ResponseHeadSources.connection close ∧
      d.get 18=ResponseHeadSources.ctEnd ct ∧ d.get 21=ResponseHeadSources.ctName ct ∧
      d.get 20=BitVec.ofNat 32 (ResponseHeadPlan.ctEnd ct).length ∧
      d.get 24=BitVec.ofNat 32 (ResponseHeadPlan.ctName ct).length ∧ Frame c d ∧ d.sameCsr c := by
  by_cases ht : ct=[]
  · obtain ⟨a,ta,pa,a9,fa,ka⟩ := ResponseHeadFieldEmpty.contract B c ram (by simpa only [ht,List.length_nil] using h14) hp
    have a16 := (fa 16 (by decide)).trans h16
    cases close with
    | false =>
      obtain ⟨d,td,pd,d24,d20,d21,d18,d8,fd,kd⟩ := ResponseHeadCTNoneKeep.contract B a ram (by simpa [ResponseHeadBodyMath.boolWord] using a16) pa
      refine ⟨d,2+7,by decide,ta.trans td,pd,?_,?_,?_,?_,?_,?_,?_,kd.trans ka⟩
      · exact (fd 9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (a9)
      · simpa [ResponseHeadLiterals.pointer,WireSpec.ascii,ResponseHeadSources.connection,ResponseHeadSources.ctEnd,ResponseHeadSources.ctName,ResponseHeadPlan.ctEnd,ResponseHeadPlan.ctName,ht,ite_true,ite_false] using d8
      · simpa [ResponseHeadLiterals.pointer,WireSpec.ascii,ResponseHeadSources.connection,ResponseHeadSources.ctEnd,ResponseHeadSources.ctName,ResponseHeadPlan.ctEnd,ResponseHeadPlan.ctName,ht,ite_true,ite_false] using d18
      · simpa [ResponseHeadLiterals.pointer,WireSpec.ascii,ResponseHeadSources.connection,ResponseHeadSources.ctEnd,ResponseHeadSources.ctName,ResponseHeadPlan.ctEnd,ResponseHeadPlan.ctName,ht,ite_true,ite_false] using d21
      · simpa [ResponseHeadLiterals.pointer,WireSpec.ascii,ResponseHeadSources.connection,ResponseHeadSources.ctEnd,ResponseHeadSources.ctName,ResponseHeadPlan.ctEnd,ResponseHeadPlan.ctName,ht,ite_true,ite_false] using d20
      · simpa [ResponseHeadLiterals.pointer,WireSpec.ascii,ResponseHeadSources.connection,ResponseHeadSources.ctEnd,ResponseHeadSources.ctName,ResponseHeadPlan.ctEnd,ResponseHeadPlan.ctName,ht,ite_true,ite_false] using d24
      · intro r h9 h6 h18 h21 h7 h28 h29 h30 h17 h31 h20 h24 h8
        exact (fd r h24 h20 h21 h18 h8).trans (fa r h9)
    | true =>
      obtain ⟨d,td,pd,d24,d20,d21,d18,d8,fd,kd⟩ := ResponseHeadCTNoneClose.contract B a ram (by simpa [ResponseHeadBodyMath.boolWord] using a16) pa
      refine ⟨d,2+7,by decide,ta.trans td,pd,?_,?_,?_,?_,?_,?_,?_,kd.trans ka⟩
      · exact (fd 9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (a9)
      · simpa [ResponseHeadLiterals.pointer,WireSpec.ascii,ResponseHeadSources.connection,ResponseHeadSources.ctEnd,ResponseHeadSources.ctName,ResponseHeadPlan.ctEnd,ResponseHeadPlan.ctName,ht,ite_true,ite_false] using d8
      · simpa [ResponseHeadLiterals.pointer,WireSpec.ascii,ResponseHeadSources.connection,ResponseHeadSources.ctEnd,ResponseHeadSources.ctName,ResponseHeadPlan.ctEnd,ResponseHeadPlan.ctName,ht,ite_true,ite_false] using d18
      · simpa [ResponseHeadLiterals.pointer,WireSpec.ascii,ResponseHeadSources.connection,ResponseHeadSources.ctEnd,ResponseHeadSources.ctName,ResponseHeadPlan.ctEnd,ResponseHeadPlan.ctName,ht,ite_true,ite_false] using d21
      · simpa [ResponseHeadLiterals.pointer,WireSpec.ascii,ResponseHeadSources.connection,ResponseHeadSources.ctEnd,ResponseHeadSources.ctName,ResponseHeadPlan.ctEnd,ResponseHeadPlan.ctName,ht,ite_true,ite_false] using d20
      · simpa [ResponseHeadLiterals.pointer,WireSpec.ascii,ResponseHeadSources.connection,ResponseHeadSources.ctEnd,ResponseHeadSources.ctName,ResponseHeadPlan.ctEnd,ResponseHeadPlan.ctName,ht,ite_true,ite_false] using d24
      · intro r h9 h6 h18 h21 h7 h28 h29 h30 h17 h31 h20 h24 h8
        exact (fd r h24 h20 h21 h18 h8).trans (fa r h9)
  · obtain ⟨a,ta,pa,a9,a6,a18,a21,a7,a28,a29,a30,a17,fa,ka⟩ := ResponseHeadFieldEnter.contract B c ram ptr ct.length (List.length_pos_iff.mpr ht) hlen h13 h14 hp
    obtain ⟨b,n,bn,tb,pb,b29,b30,fb,kb⟩ := ResponseFieldLoop.contract B a ram ptr ct ht hlen pa a29 a30 a6 a7 a28 hs hf
    have b16 := (fb 16 (by decide) (by decide) (by decide)).trans ((fa 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h16)
    cases close with
    | false =>
      obtain ⟨d,td,pd,d20,d24,d8,fd,kd⟩ := ResponseHeadCTSomeKeep.contract B b ram (by simpa [ResponseHeadBodyMath.boolWord] using b16) pb
      refine ⟨d,13+n+5,by omega,(ta.trans tb).trans td,pd,?_,?_,?_,?_,?_,?_,?_,kd.trans (kb.trans ka)⟩
      · exact (fd 9 (by decide) (by decide) (by decide)).trans ((fb 9 (by decide) (by decide) (by decide)).trans (a9))
      · simpa [ResponseHeadLiterals.pointer,WireSpec.ascii,ResponseHeadSources.connection,ResponseHeadSources.ctEnd,ResponseHeadSources.ctName,ResponseHeadPlan.ctEnd,ResponseHeadPlan.ctName,ht,ite_true,ite_false] using d8
      · simpa [ResponseHeadLiterals.pointer,WireSpec.ascii,ResponseHeadSources.connection,ResponseHeadSources.ctEnd,ResponseHeadSources.ctName,ResponseHeadPlan.ctEnd,ResponseHeadPlan.ctName,ht,ite_true,ite_false] using (fd 18 (by decide) (by decide) (by decide)).trans ((fb 18 (by decide) (by decide) (by decide)).trans (a18))
      · simpa [ResponseHeadLiterals.pointer,WireSpec.ascii,ResponseHeadSources.connection,ResponseHeadSources.ctEnd,ResponseHeadSources.ctName,ResponseHeadPlan.ctEnd,ResponseHeadPlan.ctName,ht,ite_true,ite_false] using (fd 21 (by decide) (by decide) (by decide)).trans ((fb 21 (by decide) (by decide) (by decide)).trans (a21))
      · simpa [ResponseHeadLiterals.pointer,WireSpec.ascii,ResponseHeadSources.connection,ResponseHeadSources.ctEnd,ResponseHeadSources.ctName,ResponseHeadPlan.ctEnd,ResponseHeadPlan.ctName,ht,ite_true,ite_false] using d20
      · simpa [ResponseHeadLiterals.pointer,WireSpec.ascii,ResponseHeadSources.connection,ResponseHeadSources.ctEnd,ResponseHeadSources.ctName,ResponseHeadPlan.ctEnd,ResponseHeadPlan.ctName,ht,ite_true,ite_false] using d24
      · intro r h9 h6 h18 h21 h7 h28 h29 h30 h17 h31 h20 h24 h8
        exact (fd r h20 h24 h8).trans ((fb r h29 h30 h31).trans (fa r h9 h6 h18 h21 h7 h28 h29 h30 h17))
    | true =>
      obtain ⟨d,td,pd,d20,d24,d8,fd,kd⟩ := ResponseHeadCTSomeClose.contract B b ram (by simpa [ResponseHeadBodyMath.boolWord] using b16) pb
      refine ⟨d,13+n+5,by omega,(ta.trans tb).trans td,pd,?_,?_,?_,?_,?_,?_,?_,kd.trans (kb.trans ka)⟩
      · exact (fd 9 (by decide) (by decide) (by decide)).trans ((fb 9 (by decide) (by decide) (by decide)).trans (a9))
      · simpa [ResponseHeadLiterals.pointer,WireSpec.ascii,ResponseHeadSources.connection,ResponseHeadSources.ctEnd,ResponseHeadSources.ctName,ResponseHeadPlan.ctEnd,ResponseHeadPlan.ctName,ht,ite_true,ite_false] using d8
      · simpa [ResponseHeadLiterals.pointer,WireSpec.ascii,ResponseHeadSources.connection,ResponseHeadSources.ctEnd,ResponseHeadSources.ctName,ResponseHeadPlan.ctEnd,ResponseHeadPlan.ctName,ht,ite_true,ite_false] using (fd 18 (by decide) (by decide) (by decide)).trans ((fb 18 (by decide) (by decide) (by decide)).trans (a18))
      · simpa [ResponseHeadLiterals.pointer,WireSpec.ascii,ResponseHeadSources.connection,ResponseHeadSources.ctEnd,ResponseHeadSources.ctName,ResponseHeadPlan.ctEnd,ResponseHeadPlan.ctName,ht,ite_true,ite_false] using (fd 21 (by decide) (by decide) (by decide)).trans ((fb 21 (by decide) (by decide) (by decide)).trans (a21))
      · simpa [ResponseHeadLiterals.pointer,WireSpec.ascii,ResponseHeadSources.connection,ResponseHeadSources.ctEnd,ResponseHeadSources.ctName,ResponseHeadPlan.ctEnd,ResponseHeadPlan.ctName,ht,ite_true,ite_false] using d20
      · simpa [ResponseHeadLiterals.pointer,WireSpec.ascii,ResponseHeadSources.connection,ResponseHeadSources.ctEnd,ResponseHeadSources.ctName,ResponseHeadPlan.ctEnd,ResponseHeadPlan.ctName,ht,ite_true,ite_false] using d24
      · intro r h9 h6 h18 h21 h7 h28 h29 h30 h17 h31 h20 h24 h8
        exact (fd r h20 h24 h8).trans ((fb r h29 h30 h31).trans (fa r h9 h6 h18 h21 h7 h28 h29 h30 h17))
end E5R.Thermostat.ResponseHeadField
