import Projects.thermostat.RuntimeSecondMatch
import Projects.thermostat.RuntimeThirdMatch
import Projects.thermostat.RuntimeFourthMatch
import Projects.thermostat.RuntimeFifthCandidate
import Projects.thermostat.RouteSpec
set_option autoImplicit false
namespace E5R.Thermostat.RuntimeRelayEntry
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board

def known (path : List (BitVec 8)) : Prop := path=WireSpec.ascii "/state" ∨ path=WireSpec.ascii "/setpoint" ∨ path=WireSpec.ascii "/temp" ∨ path=WireSpec.ascii "/mode"
instance (path : List (BitVec 8)) : Decidable (known path) := by unfold known;infer_instance

/-- All four actual literal candidates, including real method guards and
    per-candidate future stores, lead to the actual final relay matcher when
    no literal route accepts the pure path/method. The404/405 flag is exact. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {lowValue : Word} {close : Bool} {used : Word}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close)
    (pc : c.pc=0x800013d2#32)
    (result : c.get 10=(if RuntimeRequestSpans.path input head=WireSpec.ascii "/state" then 1#32 else 0#32))
    (denied : ∀ kind : RouteLiteralInfo.Kind, RuntimeRequestSpans.path input head=RouteLiteralInfo.text kind →
      RouteSpec.allows (RouteLiteralInfo.route kind) (MainMethodSpec.decode (MainMethodBytes.token input head.method.2))=false)
    (leading : ∃ ys,RuntimeRequestSpans.path input head=47#8::ys) (metadata : LoopTransactionMemory.At ram used) :
    ∃ n d after, n≤30*(RuntimeRequestSpans.path input head).length+695 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      RuntimeLiteralInput.At d after input s head amount rawUsed served lowValue close 0x80005b9c#32 10#32 0x80001856#32 ∧
      d.get 9=(if known (RuntimeRequestSpans.path input head) then 2#32 else 3#32) ∧ LoopTransactionMemory.At after used ∧ d.sameCsr c := by
  have state : RuntimeRequestSpans.path input head≠WireSpec.ascii "/state" ∨
      (MainMethodSpec.decode (MainMethodBytes.token input head.method.2)≠.get ∧ MainMethodSpec.decode (MainMethodBytes.token input head.method.2)≠.head) := by
    by_cases selected : RuntimeRequestSpans.path input head=WireSpec.ascii "/state"
    · right
      have bad := denied .state selected
      constructor
      · intro method;rw [method] at bad;change true=false at bad;cases bad
      · intro method;rw [method] at bad;change true=false at bad;cases bad
    · exact Or.inl selected
  have setpoint : RuntimeRequestSpans.path input head≠WireSpec.ascii "/setpoint" ∨ MainMethodSpec.decode (MainMethodBytes.token input head.method.2)≠.put := by
    by_cases selected : RuntimeRequestSpans.path input head=WireSpec.ascii "/setpoint"
    · right
      have bad := denied .setpoint selected
      intro method;rw [method] at bad;change true=false at bad;cases bad
    · exact Or.inl selected
  have temp : RuntimeRequestSpans.path input head≠WireSpec.ascii "/temp" ∨ MainMethodSpec.decode (MainMethodBytes.token input head.method.2)≠.post := by
    by_cases selected : RuntimeRequestSpans.path input head=WireSpec.ascii "/temp"
    · right
      have bad := denied .temp selected
      intro method;rw [method] at bad;change true=false at bad;cases bad
    · exact Or.inl selected
  have mode : RuntimeRequestSpans.path input head≠WireSpec.ascii "/mode" ∨ MainMethodSpec.decode (MainMethodBytes.token input head.method.2)≠.put := by
    by_cases selected : RuntimeRequestSpans.path input head=WireSpec.ascii "/mode"
    · right
      have bad := denied .mode selected
      intro method;rw [method] at bad;change true=false at bad;cases bad
    · exact Or.inl selected
  obtain ⟨na,a,ra,ba,ta,pa,a10,a11,a9,liveA,metaA,ac⟩ := RuntimeSecondMatch.contract h pc result state leading metadata
  obtain ⟨nb,b,rb,bb,tb,pb,b10,b11,b9,liveB,metaB,bc⟩ := RuntimeThirdMatch.contract liveA pa a10 setpoint leading metaA
  obtain ⟨nc,e,re,be,te,pe,e10,e11,e9,liveE,metaE,ec⟩ := RuntimeFourthMatch.contract liveB pb b10 temp leading metaB
  obtain ⟨nd,d,bd,td,entry,d9,dc,frame⟩ := RuntimeFifthCandidate.advance liveE pe e10 mode
  have metaD := LoopTransactionMemory.caller metaE frame
  refine ⟨na+nb+nc+nd,d,_,by omega,((ta.trans tb).trans te).trans td,entry,?_,metaD,dc.trans (ec.trans (bc.trans ac))⟩
  rw [d9,e9,b9,a9]
  by_cases p0 : RuntimeRequestSpans.path input head=WireSpec.ascii "/state" <;>
    by_cases p1 : RuntimeRequestSpans.path input head=WireSpec.ascii "/setpoint" <;>
    by_cases p2 : RuntimeRequestSpans.path input head=WireSpec.ascii "/temp" <;>
    by_cases p3 : RuntimeRequestSpans.path input head=WireSpec.ascii "/mode" <;>
    simp only [known,p0,p1,p2,p3,ite_true,ite_false,ite_self,true_or,or_true,false_or,or_false]
end E5R.Thermostat.RuntimeRelayEntry
