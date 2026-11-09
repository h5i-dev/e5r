import Projects.thermostat.MainRelayMatch
import Projects.thermostat.RuntimeLiteralInput
import Projects.thermostat.RuntimeRouteEnvelope
set_option autoImplicit false
namespace E5R.Thermostat.RuntimeRelayCaptured
open E5R E5R.Thermostat HttpRequestSpec
abbrev params : Word := 0x80fff9d0#32
def path (param : List (BitVec 8)) := WireSpec.ascii "/relay/"++param
def size (param : List (BitVec 8)) : Word := BitVec.ofNat 32 (7+param.length)
def memory (before : Word → BitVec 8) (origin : Core) (param : List (BitVec 8)) :=
  MainRelayCapture.memory (MainPathStateSave.memory before origin) params (size param)

/-- The old full Request view is retained only for its pre-capture RAM. The
    real post-capture RAM has a derived pair and no zero-parameter assertion. -/
structure At (origin : Core) (before : Word → BitVec 8) (c : Core) (ram : Word → BitVec 8)
    (input : List (BitVec 8)) (s : Spec.Snapshot) (head : Head) (amount rawUsed served : Nat) (lowValue : Word) (close : Bool)
    (param : List (BitVec 8)) : Prop where
  live : RuntimeRouteEnvelope.At origin before input s head amount rawUsed served lowValue close
  route : MainRequestSpans.path input head=path param
  nonempty : param≠[]
  noSlash : ∀ b∈param, b≠47#8
  memory : ram=RuntimeRelayCaptured.memory before origin param
  pc : c.pc=0x80001856#32
  matched : c.get 10=1#32
  captures : c.get 11=1#32
  regs : ∀ r : Reg, r∈[2,8,18,19,22,23,24,26] → c.get r=origin.get r
  future : c.get 24=0x80fffa2c#32
  csr : c.sameCsr origin

theorem frame {origin before c ram input s head amount rawUsed served lowValue close param}
    (h : At origin before c ram input s head amount rawUsed served lowValue close param) (obj : Word) (length : Nat)
    (saved : WordRegions.Disjoint obj length 0x80ffeb30#32 96)
    (pair : WordRegions.Disjoint obj length params 8) : ViewFrame.Region before ram obj length := by
  intro i
  rw [h.memory,RuntimeRelayCaptured.memory,MainRelayCapture.frame _ _ _ _ (pair i),MainPathStateSave.memory_eq]
  exact OuterSave.frame before 0x80ffeb30#32 origin _ (saved i)

theorem first_word {origin before c ram input s head amount rawUsed served lowValue close param}
    (h : At origin before c ram input s head amount rawUsed served lowValue close param) : ramRead ram params .w=7#32 := by
  rw [h.memory];exact MainRelayCapture.first_word _ _ _

theorem second_word {origin before c ram input s head amount rawUsed served lowValue close param}
    (h : At origin before c ram input s head amount rawUsed served lowValue close param) : ramRead ram (params+4#32) .w=size param := by
  rw [h.memory];exact MainRelayCapture.second_word _ _ _

theorem path_view {c ram input s head amount rawUsed served lowValue close}
    (h : RuntimeRouteEnvelope.At c ram input s head amount rawUsed served lowValue close) (param : List (BitVec 8))
    (route : MainRequestSpans.path input head=path param) (nonempty : param≠[]) :
    Bytes.Span RuntimeRouteEnvelope.B ram (RuntimeRouteEnvelope.rx+BitVec.ofNat 32 head.target.1) (path param) ∧
      MainRequestBuild.pathLength input head=size param ∧ 8≤(size param).toNat ∧
      WordRegions.Disjoint (RuntimeRouteEnvelope.rx+BitVec.ofNat 32 head.target.1) (path param).length 0x80ffeb30#32 96 := by
  obtain ⟨span,length,separate⟩ := RuntimeLiteralInput.literal_view h (path param) route
  have count : (path param).length=7+param.length := by unfold path;rw [List.length_append];rfl
  have bound : 7+param.length<2^32 := by rw [←count];exact span.length
  refine ⟨span,?_,?_,separate⟩
  · change BitVec.ofNat 32 (MainQuerySpec.pathLength (MainQuerySpec.bytes input) head.target.1 head.target.2)=size param
    rw [length,count];rfl
  · unfold size
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound]
    have positive := List.length_pos_iff.mpr nonempty
    omega
end E5R.Thermostat.RuntimeRelayCaptured
