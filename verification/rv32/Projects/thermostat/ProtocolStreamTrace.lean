import Projects.thermostat.ProtocolStreamSpec
set_option autoImplicit false
namespace E5R.Thermostat.ProtocolStreamSpec.Run
open E5R.Thermostat.ProtocolStreamSpec

theorem trans {a b c first last} (h : Run a first b) (finish : Run b last c) : Run a (first++last) c := by
  induction finish with
  | refl => simpa only [List.append_nil] using h
  | step path step ih => simpa only [List.append_assoc] using Run.step ih step
end E5R.Thermostat.ProtocolStreamSpec.Run

namespace E5R.Thermostat.ProtocolStreamTrace
open E5R E5R.Thermostat ProtocolStreamSpec

def input (actions : List Action) : List (BitVec 8) := actions.filterMap fun a => match a with
  | .rx byte => some byte | .tx _ => none

def output (actions : List Action) : List (BitVec 8) := actions.filterMap fun a => match a with
  | .tx byte => some byte | .rx _ => none

/-- Separate UART projections retain an actual interleaved pure execution.
    They never replace that execution with all RX followed by all TX. -/
def Trace (a : State) (rx tx : List (BitVec 8)) (b : State) : Prop :=
  ∃ actions,Run a actions b ∧ input actions=rx ∧ output actions=tx

theorem refl (m : State) : Trace m [] [] m := ⟨[],.refl _,rfl,rfl⟩

theorem trans {a b c rx₀ tx₀ rx₁ tx₁} (h : Trace a rx₀ tx₀ b) (finish : Trace b rx₁ tx₁ c) :
    Trace a (rx₀++rx₁) (tx₀++tx₁) c := by
  obtain ⟨first,path,firstRx,firstTx⟩ := h
  obtain ⟨last,rest,lastRx,lastTx⟩ := finish
  exact ⟨first++last,path.trans rest,by simp only [input,List.filterMap_append];change input first++input last=rx₀++rx₁;rw [firstRx,lastRx],
    by simp only [output,List.filterMap_append];change output first++output last=tx₀++tx₁;rw [firstTx,lastTx]⟩

theorem single {a b label} (h : ProtocolStreamSpec.Step a label b) :
    Trace a (input label.toList) (output label.toList) b :=
  ⟨label.toList,by simpa only [List.nil_append] using Run.step (.refl a) h,rfl,rfl⟩

theorem receive {a b byte} (h : ProtocolStreamSpec.receive a byte=some b) : Trace a [byte] [] b :=
  single (.receive h)

theorem transmit {m p byte rest} (phase : m.phase=.reply p) (bytes : p.remaining=byte::rest) :
    Trace m [] [byte] {m with phase := .reply {p with remaining := rest}} := single (.transmit phase bytes)

theorem complete {m p} (phase : m.phase=.reply p) (bytes : p.remaining=[]) :
    Trace m [] [] ⟨p.response.state,p.nextCount,.head []⟩ := single (.complete phase bytes)
end E5R.Thermostat.ProtocolStreamTrace
