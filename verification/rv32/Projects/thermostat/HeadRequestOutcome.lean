import Projects.thermostat.HeadLineReady
import Projects.thermostat.HeadSaved
namespace E5R.Thermostat.HeadRequestOutcome
open E5R E5R.Thermostat HttpRequestSpec

/-- An actual full-parser rejection return or the concrete header-parser
    entry for a successfully decoded request line. Neither asserts HeadR.done. -/
def At (c : Core) (ram : Word → BitVec 8) (sp : Word) (values : Reg → Word) (j length cap : Nat) : ReqLine → Prop
  | .bad status => c.pc=values 1 &&& ~~~1 ∧ c.get 2=sp+384#32 ∧ HeadSaved.CoreAt c values ∧
      HeadResultView.At ram (sp+4904#32) (.reject status)
  | .ok ms me ts te minor => ms=0 ∧ ts=me+1 ∧ HeadLineReady.At c ram sp me te j minor length cap
end E5R.Thermostat.HeadRequestOutcome
