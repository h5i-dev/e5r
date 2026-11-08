import Projects.thermostat.HeadFinalResult
namespace E5R.Thermostat.MainHeaderResultKind
open E5R E5R.Thermostat HttpRequestSpec

def tag : HeadR → Word
  | .incomplete => 3#32
  | .reject _ => 4#32
  | .done h => HeadCompletedView.framingTag h.framing

def early : HeadR → Bool
  | .incomplete => true
  | .reject _ => true
  | .done _ => false

theorem words {ram dst result} (view : HeadFinalResult.At ram dst result) :
    ramRead ram dst .w=tag result ∧ ramRead ram (dst+4#32) .w=0#32 := by
  cases result with
  | incomplete => exact view
  | reject status => exact ⟨view.2.1,view.2.2.1⟩
  | done h => exact ⟨view.tag,view.padding⟩

theorem test (result : HeadR) : taken .eq (alu .and 1#32 (alu .sltu (tag result) 3#32)) 0#32=early result := by
  cases result with
  | incomplete => decide +kernel
  | reject status => change taken .eq (alu .and 1#32 (alu .sltu 4#32 3#32)) 0#32=true;decide +kernel
  | done h => cases framing : h.framing <;> change taken .eq (alu .and 1#32 (alu .sltu (HeadCompletedView.framingTag h.framing) 3#32)) 0#32=false <;> rw [framing] <;> simp only [HeadCompletedView.framingTag] <;> decide +kernel
end E5R.Thermostat.MainHeaderResultKind
