import Projects.thermostat.HttpRequestBytes
namespace E5R.Thermostat.MainHeaderIncompleteBound
open E5R E5R.Thermostat HttpRequestSpec

theorem bound (input : List (BitVec 8)) (incomplete : HttpRequestBytes.parse input 1024 1024=.incomplete) : input.length<1024 := by
  by_cases full : 1024≤input.length
  · unfold HttpRequestBytes.parse parseHead at incomplete
    dsimp only at incomplete
    have length : (HttpRequestBytes.bytes input).length=input.length := by simp only [HttpRequestBytes.bytes,List.length_map]
    rw [length] at incomplete
    simp only [full,decide_true,ite_true] at incomplete
    split at incomplete
    next more => cases incomplete
    next notMore =>
      split at incomplete
      next bad => cases incomplete
      next notBad =>
        cases request : requestLine (window (HttpRequestBytes.bytes input) (readLimit input.length 1024)) 0
          (lineEnd (window (HttpRequestBytes.bytes input) (readLimit input.length 1024)) 0 (readLimit input.length 1024)) with
        | bad status => rw [request] at incomplete;cases incomplete
        | ok ms me ts te minor =>
          rw [request] at incomplete
          dsimp only at incomplete
          cases parsed : fields (window (HttpRequestBytes.bytes input) (readLimit input.length 1024)) (readLimit input.length 1024) minor 1024
            ((lineEnd (window (HttpRequestBytes.bytes input) (readLimit input.length 1024)) 0 (readLimit input.length 1024))+2) Fields.empty with
          | more => rw [parsed] at incomplete;cases incomplete
          | bad status => rw [parsed] at incomplete;cases incomplete
          | done f len =>
            rw [parsed] at incomplete
            dsimp only at incomplete
            split at incomplete <;> cases incomplete
  · omega
end E5R.Thermostat.MainHeaderIncompleteBound
