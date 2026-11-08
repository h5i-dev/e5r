import Projects.thermostat.ChunkBufferSpec
namespace E5R.Thermostat.ChunkBufferConcat
open E5R.Thermostat HttpRequestSpec ChunkBufferSpec

/-- Splitting a buffered byte stream does not change the consumer. Terminal
    outcomes are absorbing; only needInput consumes the following prefix. -/
theorem consume_add (wire : Nat → BitVec 8) (a b read written : Nat) (s : CState)
    (body : List (BitVec 8)) :
    consume wire (a+b) read written s body=
      let r := consume wire a read written s body
      if r.stop=.needInput then consume wire b r.read r.written r.state r.body else r := by
  induction a generalizing read written s body with
  | zero => simp only [Nat.zero_add,consume,ite_true]
  | succ a ih =>
    rw [show a+1+b=(a+b)+1 by omega]
    cases hs : chunkStep s (wire read).toNat 1024 with
    | mk s' out =>
      cases out with
      | nothing => simpa only [consume,hs] using ih (read+1) written s' body
      | data => simpa only [consume,hs] using ih (read+1) (written+1) s' (body++[wire read])
      | done => simp only [consume,hs,reduceCtorEq,ite_false]
      | reject status => simp only [consume,hs,reduceCtorEq,ite_false]

end E5R.Thermostat.ChunkBufferConcat
