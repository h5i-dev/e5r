import Projects.thermostat.ChunkDecodedInvariant
namespace E5R.Thermostat.ChunkBufferSpec
open HttpRequestSpec

inductive Stop where
  | needInput
  | done
  | reject (status : Nat)
  deriving DecidableEq,Repr

structure Result where
  read : Nat
  written : Nat
  state : CState
  body : List (BitVec 8)
  stop : Stop
  deriving DecidableEq,Repr

/-- Consume only the supplied finite buffered prefix. Additional input and
    physical UART readiness are deliberately not supplied by this function. -/
def consume (wire : Nat → BitVec 8) : Nat → Nat → Nat → CState → List (BitVec 8) → Result
  | 0, read, written, s, body => ⟨read,written,s,body,.needInput⟩
  | fuel+1, read, written, s, body =>
    let (s',out) := chunkStep s (wire read).toNat 1024
    match out with
    | .nothing => consume wire fuel (read+1) written s' body
    | .data => consume wire fuel (read+1) (written+1) s' (body++[wire read])
    | .done => ⟨read+1,written,s',body,.done⟩
    | .reject status => ⟨read+1,written,s',body,.reject status⟩

theorem positions (wire : Nat → BitVec 8) (fuel read written : Nat) (s : CState) (body : List (BitVec 8)) :
    read≤(consume wire fuel read written s body).read ∧
    (consume wire fuel read written s body).read≤read+fuel ∧
    written≤(consume wire fuel read written s body).written ∧
    (consume wire fuel read written s body).written≤written+fuel := by
  induction fuel generalizing read written s body with
  | zero => simp [consume]
  | succ fuel ih =>
    simp only [consume]
    cases he : chunkStep s (wire read).toNat 1024 with
    | mk s' out =>
      cases out with
      | nothing => simpa only [he] using (by
          have h := ih (read+1) written s' body
          exact ⟨by omega,by omega,h.2.2.1,by omega⟩)
      | data => simpa only [he] using (by
          have h := ih (read+1) (written+1) s' (body++[wire read])
          exact ⟨by omega,by omega,by omega,by omega⟩)
      | done => simp <;> omega
      | reject status => simp <;> omega

theorem body_length (wire : Nat → BitVec 8) (fuel read written start : Nat) (s : CState)
    (body : List (BitVec 8)) (hlen : written=start+body.length) :
    (consume wire fuel read written s body).written=start+(consume wire fuel read written s body).body.length := by
  induction fuel generalizing read written s body with
  | zero => exact hlen
  | succ fuel ih =>
    simp only [consume]
    cases he : chunkStep s (wire read).toNat 1024 with
    | mk s' out =>
      cases out with
      | nothing => exact ih (read+1) written s' body hlen
      | data => exact ih (read+1) (written+1) s' (body++[wire read]) (by simp only [List.length_append,List.length_singleton];omega)
      | done => exact hlen
      | reject status => exact hlen

theorem decoded (wire : Nat → BitVec 8) (fuel read written : Nat) (s : CState) (body : List (BitVec 8))
    (hi : ChunkDecodedInvariant.Inv 1024 s body.length) :
    ChunkDecodedInvariant.Inv 1024 (consume wire fuel read written s body).state
      (consume wire fuel read written s body).body.length := by
  induction fuel generalizing read written s body with
  | zero => exact hi
  | succ fuel ih =>
    have step := ChunkDecodedInvariant.preserved s (wire read).toNat 1024 body.length hi (by decide)
    simp only [consume]
    cases he : chunkStep s (wire read).toNat 1024 with
    | mk s' out =>
      rw [he] at step
      cases out with
      | nothing => exact ih (read+1) written s' body (by simpa [ChunkDecodedInvariant.advance] using step)
      | data => exact ih (read+1) (written+1) s' (body++[wire read]) (by simpa [ChunkDecodedInvariant.advance] using step)
      | done => simpa [ChunkDecodedInvariant.advance] using step
      | reject status => simpa [ChunkDecodedInvariant.advance] using step

theorem decoded_length (wire : Nat → BitVec 8) (fuel read written : Nat) (s : CState) (body : List (BitVec 8))
    (hi : ChunkDecodedInvariant.Inv 1024 s body.length) :
    (consume wire fuel read written s body).body.length≤1024 :=
  ChunkDecodedInvariant.decoded_bound (decoded wire fuel read written s body hi)

theorem exhausted_read (wire : Nat → BitVec 8) (fuel read written : Nat) (s : CState) (body : List (BitVec 8))
    (he : (consume wire fuel read written s body).stop=.needInput) :
    (consume wire fuel read written s body).read=read+fuel := by
  induction fuel generalizing read written s body with
  | zero => simp [consume]
  | succ fuel ih =>
    simp only [consume] at he ⊢
    cases hs : chunkStep s (wire read).toNat 1024 with
    | mk s' out =>
      rw [hs] at he
      cases out with
      | nothing => simpa only [Nat.add_assoc,Nat.add_comm 1 fuel] using ih (read+1) written s' body he
      | data => simpa only [Nat.add_assoc,Nat.add_comm 1 fuel] using ih (read+1) (written+1) s' (body++[wire read]) he
      | done => contradiction
      | reject status => contradiction

end E5R.Thermostat.ChunkBufferSpec
