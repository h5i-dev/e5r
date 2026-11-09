import Projects.thermostat.MainHeadAcceptedBounds
import Projects.thermostat.MainQuerySpec
import Projects.thermostat.MainHeaderStreamSpec
set_option autoImplicit false
namespace E5R.Thermostat.RouteReceivedPath
open E5R E5R.Thermostat HttpRequestSpec

theorem request_slash (g : Nat → Nat) (j ms me ts te minor : Nat)
    (accepted : requestLine g 0 j=.ok ms me ts te minor) : g ts=47 := by
  unfold requestLine at accepted
  dsimp only at accepted
  split at accepted
  next bad => cases accepted
  next good =>
    split at accepted
    next bad => cases accepted
    next good =>
      try dsimp only at accepted
      split at accepted
      next bad => cases accepted
      next good =>
        split at accepted
        next bad => cases accepted
        next delimiter =>
          try dsimp only at accepted
          split at accepted
          next bad => cases accepted
          next good =>
            split at accepted
            next bad => cases accepted
            next good => cases accepted;omega

/-- Acceptance entails the origin-form slash from the independent byte
    parser. This is a fact about the original bytes, not an interior ABI input. -/
theorem accepted_slash (input : List (BitVec 8)) (maxHead maxBody : Nat) (head : Head)
    (parsed : HttpRequestBytes.parse input maxHead maxBody=.done head) :
    MainQuerySpec.bytes input head.target.1=47 := by
  let L := HttpRequestBytes.bytes input
  let cap := readLimit L.length maxHead
  let g := window L cap
  let j := lineEnd g 0 cap
  have bounds := MainHeadAcceptedBounds.accepted L maxHead maxBody head parsed
  have bound : head.target.1<cap := by have := bounds.target;omega
  have slash : g head.target.1=47 := by
    unfold HttpRequestBytes.parse parseHead at parsed
    dsimp only at parsed
    split at parsed
    next more => split at parsed <;> cases parsed
    next notMore =>
      split at parsed
      next bad => cases parsed
      next notBad =>
        cases req : requestLine g 0 j with
        | bad status => rw [req] at parsed;cases parsed
        | ok ms me ts te minor =>
          rw [req] at parsed
          dsimp only at parsed
          cases fields : HttpRequestSpec.fields g cap minor maxBody (j+2) Fields.empty with
          | more => rw [fields] at parsed;dsimp only at parsed;split at parsed <;> cases parsed
          | bad status => rw [fields] at parsed;cases parsed
          | done f len =>
            rw [fields] at parsed;dsimp only at parsed
            split at parsed
            next missing => cases parsed
            next host => cases parsed;exact request_slash g j ms me ts te minor req
  change (if head.target.1<cap then L.getD head.target.1 0 else 0)=47 at slash
  rw [ite_eq_left bound] at slash
  simp only [L,HttpRequestBytes.bytes,List.getD_eq_getElem?_getD,List.getElem?_map] at slash
  cases item : input[head.target.1]? <;> simpa [MainQuerySpec.bytes,item] using slash

/-- Query splitting preserves the initial slash and a nonempty path. -/
theorem path_slash (input : List (BitVec 8)) (start finish : Nat)
    (ordered : start<finish) (bound : finish≤input.length) (slash : MainQuerySpec.bytes input start=47) :
    ∃ ys, MainQuerySpec.path input start finish=47#8::ys := by
  have step := MainQuerySpec.step (MainQuerySpec.bytes input) start finish ordered (by rw [slash];decide)
  have later := (MainQuerySpec.bounds (MainQuerySpec.bytes input) (start+1) finish (by omega)).1
  have positive : 0<MainQuerySpec.pathLength (MainQuerySpec.bytes input) start finish := by
    unfold MainQuerySpec.pathLength;rw [step];omega
  have length : (input.drop start).length=input.length-start := by simp only [List.length_drop]
  cases dropped : input.drop start with
  | nil => rw [dropped] at length;simp only [List.length_nil] at length;omega
  | cons b bs =>
    have first : b.toNat=47 := by
      have atZero := congrArg (fun xs : List (BitVec 8) => (xs[0]?.getD 0#8).toNat) dropped
      simp only [List.getElem?_drop,Nat.add_zero,List.getElem?_cons_zero,Option.getD_some] at atZero
      exact atZero.symm.trans slash
    have byte : b=47#8 := BitVec.eq_of_toNat_eq first
    have full : MainQuerySpec.path input start finish=(b::bs).take (MainQuerySpec.pathLength (MainQuerySpec.bytes input) start finish) := by rw [MainQuerySpec.path,dropped]
    cases size : MainQuerySpec.pathLength (MainQuerySpec.bytes input) start finish with
    | zero => omega
    | succ n => refine ⟨bs.take n,?_⟩;rw [full,size,List.take_succ_cons,byte]

/-- The literal matcher domain follows directly from full pure head acceptance. -/
theorem accepted_path (input : List (BitVec 8)) (maxHead maxBody : Nat) (head : Head)
    (parsed : HttpRequestBytes.parse input maxHead maxBody=.done head) :
    ∃ ys, MainQuerySpec.path input head.target.1 head.target.2=47#8::ys := by
  have bounds := MainHeadAcceptedBounds.accepted (HttpRequestBytes.bytes input) maxHead maxBody head parsed
  have cap := (MainHeadAcceptedBounds.limit (HttpRequestBytes.bytes input).length maxHead).1
  have available : head.target.2≤input.length := by
    have target := bounds.target
    simp only [HttpRequestBytes.bytes,List.length_map] at cap target
    omega
  exact path_slash input _ _ bounds.target.2.1 available (accepted_slash input maxHead maxBody head parsed)

/-- Real one-byte receive schedules are specified by consume; its accepted
    result entails the slash domain without assuming a selected route. -/
theorem received_path (wire : Nat → BitVec 8) (fuel : Nat) (head : Head)
    (accepted : (MainHeaderStreamSpec.consume wire fuel []).result=.done head) :
    ∃ ys, MainQuerySpec.path (MainHeaderStreamSpec.consume wire fuel []).input head.target.1 head.target.2=47#8::ys := by
  have parsed := MainHeaderStreamSpec.exact_result wire fuel [] (by decide +kernel)
  rw [accepted] at parsed
  exact accepted_path _ 1024 1024 head parsed.symm
end E5R.Thermostat.RouteReceivedPath
