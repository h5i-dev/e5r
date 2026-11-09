import Projects.thermostat.RoutePathScan
import Projects.thermostat.RouteLiteralTail
import Projects.thermostat.WireSpec
set_option autoImplicit false
namespace E5R.Thermostat.RouteScanSpec
open E5R E5R.Thermostat

theorem remainder (xs : List (BitVec 8)) : xs.drop (RoutePathScan.length xs)=[] ∨ ∃ rest,xs.drop (RoutePathScan.length xs)=47#8::rest := by
  induction xs with
  | nil => exact Or.inl rfl
  | cons b bs ih =>
    by_cases slash : b=47#8
    · subst b;exact Or.inr ⟨bs,by simp [RoutePathScan.length]⟩
    · have recur : RoutePathScan.length (b::bs)=Nat.succ (RoutePathScan.length bs) := by
        rw [RoutePathScan.length,ite_eq_right slash];omega
      rw [recur,List.drop_succ_cons]
      exact ih

theorem noSlash_of_end (xs : List (BitVec 8)) (whole : RoutePathScan.length xs=xs.length) : ∀ b∈xs,b≠47#8 := by
  induction xs with
  | nil => intro b member;cases member
  | cons b bs ih =>
    by_cases slash : b=47#8
    · simp only [RoutePathScan.length,slash,ite_true,List.length_cons] at whole;omega
    · have rest : RoutePathScan.length bs=bs.length := by
        simp only [RoutePathScan.length,ite_eq_right slash,List.length_cons] at whole;omega
      intro x member
      rcases List.mem_cons.mp member with equal|tail
      · subst x;exact slash
      · exact ih rest x tail

theorem end_iff (xs : List (BitVec 8)) : RoutePathScan.length xs=xs.length ↔ ∀ b∈xs,b≠47#8 :=
  ⟨noSlash_of_end xs,RouteLiteralTail.noSlash_length xs⟩

/-- A successful relay literal segment with remaining path derives the actual
    /relay/ prefix and its suffix, rather than assuming them at an interior PC. -/
theorem relay_decompose (xs : List (BitVec 8))
    (equal : WireSpec.ascii "relay"=xs.take (RoutePathScan.length xs)) (more : RoutePathScan.length xs<xs.length) :
    ∃ rest,47#8::xs=WireSpec.ascii "/relay/"++rest ∧ xs.drop 6=rest := by
  rcases remainder xs with ended|⟨rest,stopped⟩
  · have size := congrArg List.length ended
    simp only [List.length_drop,List.length_nil] at size
    omega
  · have whole : xs=WireSpec.ascii "relay"++47#8::rest := by
      calc
        xs=xs.take (RoutePathScan.length xs)++xs.drop (RoutePathScan.length xs) := (List.take_append_drop _ _).symm
        _ =WireSpec.ascii "relay"++47#8::rest := by rw [←equal,stopped]
    refine ⟨rest,?_,?_⟩
    · rw [whole];rfl
    · rw [whole];rfl

/-- Prefix acceptance entails both real scan-segment equality and a following
    delimiter; /relay without its final slash fails the second condition. -/
theorem relay_known (xs : List (BitVec 8)) (accepted : (47#8::xs).take 7=WireSpec.ascii "/relay/") :
    WireSpec.ascii "relay"=xs.take (RoutePathScan.length xs) ∧ RoutePathScan.length xs<xs.length := by
  let rest := (47#8::xs).drop 7
  have whole : 47#8::xs=WireSpec.ascii "/relay/"++rest := by
    calc
      47#8::xs=(47#8::xs).take 7++(47#8::xs).drop 7 := (List.take_append_drop _ _).symm
      _ =WireSpec.ascii "/relay/"++rest := by rw [accepted]
  have tail : xs=WireSpec.ascii "relay/"++rest := by
    change 47#8::xs=47#8::(WireSpec.ascii "relay/"++rest) at whole
    exact (List.cons.inj whole).2
  rw [tail]
  have scanned : RoutePathScan.length (WireSpec.ascii "relay/"++rest)=5 := rfl
  rw [scanned]
  refine ⟨rfl,?_⟩
  rw [List.length_append]
  change 5<6+rest.length
  omega
end E5R.Thermostat.RouteScanSpec
