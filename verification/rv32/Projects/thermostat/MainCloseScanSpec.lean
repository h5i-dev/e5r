import Projects.thermostat.MainCloseSpec
import Projects.thermostat.ByteSlices
set_option autoImplicit false
namespace E5R.Thermostat.MainCloseScanSpec
open E5R E5R.Thermostat

/-- Independent first-comma partition. `some []` records a trailing comma,
    unlike `none`, which records exhausting the value without a comma. -/
def scan : List (BitVec 8) → List (BitVec 8) × Option (List (BitVec 8))
  | [] => ([],none)
  | b::bs => if b=44#8 then ([],some bs) else (b::(scan bs).1,(scan bs).2)
def token (xs : List (BitVec 8)) := (scan xs).1
def rest (xs : List (BitVec 8)) := (scan xs).2

theorem hit (bs : List (BitVec 8)) : token (44#8::bs)=[] ∧ rest (44#8::bs)=some bs := by simp [token,rest,scan]
theorem miss (b : BitVec 8) (bs : List (BitVec 8)) (other : b≠44#8) : token (b::bs)=b::token bs ∧ rest (b::bs)=rest bs := by simp [token,rest,scan,other]

theorem decomposition (xs : List (BitVec 8)) : xs=token xs++(match rest xs with | none => [] | some ys => 44#8::ys) := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    by_cases comma : b=44#8
    · subst b
      simp only [(hit bs).1,(hit bs).2,List.nil_append]
    · rw [(miss b bs comma).1,(miss b bs comma).2]
      exact congrArg (List.cons b) ih

theorem no_comma (xs : List (BitVec 8)) : 44#8∉token xs := by
  induction xs with
  | nil => simp [token,scan]
  | cons b bs ih =>
    by_cases comma : b=44#8
    · subst b
      rw [(hit bs).1]
      simp
    · rw [(miss b bs comma).1]
      simp only [List.mem_cons,not_or]
      exact ⟨Ne.symm comma,ih⟩

theorem bounded (xs : List (BitVec 8)) : (token xs).length≤xs.length := by
  have sizes := congrArg List.length (decomposition xs)
  rw [List.length_append] at sizes
  omega

theorem absent (xs : List (BitVec 8)) (noneFound : rest xs=none) : token xs=xs := by
  have same := decomposition xs
  simpa only [noneFound,List.append_nil] using same.symm

theorem remaining (xs ys : List (BitVec 8)) (found : rest xs=some ys) :
    (token xs).length+1+ys.length=xs.length := by
  have sizes := congrArg List.length (decomposition xs)
  simp only [found,List.length_append,List.length_cons] at sizes
  omega

theorem splitOn (xs : List (BitVec 8)) : xs.splitOn 44#8=match rest xs with
    | none => [token xs]
    | some ys => token xs::ys.splitOn 44#8 := by
  cases found : rest xs with
  | none =>
    calc
      xs.splitOn 44#8=(token xs).splitOn 44#8 := congrArg (fun ys : List (BitVec 8) => ys.splitOn 44#8) (absent xs found).symm
      _ = [token xs] := List.splitOn_eq_singleton (no_comma xs)
  | some ys =>
    have same : xs=token xs++44#8::ys := by simpa only [found] using decomposition xs
    calc
      xs.splitOn 44#8=(token xs++44#8::ys).splitOn 44#8 := congrArg (fun zs : List (BitVec 8) => zs.splitOn 44#8) same
      _ = token xs::ys.splitOn 44#8 := List.splitOn_append_cons_self_of_not_mem (no_comma xs) ys

theorem hasClose (xs : List (BitVec 8)) : MainCloseSpec.hasClose xs=
    (HeaderSpec.same (TrimMath.trim (token xs)) (WireSpec.ascii "close") ||
      match rest xs with | none => false | some ys => MainCloseSpec.hasClose ys) := by
  unfold MainCloseSpec.hasClose
  rw [splitOn]
  cases rest xs <;> simp only [List.any_cons,List.any_nil,Bool.or_false]

theorem token_span {B ram p xs} (span : Bytes.Span B ram p xs) : Bytes.Span B ram p (token xs) := by
  rw [decomposition xs] at span
  exact Bytes.left_part span

theorem rest_span {B ram p xs ys} (span : Bytes.Span B ram p xs) (found : rest xs=some ys) :
    Bytes.Span B ram (p+BitVec.ofNat 32 ((token xs).length+1)) ys := by
  have same : xs=token xs++44#8::ys := by simpa only [found] using decomposition xs
  rw [same] at span
  have tail := Bytes.tail (Bytes.suffix span)
  simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using tail
end E5R.Thermostat.MainCloseScanSpec
