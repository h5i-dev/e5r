import Projects.thermostat.WireSpec
namespace E5R.Thermostat.HeaderSpec
open E5R E5R.Thermostat

/-- Independent ASCII folding for the Request header-name comparison. -/
def lower (b : BitVec 8) : BitVec 8 :=
  if 65 ≤ b.toNat ∧ b.toNat ≤ 90 then BitVec.ofNat 8 (b.toNat+32) else b

def same (xs ys : List (BitVec 8)) : Bool := decide (xs.map lower = ys.map lower)

structure Entry where
  nameStart : Nat
  nameEnd : Nat
  valueStart : Nat
  valueEnd : Nat
  deriving Repr,DecidableEq

def name (raw : List (BitVec 8)) (e : Entry) := (raw.drop e.nameStart).take (e.nameEnd-e.nameStart)
def value (raw : List (BitVec 8)) (e : Entry) := (raw.drop e.valueStart).take (e.valueEnd-e.valueStart)

def Bounds (rawLength : Nat) (e : Entry) : Prop :=
  e.nameStart ≤ e.nameEnd ∧ e.nameEnd ≤ rawLength ∧ e.valueStart ≤ e.valueEnd ∧ e.valueEnd ≤ rawLength

/-- Lookup returns the first matching field in original order, including the
    empty value; later duplicate headers do not override an earlier match. -/
def lookup (raw : List (BitVec 8)) (query : List (BitVec 8)) : List Entry → Option (List (BitVec 8))
  | [] => none
  | e::es => if same (name raw e) query then some (value raw e) else lookup raw query es

theorem authorization_case : same (WireSpec.ascii "AuThOrIzAtIoN") (WireSpec.ascii "authorization") = true := by decide +kernel
theorem non_ascii_exact : lower 192#8 = 192#8 := by decide +kernel
theorem punctuation_exact : lower 64#8 = 64#8 ∧ lower 91#8 = 91#8 := by decide +kernel

def find (raw query : List (BitVec 8)) : List Entry → Option Entry
  | [] => none
  | e::es => if same (name raw e) query then some e else find raw query es

theorem lookup_find (raw query : List (BitVec 8)) (entries : List Entry) :
    lookup raw query entries = (find raw query entries).map (value raw) := by
  induction entries with
  | nil => rfl
  | cons e es ih =>
    cases he : same (name raw e) query <;> simp only [lookup,find,he,Bool.false_eq_true,ite_false,ite_true,ih,Option.map_some]
end E5R.Thermostat.HeaderSpec
