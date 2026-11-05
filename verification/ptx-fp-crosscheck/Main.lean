import Crosscheck
open Ptx.Fp Crosscheck

/-- Field boundaries, ties around one, signed zeros, NaNs and infinities.
    All patterns are generated here; no upstream test fixtures are copied. -/
def corpus (F : Fmt) : Array Nat := Id.run do
  let mut xs := #[]
  for sign in [0, F.signBit] do
    for exp in [0, 1, 2, F.bias - 1, F.bias, F.bias + 1, F.expMax - 1, F.expMax] do
      for frac in [0, 1, 2, 2^(F.fb-1)-1, 2^(F.fb-1), 2^F.fb-2, 2^F.fb-1] do
        xs := xs.push (sign + exp * 2^F.fb + frac)
  return xs

def check (F : Fmt) (m : RMode) (op : Op) (a b c : Nat) : IO Unit := do
  let expected := production F m op a b c
  let actual := upstream F m op a b c
  unless actual == expected do
    throw <| IO.userError s!"mismatch {repr F} {repr m} {repr op}: {a} {b} {c}: PTX={expected}, fp-lean={actual}"

def checkRepresentation (F : Fmt) (a : Nat) : IO Unit := do
  let x := unpack F a
  unless x.toBits.toNat == a && x.sign == F.sgn a && x.isNaN == F.isNaN a &&
      x.isInfinite == F.isInf a && x.isZero == F.isZero a &&
      x.isNonzeroSubnorm == F.isSub a do
    throw <| IO.userError s!"representation mismatch f{1+F.eb+F.fb}: {a}"
  let q := if F.isNaN a || F.isInf a then none else some (F.toQ a)
  unless x.toRat? == q do
    throw <| IO.userError s!"finite decode mismatch f{1+F.eb+F.fb}: {a}"
  if let some r := q then
    if r != 0 then
      unless F.encode r == a do
        throw <| IO.userError s!"finite encode mismatch f{1+F.eb+F.fb}: {a}"

def runFormat (F : Fmt) : IO Unit := do
  let xs := corpus F
  for a in xs do checkRepresentation F a
  let mut count := 0
  for m in [RMode.rn, .rz, .rm, .rp] do
    for a in xs do
      check F m .sqrt a 0 0
      count := count + 1
      for b in xs do
        for op in [Op.add, .sub, .mul, .div] do
          check F m op a b 0
          count := count + 1
        -- FMA: selected triples, including exact and near cancellation.
        for c in [0, F.signBit, F.one, negBits F a, negBits F b] do
          check F m .fma a b c
          count := count + 1
  -- Reproducible full-width pseudorandom triples, including all exponent fields.
  let mut seed := 0x5e5f1234abcd9876
  let modulus := 2^(1+F.eb+F.fb)
  for _ in [:256] do
    seed := (seed * 6364136223846793005 + 1442695040888963407) % 2^64
    let a := seed % modulus
    seed := (seed * 6364136223846793005 + 1442695040888963407) % 2^64
    let b := seed % modulus
    seed := (seed * 6364136223846793005 + 1442695040888963407) % 2^64
    let c := seed % modulus
    for x in [a, b, c] do checkRepresentation F x
    for m in [RMode.rn, .rz, .rm, .rp] do
      for op in [Op.add, .sub, .mul, .div, .fma, .sqrt] do
        check F m op a b c
        count := count + 1
  IO.println s!"f{1+F.eb+F.fb}: {xs.size + 3*256} representation inputs passed"
  IO.println s!"f{1+F.eb+F.fb}: {count} arithmetic comparisons passed (NaNs collapsed, signed zeros exact)"

def main : IO Unit := do
  runFormat Fmt.f32
  runFormat Fmt.f64
