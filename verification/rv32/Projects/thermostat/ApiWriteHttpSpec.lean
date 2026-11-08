import Projects.thermostat.TempHttpSpec
set_option autoImplicit false
namespace E5R.Thermostat.ApiWriteHttpSpec
open E5R E5R.Thermostat

abbrev Reply := TempHttpSpec.Reply

/-- Byte-only HTTP write evaluator. The router must separately establish the
    selected API path and first captured segment; the decoder is not a router. -/
def run (s : Spec.Snapshot) (path : List (BitVec 8)) (first : Option (List (BitVec 8)))
    (raw body : List (BitVec 8)) (entries : List HeaderSpec.Entry) : Reply :=
  if AuthSpec.authorized (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) (WireSpec.ascii "dev-key") then
    match WireSpec.decode path body first with
    | .error status => ⟨s,status,[],[]⟩
    | .ok cmd => match Spec.transition true s cmd with
      | .error err => ⟨s,ReplyJson.errorStatus err,WireSpec.ascii "application/json",ReplyJson.errorBody err⟩
      | .ok res => ⟨Spec.commit s (.ok res),200,WireSpec.ascii "application/json",ReplyJson.snapshot res.reply⟩
  else ⟨s,401,[],[]⟩

theorem decode_errors (path body : List (BitVec 8)) (first : Option (List (BitVec 8))) (status : Nat)
    (h : WireSpec.decode path body first=.error status) : status=400 ∨ status=404 := by
  unfold WireSpec.decode WireSpec.number WireSpec.relay at h
  try dsimp only at h
  split at h
  · cases h
  · try dsimp only at h
    split at h
    · cases parsed : DecimalSpec.parse (TrimMath.trim body) <;> simp only [parsed] at h
      · cases h;exact Or.inl rfl
      · cases h
    · try dsimp only at h
      split at h
      · cases parsed : DecimalSpec.parse (TrimMath.trim body) <;> simp only [parsed] at h
        · cases h;exact Or.inl rfl
        · cases h
      · try dsimp only at h
        split at h
        · try dsimp only at h
          split at h
          · cases h
          · try dsimp only at h
            split at h
            · cases h
            · try dsimp only at h
              split at h
              · cases h
              · cases h;exact Or.inl rfl
        · try dsimp only at h
          split at h
          · cases h;exact Or.inr rfl
          · try dsimp only at h
            split at h
            · try dsimp only at h
              split at h
              · cases h
              · try dsimp only at h
                split at h
                · cases h
                · cases h;exact Or.inl rfl
            · cases h;exact Or.inr rfl
end E5R.Thermostat.ApiWriteHttpSpec
