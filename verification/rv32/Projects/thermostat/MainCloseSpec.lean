import Projects.thermostat.HeaderSpec
import Projects.thermostat.TrimMath
set_option autoImplicit false
namespace E5R.Thermostat.MainCloseSpec
open E5R E5R.Thermostat

/-- Exact source behavior: every comma token is trimmed and compared with
    ASCII case folding. This intentionally uses Rust's established byte set. -/
def hasClose (value : List (BitVec 8)) : Bool :=
  (value.splitOn 44#8).any (fun token => HeaderSpec.same (TrimMath.trim token) (WireSpec.ascii "close"))

def field (name value : List (BitVec 8)) : Bool :=
  HeaderSpec.same name (WireSpec.ascii "connection") && hasClose value

def wantsClose (raw : List (BitVec 8)) (entries : List HeaderSpec.Entry) : Bool :=
  entries.any (fun e => field (HeaderSpec.name raw e) (HeaderSpec.value raw e))

def mustClose (minor served : Nat) (raw : List (BitVec 8)) (entries : List HeaderSpec.Entry) : Bool :=
  decide (minor=0 ∨ 100≤served) || wantsClose raw entries

theorem http10 (served : Nat) (raw : List (BitVec 8)) (entries : List HeaderSpec.Entry) : mustClose 0 served raw entries=true := by
  simp [mustClose]

theorem limit (minor served : Nat) (reached : 100≤served) (raw : List (BitVec 8)) (entries : List HeaderSpec.Entry) : mustClose minor served raw entries=true := by
  simp [mustClose,reached]

theorem persistent (minor served : Nat) (version : minor≠0) (room : served<100) (raw : List (BitVec 8)) (entries : List HeaderSpec.Entry) :
    mustClose minor served raw entries=wantsClose raw entries := by
  have notReached : ¬100≤served := by omega
  simp [mustClose,version,notReached]

theorem correspondence (raw : List (BitVec 8)) (entries : List HeaderSpec.Entry) :
    wantsClose raw entries=true ↔ ∃ e∈entries,
      HeaderSpec.same (HeaderSpec.name raw e) (WireSpec.ascii "connection")=true ∧
      ∃ token∈(HeaderSpec.value raw e).splitOn 44#8,
        HeaderSpec.same (TrimMath.trim token) (WireSpec.ascii "close")=true := by
  simp [wantsClose,field,hasClose,Bool.and_eq_true]

theorem token_regressions :
    hasClose (WireSpec.ascii "keep-alive, ClOsE")=true ∧
    hasClose (WireSpec.ascii "disclose, closex")=false ∧
    hasClose []=false ∧ hasClose [9,99,108,111,115,101,32,9]=true ∧
    hasClose (WireSpec.ascii "clo se")=false ∧ hasClose [11,99,108,111,115,101,11]=false := by decide +kernel

theorem duplicate_regression : wantsClose (WireSpec.ascii "connectionkeep-aliveCONNECTIONclose")
    [⟨0,10,10,20⟩,⟨20,30,30,35⟩]=true := by decide +kernel
end E5R.Thermostat.MainCloseSpec
