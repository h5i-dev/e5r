import Projects.thermostat.ParamMath
import Projects.thermostat.Subspan
namespace E5R.Thermostat.ParamInput
open E5R E5R.Thermostat

def captured (path : List (BitVec 8)) (s e : Nat) := (path.drop s).take (e-s)

/-- The actual first capture of a valid Request. Every raw offset used by the
    ELF is explicit, and capture bounds give checked views into the real path. -/
structure Capture (B : Board) (ram : Word → BitVec 8) (req pathPtr : Word)
    (path : List (BitVec 8)) (s e count : Nat) : Prop where
  object : Memory.Block B req 372
  aligned : req.toNat%4 = 0
  count_word : ramRead ram (req+368#32) .w = BitVec.ofNat 32 count
  count_bound : 1 ≤ count ∧ count ≤ 4
  path_pointer : ramRead ram (req+304#32) .w = pathPtr
  path_length : ramRead ram (req+308#32) .w = BitVec.ofNat 32 path.length
  start_word : ramRead ram (req+336#32) .w = BitVec.ofNat 32 s
  finish_word : ramRead ram (req+340#32) .w = BitVec.ofNat 32 e
  ordered : s ≤ e
  bounded : e ≤ path.length
  bytes : Bytes.Span B ram pathPtr path

theorem Capture.span {B ram req pathPtr path s e count} (h : Capture B ram req pathPtr path s e count) :
    Bytes.Span B ram (pathPtr+BitVec.ofNat 32 s) (captured path s e) :=
  Bytes.subspan h.bytes s e ⟨h.ordered,h.bounded⟩

theorem Capture.length {B ram req pathPtr path s e count} (h : Capture B ram req pathPtr path s e count) :
    (captured path s e).length = e-s := Bytes.subspan_length path s e ⟨h.ordered,h.bounded⟩
end E5R.Thermostat.ParamInput
