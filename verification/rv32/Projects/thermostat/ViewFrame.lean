import Projects.thermostat.Wire
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.ViewFrame
open E5R E5R.Thermostat

/-- Pointwise equality on a checked object's bytes; no memory behavior is
    assumed beyond these explicit equalities. -/
def Region (before after : Word → BitVec 8) (p : Word) (n : Nat) : Prop :=
  ∀ i : Fin n, after (p+BitVec.ofNat 32 i.val) = before (p+BitVec.ofNat 32 i.val)

theorem word {before after p n} (h : Region before after p n) (k : Nat) (hk : k+4 ≤ n) :
    ramRead after (p+BitVec.ofNat 32 k) .w = ramRead before (p+BitVec.ofNat 32 k) .w := by
  apply ramRead_w_congr
  intro i hi
  rw [BitVec.add_assoc,←BitVec.ofNat_add]
  exact h ⟨k+i,by omega⟩

theorem span {B before after p xs} (h : Bytes.Span B before p xs) (hf : Region before after p xs.length) :
    Bytes.Span B after p xs := ⟨h.length,h.nowrap,h.memory,fun i => (hf i).trans (h.bytes i)⟩

theorem body {B before after req p xs} (h : DecodeInput.BodyAt B before req p xs)
    (ho : Region before after req 328) (hb : Region before after p xs.length) : DecodeInput.BodyAt B after req p xs :=
  ⟨h.object,h.aligned,(word ho 320 (by decide)).trans h.pointer,(word ho 324 (by decide)).trans h.length,span h.bytes hb⟩

theorem path {B before after req p xs} (h : PathDispatch.PathAt B before req p xs)
    (ho : Region before after req 312) (hb : Region before after p xs.length) : PathDispatch.PathAt B after req p xs :=
  ⟨h.object,h.aligned,(word ho 304 (by decide)).trans h.pointer,(word ho 308 (by decide)).trans h.length,span h.bytes hb⟩

theorem capture {B before after req p xs s e count} (h : ParamInput.Capture B before req p xs s e count)
    (ho : Region before after req 372) (hb : Region before after p xs.length) : ParamInput.Capture B after req p xs s e count :=
  ⟨h.object,h.aligned,(word ho 368 (by decide)).trans h.count_word,h.count_bound,
    (word ho 304 (by decide)).trans h.path_pointer,(word ho 308 (by decide)).trans h.path_length,
    (word ho 336 (by decide)).trans h.start_word,(word ho 340 (by decide)).trans h.finish_word,
    h.ordered,h.bounded,span h.bytes hb⟩

theorem params {B before after req p xs first} (h : WireInput.Params B before req p xs first)
    (ho : Region before after req 372) (hb : Region before after p xs.length) : WireInput.Params B after req p xs first := by
  cases h with
  | missing hm ha hz => exact .missing hm ha ((word ho 368 (by decide)).trans hz)
  | present hc => exact .present (capture hc ho hb)

theorem shrink {before after p n m} (h : Region before after p n) (hm : m ≤ n) : Region before after p m := by
  intro i;exact h ⟨i.val,by have := i.isLt;omega⟩

theorem snapshot {before after eng s} (h : Encoding.SnapshotAt before (eng+4#32) s)
    (hf : Region before after eng 25) : Encoding.SnapshotAt after (eng+4#32) s := by
  intro i
  have hi : 4+i.val < 25 := by have := i.isLt;omega
  have he : (eng+4#32)+BitVec.ofNat 32 i.val = eng+BitVec.ofNat 32 (4+i.val) := by rw [BitVec.add_assoc,←BitVec.ofNat_add]
  rw [he,hf ⟨4+i.val,hi⟩]
  simpa only [he] using h i
end E5R.Thermostat.ViewFrame
