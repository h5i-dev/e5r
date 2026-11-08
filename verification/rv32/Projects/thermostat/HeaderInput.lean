import Projects.thermostat.HeaderSpec
import Projects.thermostat.Subspan
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.HeaderInput
open E5R E5R.Thermostat

/-- Exactly the four usize fields read at the actual 16-byte Header slot. -/
structure Cell (B : Board) (ram : Word → BitVec 8) (p : Word) (rawLength : Nat) (e : HeaderSpec.Entry) : Prop where
  block : Memory.Block B p 16
  aligned : p.toNat%4 = 0
  nameStart : ramRead ram p .w = BitVec.ofNat 32 e.nameStart
  nameEnd : ramRead ram (p+4#32) .w = BitVec.ofNat 32 e.nameEnd
  valueStart : ramRead ram (p+8#32) .w = BitVec.ofNat 32 e.valueStart
  valueEnd : ramRead ram (p+12#32) .w = BitVec.ofNat 32 e.valueEnd
  bounds : HeaderSpec.Bounds rawLength e

structure Table (B : Board) (ram : Word → BitVec 8) (p : Word) (rawLength : Nat) (entries : List HeaderSpec.Entry) : Prop where
  bounded : entries.length ≤ 16
  cells : ∀ i : Fin entries.length, Cell B ram (p+BitVec.ofNat 32 (16*i.val)) rawLength entries[i]

theorem Table.head {B ram p n e es} (h : Table B ram p n (e::es)) : Cell B ram p n e := by
  have hc := h.cells ⟨0,by simp⟩
  change Cell B ram (p+0#32) n e at hc
  simpa only [BitVec.add_zero] using hc

theorem Table.tail {B ram p n e es} (h : Table B ram p n (e::es)) : Table B ram (p+16#32) n es := by
  refine ⟨by have := h.bounded;simp only [List.length_cons] at this;omega,?_⟩
  intro i
  have hi := i.isLt
  have hc := h.cells ⟨i.val+1,by simpa using Nat.succ_lt_succ hi⟩
  have he : (p+16#32)+BitVec.ofNat 32 (16*i.val) = p+BitVec.ofNat 32 (16*(i.val+1)) := by
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    apply congrArg (fun k : Nat => p+BitVec.ofNat 32 k)
    omega
  rw [he];exact hc

theorem name_span {B ram p raw e} (hraw : Bytes.Span B ram p raw) (hb : HeaderSpec.Bounds raw.length e) :
    Bytes.Span B ram (p+BitVec.ofNat 32 e.nameStart) (HeaderSpec.name raw e) :=
  Bytes.subspan hraw e.nameStart e.nameEnd ⟨hb.1,hb.2.1⟩

theorem value_span {B ram p raw e} (hraw : Bytes.Span B ram p raw) (hb : HeaderSpec.Bounds raw.length e) :
    Bytes.Span B ram (p+BitVec.ofNat 32 e.valueStart) (HeaderSpec.value raw e) :=
  Bytes.subspan hraw e.valueStart e.valueEnd ⟨hb.2.2.1,hb.2.2.2⟩

theorem name_length {raw e} (hb : HeaderSpec.Bounds raw.length e) :
    (HeaderSpec.name raw e).length = e.nameEnd-e.nameStart := Bytes.subspan_length raw _ _ ⟨hb.1,hb.2.1⟩

theorem value_length {raw e} (hb : HeaderSpec.Bounds raw.length e) :
    (HeaderSpec.value raw e).length = e.valueEnd-e.valueStart := Bytes.subspan_length raw _ _ ⟨hb.2.2.1,hb.2.2.2⟩
end E5R.Thermostat.HeaderInput
