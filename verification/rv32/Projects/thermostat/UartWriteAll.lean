import Projects.thermostat.UartWriteNonzero
import Projects.thermostat.UartWriteZero
namespace E5R.Thermostat.UartWriteAll
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

def time (bs : List (BitVec 8)) (slots : List UartTxLoop.Slot) : Nat := if bs=[] then 14 else 36+UartTxLoop.duration slots
def memory (ram : Word → BitVec 8) (obj io src : Word) (bs : List (BitVec 8)) :=
  if bs=[] then UartWriteZero.memory ram obj io src else UartWriteNonzero.memory ram obj io src (BitVec.ofNat 32 bs.length)

/-- The actual UART write_all from its fresh Future entry through real RET.
    Ready schedules are explicit finite environment inputs; no readiness or
    delivery guarantee is invented. Event projection is exactly the source. -/
theorem contract (c : Core) (ram : Word → BitVec 8) (obj io src : Word) (bs : List (BitVec 8)) (slots : List UartTxLoop.Slot)
    (hp : c.pc=0x80000786#32) (h10 : c.get 10=obj) (hm : Memory.Block B obj 41) (ha : obj.toNat%4=0)
    (hz : ram (obj+40#32)=0#8) (h0 : ramRead ram obj .w=io)
    (h4 : ramRead ram (obj+4#32) .w=src) (h8 : ramRead ram (obj+8#32) .w=BitVec.ofNat 32 bs.length)
    (hlen : slots.length=bs.length) (hs : ReadBytes.Span B img ram src bs)
    (hw : src.toNat+bs.length<2^32) (hsep : WordRegions.Disjoint src bs.length obj 41) :
    ∃ d, Observed.Steps B img (time bs slots) ⟨c,ram⟩ ⟨d,memory ram obj io src bs⟩
      (UartTxLoop.reads slots) (UartTxLoop.events bs) ∧ FormatCursor.Returned c d ∧
      memory ram obj io src bs (obj+40#32)=1#8 ∧
      ramRead (memory ram obj io src bs) (obj+16#32) .w=src+BitVec.ofNat 32 bs.length ∧
      ramRead (memory ram obj io src bs) (obj+20#32) .w=0#32 ∧
      ReadBytes.Span B img (memory ram obj io src bs) src bs ∧
      (∀ x, (∀ i : Fin 41, x≠obj+BitVec.ofNat 32 i.val) → memory ram obj io src bs x=ram x) := by
  have frame (x : Word) (hx : ∀ i : Fin 41, x≠obj+BitVec.ofNat 32 i.val) : memory ram obj io src bs x=ram x := by
    unfold memory
    split
    · exact UartWriteZero.frame ram obj io src x hx
    · exact UartWriteNonzero.frame ram obj io src _ x hx
  have hs' : ReadBytes.Span B img (memory ram obj io src bs) src bs :=
    ⟨hs.length,hs.nowrap,fun i => (hs.bytes i).frame (frame _ (hsep i))⟩
  cases bs with
  | nil =>
    have hslots : slots=[] := List.eq_nil_of_length_eq_zero (by simpa only [List.length_nil] using hlen)
    subst slots
    obtain ⟨d,td,hr⟩ := UartWriteZero.contract B c ram obj io src hp h10 hm ha hz h0 h4 h8
    refine ⟨d,?_,hr,UartWriteZero.complete ram obj io src,?_,UartWriteZero.length ram obj io src,hs',frame⟩
    · exact td.observed
    · simpa only [List.length_nil,show BitVec.ofNat 32 0=0#32 from rfl,BitVec.add_zero,memory,ite_true] using UartWriteZero.source ram obj io src
  | cons b bs =>
    obtain ⟨d,td,hr⟩ := UartWriteNonzero.contract c ram obj io src (b::bs) slots hp h10 hm ha hz h0 h4 h8 (by simp) hlen hs hw hsep
    refine ⟨d,?_,hr,UartWriteNonzero.complete ram obj io src _,UartWriteNonzero.source ram obj io src _,UartWriteNonzero.length ram obj io src _,hs',frame⟩
    simpa only [time,memory,List.cons_ne_self,List.cons_ne_nil,ite_false] using td

/-- A direct observation theorem, separate from physical UART delivery. -/
theorem projection (bs : List (BitVec 8)) (slots : List UartTxLoop.Slot) :
    Observed.input (UartTxLoop.reads slots)=[] ∧ Observed.output (UartTxLoop.events bs)=bs :=
  ⟨UartTxLoop.no_input slots,UartTxLoop.output bs⟩
end E5R.Thermostat.UartWriteAll
