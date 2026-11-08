import Projects.thermostat.UartWritePrepare
import Projects.thermostat.UartWriteComplete
import Projects.thermostat.UartTxLoop
import Projects.thermostat.UartWriteRegs
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.UartWriteNonzero
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

def memory (ram : Word → BitVec 8) (obj io src len : Word) := UartWriteComplete.memory (UartWritePrepare.memory ram obj io src len) obj src len

/-- Complete actual fresh write_all for a nonempty source, including its
    Future fields, observed byte loop, zero remaining length and real RET. -/
theorem contract (c : Core) (ram : Word → BitVec 8) (obj io src : Word) (bs : List (BitVec 8)) (slots : List UartTxLoop.Slot)
    (hp : c.pc=0x80000786#32) (h10 : c.get 10=obj) (hm : Memory.Block B obj 41) (ha : obj.toNat%4=0)
    (hz : ram (obj+40#32)=0#8) (h0 : ramRead ram obj .w=io)
    (h4 : ramRead ram (obj+4#32) .w=src) (h8 : ramRead ram (obj+8#32) .w=BitVec.ofNat 32 bs.length)
    (hn : 0<bs.length) (hlen : slots.length=bs.length) (hs : ReadBytes.Span B img ram src bs)
    (hw : src.toNat+bs.length<2^32) (hsep : WordRegions.Disjoint src bs.length obj 41) :
    ∃ d, Observed.Steps B img (36+UartTxLoop.duration slots) ⟨c,ram⟩ ⟨d,memory ram obj io src (BitVec.ofNat 32 bs.length)⟩
      (UartTxLoop.reads slots) (UartTxLoop.events bs) ∧ FormatCursor.Returned c d := by
  let len := BitVec.ofNat 32 bs.length
  have hne : len≠0#32 := by
    intro he
    have hh := congrArg BitVec.toNat he
    change bs.length%2^32=0 at hh
    rw [Nat.mod_eq_of_lt hs.length] at hh;omega
  obtain ⟨a,ta,pa,a10,a11,a12,a13,a14,a15,ar,ac⟩ := UartWritePrepare.contract B c ram obj io src len hp h10 hm ha hz h0 h4 h8 hne
  let r0 := UartWritePrepare.memory ram obj io src len
  have hs' : ReadBytes.Span B img r0 src bs := ⟨hs.length,hs.nowrap,fun i =>
    (hs.bytes i).frame (UartWritePrepare.frame ram obj io src len _ (hsep i))⟩
  obtain ⟨b,tb,pb,_,br,bc⟩ := UartTxLoop.contract a r0 src bs slots hn hlen pa a12 a14 a13 a15 hs' hw
  have b10 := (br 10 (by decide) (by decide) (by decide)).trans a10
  have b11 := (br 11 (by decide) (by decide) (by decide)).trans a11
  obtain ⟨d,td,pd,dr,dc⟩ := UartWriteComplete.contract B b r0 obj src len pb b10 b11 hm ha
    (UartWritePrepare.length ram obj io src len) (UartWritePrepare.source ram obj io src len)
  have hf : UartWriteRegs.Frame c d := by
    intro reg h11 h12 h13 h14 h15 h16 h17
    exact (dr reg h11 h12 h14).trans ((br reg h12 h16 h17).trans (ar reg h11 h12 h13 h14 h15))
  have b1 : b.get 1=c.get 1 := (br 1 (by decide) (by decide) (by decide)).trans
    (ar 1 (by decide) (by decide) (by decide) (by decide) (by decide))
  refine ⟨d,?_,UartWriteRegs.returned (by rw [pd,b1]) (dc.trans (bc.trans ac)) hf⟩
  have tt := (ta.observed.trans tb).trans td.observed
  rw [show 22+UartTxLoop.duration slots+14=36+UartTxLoop.duration slots by omega] at tt
  simpa only [memory,r0,len,List.nil_append,List.append_nil] using tt

theorem source (ram : Word → BitVec 8) (obj io src len : Word) : ramRead (memory ram obj io src len) (obj+16#32) .w=src+len := UartWriteComplete.source _ obj src len

theorem length (ram : Word → BitVec 8) (obj io src len : Word) : ramRead (memory ram obj io src len) (obj+20#32) .w=0#32 := UartWriteComplete.length _ obj src len

theorem complete (ram : Word → BitVec 8) (obj io src len : Word) : memory ram obj io src len (obj+40#32)=1#8 := UartWriteComplete.complete _ obj src len

theorem frame (ram : Word → BitVec 8) (obj io src len x : Word) (hx : ∀ i : Fin 41, x≠obj+BitVec.ofNat 32 i.val) : memory ram obj io src len x=ram x :=
  (UartWriteComplete.frame _ obj src len x hx).trans (UartWritePrepare.frame ram obj io src len x hx)
end E5R.Thermostat.UartWriteNonzero
