import Projects.thermostat.I16Display
import Projects.thermostat.PadWitness
import Projects.thermostat.Fields
import Projects.thermostat.StoreBytes
namespace E5R.Thermostat.I16DisplayWitness
open E5R E5R.Thermostat

def baseRam (a : Word) : BitVec 8 :=
  if a.toNat = 0x80030008 then 32#8 else if a.toNat = 0x8003000b then 96#8 else PadWitness.ram true a

def ram (v : BitVec 16) := ramWrite baseRam 0x80010000#32 (v.signExtend 32) .h

def core : Core :=
  ⟨0x80004e5e#32,(fun r => if r = 1 then 0x80000abc#32 else if r = 2 then 0x800500a0#32
    else if r = 10 then 0x80010000#32 else if r = 11 then 0x80030000#32
    else BitVec.ofNat 32 (0x11110000+r.val)),false,false,3,0,0,0,0,0,false⟩

theorem region (v : BitVec 16) (a : Word) (n : Nat) (h : WordRegions.Disjoint a n 0x80010000#32 2) :
    ViewFrame.Region baseRam (ram v) a n := by
  intro i
  exact StoreBytes.frame _ _ _ _ .h (h i)

theorem data (v : BitVec 16) : I16Input.Data UartPlatform.board (ram v) 0x80050000#32 0x80010000#32
    0x80030000#32 0x80020000#32 0x80070000#32 32 3 v := by
  have ho := region v 0x80020000#32 12 (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
  have hf := region v 0x80030000#32 14 (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
  have hp : ramRead (ram v) 0x80020000#32 .w = 0x80070000#32 := by
    have hh := ViewFrame.word ho 0 (by decide)
    simp only [BitVec.add_zero] at hh
    exact hh.trans (by decide +kernel)
  have hc : CharInput.Data UartPlatform.board (ram v) (0x80050000#32+16#32) 0x80020000#32 0x80070000#32 32 3 := by
    refine ⟨?_,by decide,?_,by decide,by decide,by decide,hp,(ViewFrame.word ho 4 (by decide)).trans (by decide +kernel),
      (ViewFrame.word ho 8 (by decide)).trans (by decide +kernel),?_,by decide,?_,?_,?_⟩
    all_goals first
      | (unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel)
      | (exact WordRegions.before _ _ _ _ (by decide) (by decide))
      | (exact WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
  refine ⟨hc,?_,by decide,?_,by decide,Fields.half_store_load _ _ v,?_,by decide,?_,
    (ViewFrame.word hf 4 (by decide)).trans (by decide +kernel),
    (ViewFrame.word hf 8 (by decide)).trans (by decide +kernel),
    (ViewFrame.half hf 12 (by decide)).trans (by decide +kernel),?_,?_,?_,?_⟩
  all_goals first
    | (unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel)
    | (exact WordRegions.before _ _ _ _ (by decide) (by decide))
    | (exact WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    | (have hh := ViewFrame.word hf 0 (by decide);simp only [BitVec.add_zero] at hh;exact hh.trans (by decide +kernel))

/-- Symbolically every i16 appends its exact signed decimal after ABC, returns
    to the real caller with all thirteen nonzero saves, and preserves ABC. -/
theorem all_values (v : BitVec 16) :
    ∃ d n r, n ≤ 292 ∧ Trace.Closed UartPlatform.board img n ⟨core,ram v⟩ ⟨d,r⟩ ∧
      FormatCursor.Returned core d ∧ d.get 10 = 0#32 ∧
      Bytes.Span UartPlatform.board r 0x80070003#32 (ReplyJson.signed v) ∧
      ramRead r 0x80020008#32 .w = BitVec.ofNat 32 (3+(ReplyJson.signed v).length) ∧ r 0x80070000#32 = 65#8 := by
  have hlen := ReplyJsonBounds.signed_length v
  have hfit : 3+(ReplyJson.signed v).length ≤ 32 := by omega
  obtain ⟨d,n,r,hn,td,hd⟩ := I16Display.contract UartPlatform.board core (ram v) 0x80050000#32 0x80010000#32
    0x80030000#32 0x80020000#32 0x80070000#32 32 3 v (data v) rfl rfl rfl rfl hfit
    FormatLiterals.cursor_method_outside FormatData.cursor_char_method_outside DigitTable.outside
  refine ⟨d,n,r,hn,Interrupt.close td rfl,hd.returned,?_,hd.written hfit,?_,?_⟩
  · simpa only [Cursor.resultWord,ite_eq_left hfit] using hd.result
  · change ramRead r (0x80020000#32+8#32) .w = _
    simpa only [Cursor.nextPosition,ite_eq_left hfit] using hd.position
  · apply Eq.trans (hd.frame 0x80070000#32 (by decide +kernel) (by
      intro i
      have hi := i.isLt
      simpa only [BitVec.add_zero,BitVec.ofNat_add,BitVec.add_assoc] using Bytes.offset_ne 0x80070000#32 0 (3+i.val) (by decide) (by omega) (by omega)) (by decide +kernel))
    unfold ram
    rw [StoreBytes.frame _ _ _ _ .h (by decide +kernel)]
    decide +kernel

theorem minimum :
    ∃ d n r, n ≤ 292 ∧ Trace.Closed UartPlatform.board img n ⟨core,ram 0x8000#16⟩ ⟨d,r⟩ ∧
      FormatCursor.Returned core d ∧ d.get 10 = 0#32 ∧ Bytes.Span UartPlatform.board r 0x80070003#32 (WireSpec.ascii "-32768") := by
  obtain ⟨d,n,r,hn,td,hd,hzero,hbytes,_,_⟩ := all_values 0x8000#16
  exact ⟨d,n,r,hn,td,hd,hzero,by simpa only [ReplyJson.minimum_signed] using hbytes⟩
end E5R.Thermostat.I16DisplayWitness
