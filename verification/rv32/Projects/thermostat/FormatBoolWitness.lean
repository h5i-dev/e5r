import Projects.thermostat.FormatBool
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.FormatBoolWitness
open E5R E5R.Thermostat

def ram (b : Bool) (a : Word) : BitVec 8 :=
  if a.toNat = 0x80010000 then Encoding.boolByte b
  else if a.toNat = 0x80020002 then 7#8
  else if a.toNat = 0x80020003 then 128#8
  else if a.toNat = 0x80020004 then 32#8
  else if a.toNat = 0x80020008 then 3#8
  else if a.toNat = 0x80030002 then 2#8
  else if a.toNat = 0x80030003 then 128#8
  else if a.toNat = 0x80030004 then 4#8
  else if a.toNat = 0x80030005 then 92#8
  else if a.toNat = 0x80030007 then 128#8
  else if (0x80020000 ≤ a.toNat ∧ a.toNat < 0x8002000c) ∨ (0x80030000 ≤ a.toNat ∧ a.toNat < 0x8003000c) then 0#8
  else if a.toNat = 0x80070000 then 65#8 else if a.toNat = 0x80070001 then 66#8 else if a.toNat = 0x80070002 then 67#8
  else 255#8

def core : Core :=
  ⟨0x80005112#32,(fun r => if r = 1 then 0x80000abc#32 else if r = 2 then 0x80050040#32
    else if r = 10 then 0x80010000#32 else if r = 11 then 0x80030000#32
    else BitVec.ofNat 32 (0x11110000+r.val)),false,false,3,0,0,0,0,0,false⟩

theorem data (b : Bool) : FormatInput.Data UartPlatform.board (ram b) 0x80050000#32 0x80030000#32 0x80020000#32
    (FormatLiterals.boolPointer b) 0x80070000#32 0#32 32 3 (ReplyJson.boolean b) := by
  have hl : CursorInput.Layout UartPlatform.board (ram b) (0x80050000#32+32#32) 0x80020000#32
      (FormatLiterals.boolPointer b) 0x80070000#32 32 3 (ReplyJson.boolean b) := by
    cases b
    all_goals refine ⟨?_,by decide,?_,by decide,by decide,by decide,by decide +kernel,by decide +kernel,by decide +kernel,
      FormatLiterals.bool_span _ _,by decide,?_,by decide,?_,?_,?_,?_,?_⟩
    all_goals first
      | (unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel)
      | (exact WordRegions.before _ _ _ _ (by decide) (by decide))
      | (exact WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
  cases b
  all_goals refine ⟨?_,by decide,?_,by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide,?_,hl,?_,?_,?_⟩
  all_goals first
    | (unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel)
    | (exact WordRegions.before _ _ _ _ (by decide) (by decide))
    | (exact WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))

/-- Both bool values pass the actual Display/Formatter/vtable/Cursor/memcpy
    chain, append after an existing prefix, and restore all13nonzero saves. -/
theorem appends_boolean (b : Bool) :
    ∃ d n r, n ≤ 116 ∧ Trace.Closed UartPlatform.board img n ⟨core,ram b⟩ ⟨d,r⟩ ∧
      FormatCursor.Returned core d ∧ d.get 10 = 0#32 ∧
      Bytes.Span UartPlatform.board r 0x80070003#32 (ReplyJson.boolean b) ∧
      ramRead r 0x80020008#32 .w = BitVec.ofNat 32 (3+(ReplyJson.boolean b).length) ∧ r 0x80070000#32 = 65#8 := by
  have hb : ReadBytes.Byte UartPlatform.board img (ram b) 0x80010000#32 (Encoding.boolByte b) := by
    apply ReadBytes.Byte.ram
    · unfold UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
    · cases b <;> decide +kernel
  obtain ⟨d,n,r,hn,ht,hd⟩ := FormatBool.contract UartPlatform.board core (ram b) 0x80050000#32 0x80030000#32
    0x80020000#32 0x80010000#32 0x80070000#32 0#32 32 3 b rfl rfl rfl rfl hb (data b) FormatLiterals.cursor_method_outside
  have hfit : 3+(ReplyJson.boolean b).length ≤ 32 := by cases b <;> decide
  have hlen : (ReplyJson.boolean b).length ≤ 5 := by cases b <;> decide
  refine ⟨d,n,r,by omega,Interrupt.close ht rfl,hd.returned,?_,hd.written hfit,?_,?_⟩
  · simpa only [Cursor.resultWord,ite_eq_left hfit] using hd.result
  · change ramRead r (0x80020000#32+8#32) .w = BitVec.ofNat 32 (3+(ReplyJson.boolean b).length)
    simpa only [Cursor.nextPosition,ite_eq_left hfit] using hd.position
  · exact hd.frame 0x80070000#32 (by decide +kernel) (by
      intro i
      have hi := i.isLt
      have hh := Bytes.offset_ne 0x80070000#32 0 (3+i.val) (by decide) (by omega) (by omega)
      simpa only [BitVec.add_zero,BitVec.ofNat_add,BitVec.add_assoc] using hh) (by decide +kernel)
end E5R.Thermostat.FormatBoolWitness
