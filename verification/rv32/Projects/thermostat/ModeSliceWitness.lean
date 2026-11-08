import Projects.thermostat.FormatSlice
import Projects.thermostat.ModeLiterals
import Projects.thermostat.I16DisplayWitness
namespace E5R.Thermostat.ModeSliceWitness
open E5R E5R.Thermostat

def ram (m : Spec.Mode) := ramWrite
  (ramWrite I16DisplayWitness.baseRam 0x80010000#32 (ModeLiterals.pointer m) .w)
  0x80010004#32 (BitVec.ofNat 32 (ReplyJson.mode m).length) .w

def core : Core :=
  ⟨0x8000228c#32,(fun r => if r = 1 then 0x80000abc#32 else if r = 2 then 0x80050040#32
    else if r = 10 then 0x80010000#32 else if r = 11 then 0x80030000#32
    else BitVec.ofNat 32 (0x11110000+r.val)),false,false,3,0,0,0,0,0,false⟩

theorem data (m : Spec.Mode) : FormatInput.Data UartPlatform.board (ram m) 0x80050000#32 0x80030000#32 0x80020000#32
    (ModeLiterals.pointer m) 0x80070000#32 0x60000020#32 32 3 (ReplyJson.mode m) := by
  have hl : CursorInput.Layout UartPlatform.board (ram m) (0x80050000#32+32#32) 0x80020000#32
      (ModeLiterals.pointer m) 0x80070000#32 32 3 (ReplyJson.mode m) := by
    cases m
    all_goals refine ⟨?_,by decide,?_,by decide,by decide,by decide,by decide +kernel,by decide +kernel,by decide +kernel,
      ModeLiterals.span _ _,by decide,?_,by decide,?_,?_,?_,?_,?_⟩
    all_goals first
      | (unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel)
      | (exact WordRegions.before _ _ _ _ (by decide) (by decide))
      | (exact WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
  cases m
  all_goals refine ⟨?_,by decide,?_,by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide,?_,hl,?_,?_,?_⟩
  all_goals first
    | (unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel)
    | (exact WordRegions.before _ _ _ _ (by decide) (by decide))
    | (exact WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))

theorem appends_mode (m : Spec.Mode) :
    ∃ d n r, n ≤ 116 ∧ Trace.Closed UartPlatform.board img n ⟨core,ram m⟩ ⟨d,r⟩ ∧
      FormatCursor.Returned core d ∧ d.get 10 = 0#32 ∧ Bytes.Span UartPlatform.board r 0x80070003#32 (ReplyJson.mode m) := by
  obtain ⟨d,n,r,hn,td,hd⟩ := FormatSlice.contract UartPlatform.board core (ram m) 0x80050000#32 0x80030000#32
    0x80020000#32 0x80010000#32 (ModeLiterals.pointer m) 0x80070000#32 0x60000020#32 32 3 (ReplyJson.mode m)
    rfl rfl rfl rfl (by unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel)
    (by decide) (by cases m <;> decide +kernel) (by cases m <;> decide +kernel) (data m) FormatLiterals.cursor_method_outside
  have hfit : 3+(ReplyJson.mode m).length ≤ 32 := by cases m <;> decide
  have hlen : (ReplyJson.mode m).length ≤ 4 := by cases m <;> decide
  exact ⟨d,n,r,by omega,Interrupt.close td rfl,hd.returned,by simpa only [Cursor.resultWord,ite_eq_left hfit] using hd.result,hd.written hfit⟩
end E5R.Thermostat.ModeSliceWitness
