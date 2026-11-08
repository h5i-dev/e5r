import Projects.thermostat.Cursor
import Projects.thermostat.JsonLiterals
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.CursorWitness
open E5R E5R.Thermostat

def capacity (fits : Bool) : Nat := if fits then 32 else 14

def ram (fits : Bool) (a : Word) : BitVec 8 :=
  if a.toNat = 0x80020002 then 7#8
  else if a.toNat = 0x80020003 then 128#8
  else if a.toNat = 0x80020004 then BitVec.ofNat 8 (capacity fits)
  else if 0x80020000 ≤ a.toNat ∧ a.toNat < 0x8002000c then 0#8
  else 255#8

def core : Core :=
  ⟨0x800022a0#32,(fun r => if r = 1 then 0x80000abc#32 else if r = 2 then 0x80050020#32
    else if r = 10 then 0x80020000#32 else if r = 11 then 0x8000574c#32 else if r = 12 then 15#32
    else BitVec.ofNat 32 (0x11110000+r.val)),false,false,3,0,0,0,0,0,false⟩

theorem pre (fits : Bool) : CursorInput.Pre UartPlatform.board core (ram fits) 0x80050000#32 0x80020000#32
    0x8000574c#32 0x80070000#32 (capacity fits) 0 JsonLiterals.prefixBytes := by
  cases fits
  all_goals refine ⟨rfl,rfl,rfl,rfl,rfl,?_,by decide,?_,by decide,by decide,by decide,
    by decide +kernel,by decide +kernel,by decide +kernel,JsonLiterals.prefix_span _,by decide,?_,by decide,?_,?_,?_,?_,?_⟩
  all_goals first
    | (unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel)
    | (exact WordRegions.before _ _ _ _ (by decide) (by decide))
    | (exact WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))

/-- Real JSON literal in this ELF is appended to the Cursor and the nonzero
    callee saves are restored. -/
theorem appends_json_prefix :
    ∃ d n r, n ≤ 131 ∧ Trace.Closed UartPlatform.board img n ⟨core,ram true⟩ ⟨d,r⟩ ∧
      CursorExit.Returned core d ∧ d.get 10 = 0#32 ∧ ramRead r 0x80020008#32 .w = 15#32 ∧
      Bytes.Span UartPlatform.board r 0x80070000#32 JsonLiterals.prefixBytes := by
  obtain ⟨d,n,r,hn,ht,hpost⟩ := Cursor.contract UartPlatform.board core (ram true) 0x80050000#32 0x80020000#32
    0x8000574c#32 0x80070000#32 (capacity true) 0 JsonLiterals.prefixBytes (pre true)
  exact ⟨d,n,r,hn,Interrupt.close ht rfl,hpost.returned,hpost.result,hpost.position,hpost.written (by decide)⟩

/-- A fourteen-byte output cannot hold the fifteen-byte JSON prefix. The actual
    Cursor returns Err, keeps its position and leaves the output byte untouched. -/
theorem rejects_short_output :
    ∃ d n r, n ≤ 131 ∧ Trace.Closed UartPlatform.board img n ⟨core,ram false⟩ ⟨d,r⟩ ∧
      CursorExit.Returned core d ∧ d.get 10 = 1#32 ∧ ramRead r 0x80020008#32 .w = 0#32 ∧
      r 0x80070000#32 = 255#8 := by
  obtain ⟨d,n,r,hn,ht,hpost⟩ := Cursor.contract UartPlatform.board core (ram false) 0x80050000#32 0x80020000#32
    0x8000574c#32 0x80070000#32 (capacity false) 0 JsonLiterals.prefixBytes (pre false)
  refine ⟨d,n,r,hn,Interrupt.close ht rfl,hpost.returned,hpost.result,hpost.position,?_⟩
  exact hpost.refused (by decide) 0x80070000#32 (by decide +kernel)
end E5R.Thermostat.CursorWitness
