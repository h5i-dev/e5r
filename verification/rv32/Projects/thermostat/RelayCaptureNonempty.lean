import Projects.thermostat.RelayCaptureStore
import Projects.thermostat.RouteLiteralEnd
set_option autoImplicit false
namespace E5R.Thermostat.RelayCaptureNonempty
open E5R E5R.Thermostat

/-- The actual nonempty capture stores its first segment before comparing
    against full path end. Extra slashes therefore returnfalse with one stored
    capture; no unchanged-params claim is made for that refusal. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (params captured full : Word)
    (h9 : c.get 9=full) (h18 : c.get 18=10#32) (h22 : c.get 22=10#32) (h11 : c.get 11=7#32)
    (h23 : c.get 23=captured) (h10 : c.get 10=7#32) (h21 : c.get 21=0x80005b9c#32) (h25 : c.get 25=1#32)
    (h26 : c.get 26=123#32) (h27 : c.get 27=125#32) (h8 : c.get 8=0#32) (h19 : c.get 19=params)
    (nonempty : 8≤captured.toNat) (ordered : captured.toNat≤full.toNat)
    (block : Memory.Block B params 8) (aligned : params.toNat%4=0)
    (pattern : ReadBytes.Span B img ram 0x80005b9c#32 (WireSpec.ascii "/relay/{i}")) (pc : c.pc=0x800028a8#32) :
    ∃ d, Quiet.Steps B img 29 ⟨c,ram⟩ ⟨d,MainRelayCapture.memory ram params captured⟩ ∧ d.pc=0x8000293a#32 ∧
      d.get 10=(if captured=full then 1#32 else 0#32) ∧ d.get 11=1#32 ∧
      (∀ r : Reg,r≠12 → r≠13 → r≠11 → r≠8 → r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,ta,pa,a8,ar,ac⟩ := RelayCaptureStore.contract B c ram params captured full h9 h18 h22 h11 h23 h10 h21 h25 h26 h27 h8 h19
    nonempty ordered block aligned pattern pc
  obtain ⟨d,td,pd,d10,d11,dr,dc⟩ := RouteLiteralEnd.contract B a (MainRelayCapture.memory ram params captured) 10#32 captured full 1#32 pa
    ((ar 22 (by decide) (by decide) (by decide) (by decide)).trans h22)
    ((ar 18 (by decide) (by decide) (by decide) (by decide)).trans h18)
    ((ar 23 (by decide) (by decide) (by decide) (by decide)).trans h23)
    ((ar 9 (by decide) (by decide) (by decide) (by decide)).trans h9) a8
  refine ⟨d,ta.trans td,pd,d10,d11,?_,dc.trans ac⟩
  intro r n12 n13 n11 n8 n10;exact (dr r n10 n11).trans (ar r n12 n13 n11 n8)
end E5R.Thermostat.RelayCaptureNonempty
