import Projects.thermostat.MainHeaderToBody
import Projects.thermostat.MainLengthFrame
import Projects.thermostat.MainLengthReadSetup
namespace E5R.Thermostat.MainLengthState
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
abbrev fp := 0x80fff814#32
abbrev rx := 0x80ffec14#32

structure At (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (s : Spec.Snapshot) (head : Head) (amount : Nat) : Prop where
  stable : MainHeaderLoopTwo.Stable c ram input s
  view : HeadCompletedView.At ram (fp+116#32) head
  consumed : ramRead ram (fp+444#32) .w=BitVec.ofNat 32 head.len
  two : c.get 18=2#32
  length : c.get 20=BitVec.ofNat 32 head.len
  tag : c.get 9=HeadCompletedView.framingTag head.framing
  bounds : MainHeadAcceptedBounds.At 1024 1024 head
  kind : head.framing=.length amount
  total : ramRead ram (fp+452#32) .w=BitVec.ofNat 32 (head.len+amount)

theorem total_bound {c ram input s head amount} (h : At c ram input s head amount) : head.len+amount≤2048 := by
  have len := h.bounds.length.2
  have content := h.bounds.content amount h.kind
  omega

structure Ready (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (s : Spec.Snapshot) (head : Head) (amount : Nat) : Prop where
  pc : c.pc=0x80000c6c#32
  state : At c ram input s head amount
  dst : c.get 12=rx+BitVec.ofNat 32 input.length
  short : input.length<head.len+amount

def Boundary (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (s : Spec.Snapshot) (head : Head) (amount : Nat) : Prop :=
  if input.length<head.len+amount then Ready c ram input s head amount
  else c.pc=0x80000c98#32 ∧ At c ram input s head amount

/-- Existing parser bounds are monotone under a larger containing byte slice. -/
theorem widen {cap upper max head} (h : MainHeadAcceptedBounds.At cap max head) (le : cap≤upper) : MainHeadAcceptedBounds.At upper max head := by
  refine ⟨h.method,⟨h.target.1,h.target.2.1,by have := h.target.2.2;omega⟩,h.version,?_,⟨h.length.1,by have := h.length.2;omega⟩,h.content⟩
  intro entry mem
  obtain ⟨a,b,c,d⟩ := h.fields entry mem
  exact ⟨a,b,c,by omega⟩

/-- Receiving into RX and updating only the real count/poll words preserves
    the complete copied Head, body target and all committed App invariants. -/
theorem received {c d before after input s head amount} {b : BitVec 8}
    (h : At c before input s head amount)
    (stable : MainHeaderLoopTwo.Stable d after (input++[b]) s)
    (frame : MainLengthFrame.At before after input.length) (room : input.length<2048)
    (regs : ∀ r : Reg, r≠10 → r≠11 → r≠25 → d.get r=c.get r) : At d after (input++[b]) s head amount := by
  have headFrame := MainLengthFrame.region frame room 116 304 (by decide) (Or.inr (by decide))
  have consumedFrame := MainLengthFrame.region frame room 444 4 (by decide) (Or.inr (by decide))
  have totalFrame := MainLengthFrame.region frame room 452 4 (by decide) (Or.inr (by decide))
  refine ⟨stable,MainCopyView.head headFrame head h.view,?_,(regs 18 (by decide) (by decide) (by decide)).trans h.two,
    (regs 20 (by decide) (by decide) (by decide)).trans h.length,(regs 9 (by decide) (by decide) (by decide)).trans h.tag,h.bounds,h.kind,?_⟩
  · simpa only [BitVec.add_zero] using (ViewFrame.word consumedFrame 0 (by decide)).trans h.consumed
  · simpa only [BitVec.add_zero] using (ViewFrame.word totalFrame 0 (by decide)).trans h.total

/-- Rebuilding the receive descriptor changes bytes456..468 only. -/
theorem prepared {c d before after input s head amount} (h : At c before input s head amount)
    (stable : MainHeaderLoopTwo.Stable d after input s)
    (region : ViewFrame.Region before after fp 456)
    (regs : HeadRegisterFrame.At c d MainLengthReadSetup.writes) : At d after input s head amount := by
  have sub (off len : Nat) (bound : off+len≤456) : ViewFrame.Region before after (fp+BitVec.ofNat 32 off) len := by
    intro i
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add,Nat.add_assoc] using region ⟨off+i.val,by have := i.isLt;omega⟩
  refine ⟨stable,MainCopyView.head (sub 116 304 (by decide)) head h.view,?_,(regs 18 (by decide)).trans h.two,
    (regs 20 (by decide)).trans h.length,(regs 9 (by decide)).trans h.tag,h.bounds,h.kind,?_⟩
  · simpa only [BitVec.add_zero] using (ViewFrame.word (sub 444 4 (by decide)) 0 (by decide)).trans h.consumed
  · simpa only [BitVec.add_zero] using (ViewFrame.word (sub 452 4 (by decide)) 0 (by decide)).trans h.total
end E5R.Thermostat.MainLengthState
