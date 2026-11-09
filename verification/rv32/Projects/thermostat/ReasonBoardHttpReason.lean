import Projects.thermostat.HttpReason
import Projects.thermostat.ReasonBoardHttpReason200Data
import Projects.thermostat.ReasonBoardHttpReason201Data
import Projects.thermostat.ReasonBoardHttpReason204Data
import Projects.thermostat.ReasonBoardHttpReason400Data
import Projects.thermostat.ReasonBoardHttpReason401Data
import Projects.thermostat.ReasonBoardHttpReason403Data
import Projects.thermostat.ReasonBoardHttpReason404Data
import Projects.thermostat.ReasonBoardHttpReason405Data
import Projects.thermostat.ReasonBoardHttpReason408Data
import Projects.thermostat.ReasonBoardHttpReason409Data
import Projects.thermostat.ReasonBoardHttpReason413Data
import Projects.thermostat.ReasonBoardHttpReason414Data
import Projects.thermostat.ReasonBoardHttpReason422Data
import Projects.thermostat.ReasonBoardHttpReason431Data
import Projects.thermostat.ReasonBoardHttpReason500Data
import Projects.thermostat.ReasonBoardHttpReason501Data
import Projects.thermostat.ReasonBoardHttpReason503Data
import Projects.thermostat.ReasonBoardHttpReason505Data
import Projects.thermostat.ReasonBoardHttpReasonDefault100
import Projects.thermostat.ReasonBoardHttpReasonDefault202
import Projects.thermostat.ReasonBoardHttpReasonDefault205
import Projects.thermostat.ReasonBoardHttpReasonDefault402
import Projects.thermostat.ReasonBoardHttpReasonDefault406
import Projects.thermostat.ReasonBoardHttpReasonDefault410
import Projects.thermostat.ReasonBoardHttpReasonDefault415
import Projects.thermostat.ReasonBoardHttpReasonDefault423
import Projects.thermostat.ReasonBoardHttpReasonDefault432
import Projects.thermostat.ReasonBoardHttpReasonDefault502
import Projects.thermostat.ReasonBoardHttpReasonDefault504
import Projects.thermostat.ReasonBoardHttpReasonDefault506
import Projects.thermostat.StackBoard
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 5000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.ReasonBoardHttpReason
open E5R E5R.Thermostat HttpReason
abbrev B := StackBoard.board

theorem contract (c : Core) (ram : Word → BitVec 8) (dst : Word) (status : Nat)
    (hlo : 100≤status) (hhi : status≤599) (hp : c.pc=0x80003584#32)
    (h10 : c.get 10=dst) (h11 : c.get 11=192#32) (h12 : c.get 12=13#32)
    (h13 : c.get 13=BitVec.ofNat 32 status) (hm : Memory.Block B dst 192) :
    ∃ d n, n≤178 ∧ Quiet.Steps B img n ⟨c,ram⟩
      ⟨d,ByteWrite.write ram (dst+13#32) (WireSpec.ascii (ResponseHeadSpec.reason status))⟩ ∧
      FormatCursor.Returned c d ∧ d.get 10=1#32 ∧
      d.get 11=BitVec.ofNat 32 (13+(WireSpec.ascii (ResponseHeadSpec.reason status)).length) ∧
      Bytes.Span B (ByteWrite.write ram (dst+13#32) (WireSpec.ascii (ResponseHeadSpec.reason status)))
        (dst+13#32) (WireSpec.ascii (ResponseHeadSpec.reason status)) := by
  by_cases h200 : status=200
  · subst status
    obtain ⟨d,td,hr,d10,d11,hbytes⟩ := ReasonBoardHttpReason200Data.contract c ram dst hp h10 h11 h12 h13 hm
    exact ⟨d,25,by decide,td,hr,d10,d11,hbytes⟩
  by_cases h201 : status=201
  · subst status
    obtain ⟨d,td,hr,d10,d11,hbytes⟩ := ReasonBoardHttpReason201Data.contract c ram dst hp h10 h11 h12 h13 hm
    exact ⟨d,36,by decide,td,hr,d10,d11,hbytes⟩
  by_cases h204 : status=204
  · subst status
    obtain ⟨d,td,hr,d10,d11,hbytes⟩ := ReasonBoardHttpReason204Data.contract c ram dst hp h10 h11 h12 h13 hm
    exact ⟨d,38,by decide,td,hr,d10,d11,hbytes⟩
  by_cases h400 : status=400
  · subst status
    obtain ⟨d,td,hr,d10,d11,hbytes⟩ := ReasonBoardHttpReason400Data.contract c ram dst hp h10 h11 h12 h13 hm
    exact ⟨d,44,by decide,td,hr,d10,d11,hbytes⟩
  by_cases h401 : status=401
  · subst status
    obtain ⟨d,td,hr,d10,d11,hbytes⟩ := ReasonBoardHttpReason401Data.contract c ram dst hp h10 h11 h12 h13 hm
    exact ⟨d,45,by decide,td,hr,d10,d11,hbytes⟩
  by_cases h403 : status=403
  · subst status
    obtain ⟨d,td,hr,d10,d11,hbytes⟩ := ReasonBoardHttpReason403Data.contract c ram dst hp h10 h11 h12 h13 hm
    exact ⟨d,40,by decide,td,hr,d10,d11,hbytes⟩
  by_cases h404 : status=404
  · subst status
    obtain ⟨d,td,hr,d10,d11,hbytes⟩ := ReasonBoardHttpReason404Data.contract c ram dst hp h10 h11 h12 h13 hm
    exact ⟨d,38,by decide,td,hr,d10,d11,hbytes⟩
  by_cases h405 : status=405
  · subst status
    obtain ⟨d,td,hr,d10,d11,hbytes⟩ := ReasonBoardHttpReason405Data.contract c ram dst hp h10 h11 h12 h13 hm
    exact ⟨d,52,by decide,td,hr,d10,d11,hbytes⟩
  by_cases h408 : status=408
  · subst status
    obtain ⟨d,td,hr,d10,d11,hbytes⟩ := ReasonBoardHttpReason408Data.contract c ram dst hp h10 h11 h12 h13 hm
    exact ⟨d,51,by decide,td,hr,d10,d11,hbytes⟩
  by_cases h409 : status=409
  · subst status
    obtain ⟨d,td,hr,d10,d11,hbytes⟩ := ReasonBoardHttpReason409Data.contract c ram dst hp h10 h11 h12 h13 hm
    exact ⟨d,37,by decide,td,hr,d10,d11,hbytes⟩
  by_cases h413 : status=413
  · subst status
    obtain ⟨d,td,hr,d10,d11,hbytes⟩ := ReasonBoardHttpReason413Data.contract c ram dst hp h10 h11 h12 h13 hm
    exact ⟨d,51,by decide,td,hr,d10,d11,hbytes⟩
  by_cases h414 : status=414
  · subst status
    obtain ⟨d,td,hr,d10,d11,hbytes⟩ := ReasonBoardHttpReason414Data.contract c ram dst hp h10 h11 h12 h13 hm
    exact ⟨d,43,by decide,td,hr,d10,d11,hbytes⟩
  by_cases h422 : status=422
  · subst status
    obtain ⟨d,td,hr,d10,d11,hbytes⟩ := ReasonBoardHttpReason422Data.contract c ram dst hp h10 h11 h12 h13 hm
    exact ⟨d,59,by decide,td,hr,d10,d11,hbytes⟩
  by_cases h431 : status=431
  · subst status
    obtain ⟨d,td,hr,d10,d11,hbytes⟩ := ReasonBoardHttpReason431Data.contract c ram dst hp h10 h11 h12 h13 hm
    exact ⟨d,178,by decide,td,hr,d10,d11,hbytes⟩
  by_cases h500 : status=500
  · subst status
    obtain ⟨d,td,hr,d10,d11,hbytes⟩ := ReasonBoardHttpReason500Data.contract c ram dst hp h10 h11 h12 h13 hm
    exact ⟨d,56,by decide,td,hr,d10,d11,hbytes⟩
  by_cases h501 : status=501
  · subst status
    obtain ⟨d,td,hr,d10,d11,hbytes⟩ := ReasonBoardHttpReason501Data.contract c ram dst hp h10 h11 h12 h13 hm
    exact ⟨d,47,by decide,td,hr,d10,d11,hbytes⟩
  by_cases h503 : status=503
  · subst status
    obtain ⟨d,td,hr,d10,d11,hbytes⟩ := ReasonBoardHttpReason503Data.contract c ram dst hp h10 h11 h12 h13 hm
    exact ⟨d,54,by decide,td,hr,d10,d11,hbytes⟩
  by_cases h505 : status=505
  · subst status
    obtain ⟨d,td,hr,d10,d11,hbytes⟩ := ReasonBoardHttpReason505Data.contract c ram dst hp h10 h11 h12 h13 hm
    exact ⟨d,68,by decide,td,hr,d10,d11,hbytes⟩
  have hranges : (100≤status ∧ status≤199) ∨ (202≤status ∧ status≤203) ∨ (205≤status ∧ status≤399) ∨ (402≤status ∧ status≤402) ∨ (406≤status ∧ status≤407) ∨ (410≤status ∧ status≤412) ∨ (415≤status ∧ status≤421) ∨ (423≤status ∧ status≤430) ∨ (432≤status ∧ status≤499) ∨ (502≤status ∧ status≤502) ∨ (504≤status ∧ status≤504) ∨ (506≤status ∧ status≤599) := by omega
  have hre : WireSpec.ascii (ResponseHeadSpec.reason status)=[] := by
    unfold ResponseHeadSpec.reason
    split <;> simp_all [WireSpec.ascii]
  have hmem : ByteWrite.write ram (dst+13#32) (WireSpec.ascii (ResponseHeadSpec.reason status))=ram := by rw [hre];rfl
  rcases hranges with g0|g1|g2|g3|g4|g5|g6|g7|g8|g9|g10|g11
  · obtain ⟨d,td,pd,d14,d15,d10,d11,dr,dc⟩ := ReasonBoardHttpReasonDefault100.contract c ram dst status g0.1 g0.2 h10 h11 h12 h13 hp
    refine ⟨d,14,by decide,?_,CopyRegs.returned pd (dr 2 (by decide) (by decide) (by decide) (by decide)) dc ?_,d10,?_,?_⟩
    · rw [hmem];exact td
    · intro r hr
      exact dr r (CopyRegs.ne_low r 14 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 15 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 10 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 11 hr (by decide) (by decide) (by decide) (by decide))
    · rw [hre];exact d11
    · rw [hre];exact Bytes.empty B ram (dst+13#32)
  · obtain ⟨d,td,pd,d14,d15,d10,d11,dr,dc⟩ := ReasonBoardHttpReasonDefault202.contract c ram dst status g1.1 g1.2 h10 h11 h12 h13 hp
    refine ⟨d,14,by decide,?_,CopyRegs.returned pd (dr 2 (by decide) (by decide) (by decide) (by decide)) dc ?_,d10,?_,?_⟩
    · rw [hmem];exact td
    · intro r hr
      exact dr r (CopyRegs.ne_low r 14 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 15 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 10 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 11 hr (by decide) (by decide) (by decide) (by decide))
    · rw [hre];exact d11
    · rw [hre];exact Bytes.empty B ram (dst+13#32)
  · obtain ⟨d,td,pd,d14,d15,d10,d11,dr,dc⟩ := ReasonBoardHttpReasonDefault205.contract c ram dst status g2.1 g2.2 h10 h11 h12 h13 hp
    refine ⟨d,14,by decide,?_,CopyRegs.returned pd (dr 2 (by decide) (by decide) (by decide) (by decide)) dc ?_,d10,?_,?_⟩
    · rw [hmem];exact td
    · intro r hr
      exact dr r (CopyRegs.ne_low r 14 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 15 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 10 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 11 hr (by decide) (by decide) (by decide) (by decide))
    · rw [hre];exact d11
    · rw [hre];exact Bytes.empty B ram (dst+13#32)
  · obtain ⟨d,td,pd,d14,d15,d10,d11,dr,dc⟩ := ReasonBoardHttpReasonDefault402.contract c ram dst status g3.1 g3.2 h10 h11 h12 h13 hp
    refine ⟨d,14,by decide,?_,CopyRegs.returned pd (dr 2 (by decide) (by decide) (by decide) (by decide)) dc ?_,d10,?_,?_⟩
    · rw [hmem];exact td
    · intro r hr
      exact dr r (CopyRegs.ne_low r 14 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 15 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 10 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 11 hr (by decide) (by decide) (by decide) (by decide))
    · rw [hre];exact d11
    · rw [hre];exact Bytes.empty B ram (dst+13#32)
  · obtain ⟨d,td,pd,d14,d15,d10,d11,dr,dc⟩ := ReasonBoardHttpReasonDefault406.contract c ram dst status g4.1 g4.2 h10 h11 h12 h13 hp
    refine ⟨d,16,by decide,?_,CopyRegs.returned pd (dr 2 (by decide) (by decide) (by decide) (by decide)) dc ?_,d10,?_,?_⟩
    · rw [hmem];exact td
    · intro r hr
      exact dr r (CopyRegs.ne_low r 14 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 15 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 10 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 11 hr (by decide) (by decide) (by decide) (by decide))
    · rw [hre];exact d11
    · rw [hre];exact Bytes.empty B ram (dst+13#32)
  · obtain ⟨d,td,pd,d14,d15,d10,d11,dr,dc⟩ := ReasonBoardHttpReasonDefault410.contract c ram dst status g5.1 g5.2 h10 h11 h12 h13 hp
    refine ⟨d,14,by decide,?_,CopyRegs.returned pd (dr 2 (by decide) (by decide) (by decide) (by decide)) dc ?_,d10,?_,?_⟩
    · rw [hmem];exact td
    · intro r hr
      exact dr r (CopyRegs.ne_low r 14 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 15 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 10 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 11 hr (by decide) (by decide) (by decide) (by decide))
    · rw [hre];exact d11
    · rw [hre];exact Bytes.empty B ram (dst+13#32)
  · obtain ⟨d,td,pd,d14,d15,d10,d11,dr,dc⟩ := ReasonBoardHttpReasonDefault415.contract c ram dst status g6.1 g6.2 h10 h11 h12 h13 hp
    refine ⟨d,14,by decide,?_,CopyRegs.returned pd (dr 2 (by decide) (by decide) (by decide) (by decide)) dc ?_,d10,?_,?_⟩
    · rw [hmem];exact td
    · intro r hr
      exact dr r (CopyRegs.ne_low r 14 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 15 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 10 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 11 hr (by decide) (by decide) (by decide) (by decide))
    · rw [hre];exact d11
    · rw [hre];exact Bytes.empty B ram (dst+13#32)
  · obtain ⟨d,td,pd,d14,d15,d10,d11,dr,dc⟩ := ReasonBoardHttpReasonDefault423.contract c ram dst status g7.1 g7.2 h10 h11 h12 h13 hp
    refine ⟨d,14,by decide,?_,CopyRegs.returned pd (dr 2 (by decide) (by decide) (by decide) (by decide)) dc ?_,d10,?_,?_⟩
    · rw [hmem];exact td
    · intro r hr
      exact dr r (CopyRegs.ne_low r 14 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 15 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 10 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 11 hr (by decide) (by decide) (by decide) (by decide))
    · rw [hre];exact d11
    · rw [hre];exact Bytes.empty B ram (dst+13#32)
  · obtain ⟨d,td,pd,d14,d15,d10,d11,dr,dc⟩ := ReasonBoardHttpReasonDefault432.contract c ram dst status g8.1 g8.2 h10 h11 h12 h13 hp
    refine ⟨d,14,by decide,?_,CopyRegs.returned pd (dr 2 (by decide) (by decide) (by decide) (by decide)) dc ?_,d10,?_,?_⟩
    · rw [hmem];exact td
    · intro r hr
      exact dr r (CopyRegs.ne_low r 14 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 15 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 10 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 11 hr (by decide) (by decide) (by decide) (by decide))
    · rw [hre];exact d11
    · rw [hre];exact Bytes.empty B ram (dst+13#32)
  · obtain ⟨d,td,pd,d14,d15,d10,d11,dr,dc⟩ := ReasonBoardHttpReasonDefault502.contract c ram dst status g9.1 g9.2 h10 h11 h12 h13 hp
    refine ⟨d,16,by decide,?_,CopyRegs.returned pd (dr 2 (by decide) (by decide) (by decide) (by decide)) dc ?_,d10,?_,?_⟩
    · rw [hmem];exact td
    · intro r hr
      exact dr r (CopyRegs.ne_low r 14 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 15 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 10 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 11 hr (by decide) (by decide) (by decide) (by decide))
    · rw [hre];exact d11
    · rw [hre];exact Bytes.empty B ram (dst+13#32)
  · obtain ⟨d,td,pd,d14,d15,d10,d11,dr,dc⟩ := ReasonBoardHttpReasonDefault504.contract c ram dst status g10.1 g10.2 h10 h11 h12 h13 hp
    refine ⟨d,16,by decide,?_,CopyRegs.returned pd (dr 2 (by decide) (by decide) (by decide) (by decide)) dc ?_,d10,?_,?_⟩
    · rw [hmem];exact td
    · intro r hr
      exact dr r (CopyRegs.ne_low r 14 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 15 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 10 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 11 hr (by decide) (by decide) (by decide) (by decide))
    · rw [hre];exact d11
    · rw [hre];exact Bytes.empty B ram (dst+13#32)
  · obtain ⟨d,td,pd,d14,d15,d10,d11,dr,dc⟩ := ReasonBoardHttpReasonDefault506.contract c ram dst status g11.1 g11.2 h10 h11 h12 h13 hp
    refine ⟨d,16,by decide,?_,CopyRegs.returned pd (dr 2 (by decide) (by decide) (by decide) (by decide)) dc ?_,d10,?_,?_⟩
    · rw [hmem];exact td
    · intro r hr
      exact dr r (CopyRegs.ne_low r 14 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 15 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 10 hr (by decide) (by decide) (by decide) (by decide))
        (CopyRegs.ne_low r 11 hr (by decide) (by decide) (by decide) (by decide))
    · rw [hre];exact d11
    · rw [hre];exact Bytes.empty B ram (dst+13#32)
end E5R.Thermostat.ReasonBoardHttpReason
