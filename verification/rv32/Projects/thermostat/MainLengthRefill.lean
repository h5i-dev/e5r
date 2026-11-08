import Projects.thermostat.MainLengthWait
import Projects.thermostat.MainLengthTailMemory
import Projects.thermostat.MainLengthMoreBranch
import Projects.thermostat.WordZero
import Projects.thermostat.HeadTargetMath
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.MainLengthRefill
open E5R E5R.Thermostat
abbrev B := UartPlatform.board
abbrev rx := 0x80ffec14#32
abbrev fp := 0x80fff814#32

theorem contract (c : Core) (ram : Word → BitVec 8) (filled total : Nat) (pending : List Word) (ready datum : Word)
    (hp : c.pc=0x80000c6c#32) (h8 : c.get 8=fp) (h19 : c.get 19=0x10000000#32) (h22 : c.get 22=1#32)
    (h12 : c.get 12=rx+BitVec.ofNat 32 filled) (layout : MainHeaderLayout.At ram filled) (room : filled<2048) (totalBound : total≤2048) (h452 : ramRead ram (fp+452#32) .w=BitVec.ofNat 32 total)
    (stack : Memory.Block B 0x80ff0000#32 65536)
    (notReady : ∀ status ∈ pending, UartPoll.byte status &&& 1#32=0#32) (isReady : UartPoll.byte ready &&& 1#32≠0#32) :
    ∃ d after, Observed.Steps B img (14+4*pending.length) ⟨c,ram⟩ ⟨d,after⟩ (MainLengthWait.reads pending ready datum) [] ∧
      d.pc=(if decide (filled+1<total) then 0x80000c3a#32 else 0x80000c98#32) ∧ d.get 10=BitVec.ofNat 32 (filled+1) ∧ d.get 25=BitVec.ofNat 32 total ∧ MainHeaderLayout.At after (filled+1) ∧
      after (rx+BitVec.ofNat 32 filled)=(UartPoll.byte datum).setWidth 8 ∧
      (∀ x, x≠rx+BitVec.ofNat 32 filled → (∀ i : Fin 4, x≠(fp+84#32)+BitVec.ofNat 32 i.val) → x≠fp+468#32 → after x=ram x) ∧
      (∀ r : Reg, r≠10 → r≠11 → r≠25 → d.get r=c.get r) ∧ d.sameCsr c := by
  have rxBlock : Memory.Block B rx 2048 := by
    have block := Memory.sub_block (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60436) (m := 2048) stack (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60436#32=rx by decide +kernel] using block
  have object : Memory.Block B fp 469 := by
    have block := Memory.sub_block (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 63508) (m := 469) stack (by decide) (by decide)
    simpa only [show 0x80ff0000#32+63508#32=fp by decide +kernel] using block
  have destination : B.inRam (c.get 12) 1=true := by rw [h12];exact Memory.block_access rxBlock (off := filled) (by decide) (by omega)
  obtain ⟨a,mid,ta,apc,a12,a19,ac,value,byteFrame,ar⟩ := MainLengthWait.contract c ram pending ready datum hp h19 notReady isReady destination
  have futureFrame : ViewFrame.Region ram mid fp 456 := by
    intro i;apply byteFrame
    rw [h12]
    exact Ne.symm (WordZero.separated rx fp 2048 456 (by decide +kernel) (by decide +kernel) ⟨filled,room⟩ i)
  have midLayout := MainHeaderLayout.preserve layout (fun i => futureFrame ⟨i.val,by have := i.isLt;omega⟩)
  obtain ⟨b,tb,bpc,b10,b11,b25,br,bc⟩ := MainLengthTail.contract B a mid fp (BitVec.ofNat 32 filled) (BitVec.ofNat 32 total)
    ((ar 8 (by decide)).trans h8) ((ar 22 (by decide)).trans h22) midLayout.filledPtr midLayout.filled ((ViewFrame.word futureFrame 452 (by decide)).trans h452) object (by decide +kernel) apc
  have test : taken .ltu (BitVec.ofNat 32 filled+1#32) (BitVec.ofNat 32 total)=decide (filled+1<total) := by
    rw [←BitVec.ofNat_add]
    simp only [taken,BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show filled+1<2^32 by omega),Nat.mod_eq_of_lt (show total<2^32 by omega)]
  obtain ⟨d,td,dpc,dr,dc⟩ := MainLengthMoreBranch.contract B b _ _ _ (decide (filled+1<total)) bpc b10 b25 test
  have valueAfter : MainLengthTail.memory mid fp (BitVec.ofNat 32 filled) (rx+BitVec.ofNat 32 filled)=(UartPoll.byte datum).setWidth 8 := by
    rw [MainLengthTailMemory.frame mid fp _ _ (fun i => WordZero.separated rx (fp+84#32) 2048 4 (by decide +kernel) (by decide +kernel) ⟨filled,room⟩ i)
      (by simpa only [BitVec.add_zero] using WordZero.separated rx (fp+468#32) 2048 1 (by decide +kernel) (by decide +kernel) ⟨filled,room⟩ ⟨0,by decide⟩)]
    simpa only [h12,MainLengthUart.byte,UartPoll.byte] using value
  refine ⟨d,_,?_,dpc,?_,(dr 25).trans b25,MainLengthTailMemory.layout midLayout room,valueAfter,?_,?_,(dc.trans bc).trans ac⟩
  · have trace := (ta.trans tb.observed).trans td.observed
    have count : (4*pending.length+5)+8+1=14+4*pending.length := by omega
    simpa only [count,List.append_nil] using trace
  · exact (dr 10).trans (b10.trans (by rw [←BitVec.ofNat_add]))
  · intro x byte count poll
    rw [MainLengthTailMemory.frame mid fp _ x count poll]
    exact byteFrame x (by simpa only [h12] using byte)
  · intro r h10 h11 h25
    exact (dr r).trans ((br r h10 h11 h25).trans (ar r h10))
end E5R.Thermostat.MainLengthRefill
