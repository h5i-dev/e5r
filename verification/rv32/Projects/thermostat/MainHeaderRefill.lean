import Projects.thermostat.MainHeaderWait
import Projects.thermostat.MainHeaderTailMemory
import Projects.thermostat.MainHeaderCapacityBranch
import Projects.thermostat.WordZero
import Projects.thermostat.HeadTargetMath
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.MainHeaderRefill
open E5R E5R.Thermostat
abbrev B := UartPlatform.board
abbrev rx := 0x80ffec14#32
abbrev fp := 0x80fff814#32

theorem contract (c : Core) (ram : Word → BitVec 8) (filled : Nat) (pending : List Word) (ready datum : Word)
    (hp : c.pc=0x80000ba2#32) (h8 : c.get 8=fp) (h19 : c.get 19=0x10000000#32) (h22 : c.get 22=1#32)
    (h12 : c.get 12=rx+BitVec.ofNat 32 filled) (layout : MainHeaderLayout.At ram filled) (room : filled<2048)
    (stack : Memory.Block B 0x80ff0000#32 65536)
    (notReady : ∀ status ∈ pending, UartPoll.byte status &&& 1#32=0#32) (isReady : UartPoll.byte ready &&& 1#32≠0#32) :
    ∃ d after, Observed.Steps B img (14+4*pending.length) ⟨c,ram⟩ ⟨d,after⟩ (MainHeaderWait.reads pending ready datum) [] ∧
      d.pc=0x80000a10#32 ∧ d.get 12=BitVec.ofNat 32 (filled+1) ∧ MainHeaderLayout.At after (filled+1) ∧
      after (rx+BitVec.ofNat 32 filled)=(UartPoll.byte datum).setWidth 8 ∧
      (∀ x, x≠rx+BitVec.ofNat 32 filled → (∀ i : Fin 4, x≠(fp+84#32)+BitVec.ofNat 32 i.val) → x≠fp+464#32 → after x=ram x) ∧
      (∀ r : Reg, r≠10 → r≠11 → r≠14 → r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  have rxBlock : Memory.Block B rx 2048 := by
    have block := Memory.sub_block (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60436) (m := 2048) stack (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60436#32=rx by decide +kernel] using block
  have object : Memory.Block B fp 465 := by
    have block := Memory.sub_block (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 63508) (m := 465) stack (by decide) (by decide)
    simpa only [show 0x80ff0000#32+63508#32=fp by decide +kernel] using block
  have destination : B.inRam (c.get 12) 1=true := by rw [h12];exact Memory.block_access rxBlock (off := filled) (by decide) (by omega)
  obtain ⟨a,mid,ta,apc,a12,a19,ac,value,byteFrame,ar⟩ := MainHeaderWait.contract c ram pending ready datum hp h19 notReady isReady destination
  have futureFrame : ViewFrame.Region ram mid fp 449 := by
    intro i;apply byteFrame
    rw [h12]
    exact Ne.symm (WordZero.separated rx fp 2048 449 (by decide +kernel) (by decide +kernel) ⟨filled,room⟩ i)
  have midLayout := MainHeaderLayout.preserve layout futureFrame
  obtain ⟨b,tb,bpc,b10,b11,b14,b12,br,bc⟩ := MainHeaderTail.contract B a mid fp (BitVec.ofNat 32 filled)
    ((ar 8 (by decide)).trans h8) ((ar 22 (by decide)).trans h22) midLayout.filledPtr midLayout.filled midLayout.capacity object (by decide +kernel) apc
  have test : taken .geu 2048#32 (BitVec.ofNat 32 filled+1#32)=true := by
    rw [←BitVec.ofNat_add]
    have h := HeadTargetMath.geu 2048 (filled+1) (by decide) (by omega)
    simpa only [show decide (filled+1≤2048)=true from decide_eq_true (by omega)] using h
  obtain ⟨d,td,dpc,dr,dc⟩ := MainHeaderCapacityBranch.contract B b _ 2048#32 _ true bpc b14 b12 test
  have valueAfter : MainHeaderTail.memory mid fp (BitVec.ofNat 32 filled) (rx+BitVec.ofNat 32 filled)=(UartPoll.byte datum).setWidth 8 := by
    rw [MainHeaderTailMemory.frame mid fp _ _ (fun i => WordZero.separated rx (fp+84#32) 2048 4 (by decide +kernel) (by decide +kernel) ⟨filled,room⟩ i)
      (by simpa only [BitVec.add_zero] using WordZero.separated rx (fp+464#32) 2048 1 (by decide +kernel) (by decide +kernel) ⟨filled,room⟩ ⟨0,by decide⟩)]
    simpa only [h12] using value
  refine ⟨d,_,?_,by simpa only [ite_true] using dpc,?_,MainHeaderTailMemory.layout midLayout room,valueAfter,?_,?_,(dc.trans bc).trans ac⟩
  · have trace := (ta.trans tb.observed).trans td.observed
    have count : (4*pending.length+5)+8+1=14+4*pending.length := by omega
    simpa only [count,List.append_nil] using trace
  · exact (dr 12).trans (b12.trans (by rw [←BitVec.ofNat_add]))
  · intro x byte count poll
    rw [MainHeaderTailMemory.frame mid fp _ x count poll]
    exact byteFrame x (by simpa only [h12] using byte)
  · intro r h10 h11 h14 h12
    exact (dr r).trans ((br r h10 h11 h14 h12).trans (ar r h10))
end E5R.Thermostat.MainHeaderRefill
