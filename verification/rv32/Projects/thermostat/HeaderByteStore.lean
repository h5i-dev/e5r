import Projects.thermostat.HeaderReparse
import Projects.thermostat.MainHeaderRefill
set_option autoImplicit false
namespace E5R.Thermostat.HeaderByteStore
open E5R E5R.Thermostat
abbrev B := UartPlatform.board
abbrev rx := 0x80ffec14#32
abbrev fp := 0x80fff814#32

/-- Real post-RBR byte store and filled/poll stores up to parser entry.
    All instructions are quiet for every oracle; the byte need not be valid. -/
theorem contract (c : Core) (ram : Word → BitVec 8) (filled : Nat)
    (hp : c.pc=0x80000bae#32) (h8 : c.get 8=fp) (h19 : c.get 19=0x10000000#32) (h22 : c.get 22=1#32)
    (h12 : c.get 12=rx+BitVec.ofNat 32 filled) (layout : MainHeaderLayout.At ram filled) (room : filled<2048)
    (stack : Memory.Block B 0x80ff0000#32 65536) :
    ∃ d after, Quiet.Steps B img 10 ⟨c,ram⟩ ⟨d,after⟩ ∧
      d.pc=0x80000a10#32 ∧ d.get 12=BitVec.ofNat 32 (filled+1) ∧ MainHeaderLayout.At after (filled+1) ∧
      after (rx+BitVec.ofNat 32 filled)=(c.get 10).setWidth 8 ∧
      (∀ x, x≠rx+BitVec.ofNat 32 filled → (∀ i : Fin 4, x≠(fp+84#32)+BitVec.ofNat 32 i.val) → x≠fp+464#32 → after x=ram x) ∧
      (∀ r : Reg, r≠10 → r≠11 → r≠14 → r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  have rxBlock : Memory.Block B rx 2048 := by
    have block := Memory.sub_block (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60436) (m := 2048) stack (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60436#32=rx by decide +kernel] using block
  have object : Memory.Block B fp 465 := by
    have block := Memory.sub_block (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 63508) (m := 465) stack (by decide) (by decide)
    simpa only [show 0x80ff0000#32+63508#32=fp by decide +kernel] using block
  have destination : B.inRam (c.get 12) 1=true := by rw [h12];exact Memory.block_access rxBlock (off := filled) (by decide) (by omega)
  let a := c.goto 0x80000bb2#32
  let mid := ramWrite ram (c.get 12) (c.get 10) .b
  have ta : Quiet.Steps B img 1 ⟨c,ram⟩ ⟨a,mid⟩ := Quiet.Steps.single (by
    intro o
    rw [Observed.stepInstr_of (by rw [hp];decide) (by rw [hp];exact up2147486638),exec_store,BitVec.add_zero]
    rw [Quiet.interp_store_ram o (w := .b) (a := c.get 12) (by simp only [Width.bytes,Nat.mod_one]) destination]
    simp only [hp,show 0x80000bae#32+4#32=0x80000bb2#32 by decide +kernel]
    rfl)
  have apc : a.pc=0x80000bb2#32 := rfl
  have value : mid (c.get 12)=(c.get 10).setWidth 8 := by
    change ramPut ram (c.get 12) (byteOf (c.get 10) 0) (c.get 12)=_
    simp only [ramPut,ite_true,UartPoll.byteOf_zero]
  have byteFrame (x : Word) (different : x≠c.get 12) : mid x=ram x := ramPut_ne _ different
  have ar (r : Reg) : a.get r=c.get r := rfl
  have ac : a.sameCsr c := rfl
  have futureFrame : ViewFrame.Region ram mid fp 449 := by
    intro i;apply byteFrame
    rw [h12]
    exact Ne.symm (WordZero.separated rx fp 2048 449 (by decide +kernel) (by decide +kernel) ⟨filled,room⟩ i)
  have midLayout := MainHeaderLayout.preserve layout futureFrame
  obtain ⟨b,tb,bpc,b10,b11,b14,b12,br,bc⟩ := MainHeaderTail.contract B a mid fp (BitVec.ofNat 32 filled)
    ((ar 8).trans h8) ((ar 22).trans h22) midLayout.filledPtr midLayout.filled midLayout.capacity object (by decide +kernel) apc
  have test : taken .geu 2048#32 (BitVec.ofNat 32 filled+1#32)=true := by
    rw [←BitVec.ofNat_add]
    have h := HeadTargetMath.geu 2048 (filled+1) (by decide) (by omega)
    simpa only [show decide (filled+1≤2048)=true from decide_eq_true (by omega)] using h
  obtain ⟨d,td,dpc,dr,dc⟩ := MainHeaderCapacityBranch.contract B b _ 2048#32 _ true bpc b14 b12 test
  have valueAfter : MainHeaderTail.memory mid fp (BitVec.ofNat 32 filled) (rx+BitVec.ofNat 32 filled)=(c.get 10).setWidth 8 := by
    rw [MainHeaderTailMemory.frame mid fp _ _ (fun i => WordZero.separated rx (fp+84#32) 2048 4 (by decide +kernel) (by decide +kernel) ⟨filled,room⟩ i)
      (by simpa only [BitVec.add_zero] using WordZero.separated rx (fp+464#32) 2048 1 (by decide +kernel) (by decide +kernel) ⟨filled,room⟩ ⟨0,by decide⟩)]
    simpa only [h12] using value
  refine ⟨d,_,?_,by simpa only [ite_true] using dpc,?_,MainHeaderTailMemory.layout midLayout room,valueAfter,?_,?_,(dc.trans bc).trans ac⟩
  · have trace := (ta.trans tb).trans td
    have count : 1+8+1=10 := rfl
    simpa only [count,List.append_nil] using trace
  · exact (dr 12).trans (b12.trans (by rw [←BitVec.ofNat_add]))
  · intro x byte count poll
    rw [MainHeaderTailMemory.frame mid fp _ x count poll]
    exact byteFrame x (by simpa only [h12] using byte)
  · intro r h10 h11 h14 h12
    exact (dr r).trans ((br r h10 h11 h14 h12).trans (ar r))
end E5R.Thermostat.HeaderByteStore
