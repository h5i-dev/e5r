import Projects.thermostat.ResponseHeadCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ResponseHeadSave
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (frame : Word) (c : Core) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (frame+92#32) (c.get 1) .w) (frame+88#32) (c.get 8) .w) (frame+84#32) (c.get 9) .w) (frame+80#32) (c.get 18) .w) (frame+76#32) (c.get 19) .w) (frame+72#32) (c.get 20) .w) (frame+68#32) (c.get 21) .w) (frame+64#32) (c.get 22) .w) (frame+60#32) (c.get 23) .w) (frame+56#32) (c.get 24) .w) (frame+52#32) (c.get 25) .w) (frame+48#32) (c.get 26) .w) (frame+44#32) (c.get 27) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (frame : Word) (h2 : c.get 2=frame+96#32) (hm : Memory.Block B frame 96) (ha : frame.toNat%4=0)
    (hp : c.pc=0x80003e66#32) :
    ∃ d, Quiet.Steps B img 14 ⟨c,ram⟩ ⟨d,memory ram frame c⟩ ∧ d.pc=0x80003e82#32 ∧
      d.get 2=frame+16#32 ∧ (∀ r : Reg, r≠2 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 2 (frame+16#32) 0x80003e68#32
  let r1 := ramWrite ram (frame+92#32) (c.get 1) .w
  let c2 := c1.goto 0x80003e6a#32
  let r2 := ramWrite r1 (frame+88#32) (c.get 8) .w
  let c3 := c2.goto 0x80003e6c#32
  let r3 := ramWrite r2 (frame+84#32) (c.get 9) .w
  let c4 := c3.goto 0x80003e6e#32
  let r4 := ramWrite r3 (frame+80#32) (c.get 18) .w
  let c5 := c4.goto 0x80003e70#32
  let r5 := ramWrite r4 (frame+76#32) (c.get 19) .w
  let c6 := c5.goto 0x80003e72#32
  let r6 := ramWrite r5 (frame+72#32) (c.get 20) .w
  let c7 := c6.goto 0x80003e74#32
  let r7 := ramWrite r6 (frame+68#32) (c.get 21) .w
  let c8 := c7.goto 0x80003e76#32
  let r8 := ramWrite r7 (frame+64#32) (c.get 22) .w
  let c9 := c8.goto 0x80003e78#32
  let r9 := ramWrite r8 (frame+60#32) (c.get 23) .w
  let c10 := c9.goto 0x80003e7a#32
  let r10 := ramWrite r9 (frame+56#32) (c.get 24) .w
  let c11 := c10.goto 0x80003e7c#32
  let r11 := ramWrite r10 (frame+52#32) (c.get 25) .w
  let c12 := c11.goto 0x80003e7e#32
  let r12 := ramWrite r11 (frame+48#32) (c.get 26) .w
  let c13 := c12.goto 0x80003e80#32
  let r13 := ramWrite r12 (frame+44#32) (c.get 27) .w
  let c14 := c13.goto 0x80003e82#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rh2147499622) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,h2]
    change Observed.interp B img o (.done (c.wr 2 ((frame+96#32)+0xffffffb0#32) (c.pc+2#32))) ram 0 [] [] = _
    rw [BitVec.add_assoc,show 96#32+0xffffffb0#32=16#32 by decide +kernel,hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine Quiet.step_of (by change (0x80003e68#32).getLsbD 0=false;decide) rh2147499624 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 r1 [],[]⟩
    have v2 : c1.get 2=frame+16#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2]
    have vr : c1.get 1=c.get 1 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_store,v2,vr,BitVec.add_assoc,show 16#32+76#32=92#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 23 ha)
        (Memory.block_access hm (off := 92) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,r2⟩ := by
    refine Quiet.step_of (by change (0x80003e6a#32).getLsbD 0=false;decide) rh2147499626 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) r1 0 [] [] = ⟨.ok c3 r2 [],[]⟩
    have v2 : c2.get 2=frame+16#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have vr : c2.get 8=c.get 8 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_store,v2,vr,BitVec.add_assoc,show 16#32+72#32=88#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 22 ha)
        (Memory.block_access hm (off := 88) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r2⟩ ⟨c4,r3⟩ := by
    refine Quiet.step_of (by change (0x80003e6c#32).getLsbD 0=false;decide) rh2147499628 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r2 0 [] [] = ⟨.ok c4 r3 [],[]⟩
    have v2 : c3.get 2=frame+16#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have vr : c3.get 9=c.get 9 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_store,v2,vr,BitVec.add_assoc,show 16#32+68#32=84#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 21 ha)
        (Memory.block_access hm (off := 84) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r3⟩ ⟨c5,r4⟩ := by
    refine Quiet.step_of (by change (0x80003e6e#32).getLsbD 0=false;decide) rh2147499630 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r3 0 [] [] = ⟨.ok c5 r4 [],[]⟩
    have v2 : c4.get 2=frame+16#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have vr : c4.get 18=c.get 18 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_store,v2,vr,BitVec.add_assoc,show 16#32+64#32=80#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 20 ha)
        (Memory.block_access hm (off := 80) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r4⟩ ⟨c6,r5⟩ := by
    refine Quiet.step_of (by change (0x80003e70#32).getLsbD 0=false;decide) rh2147499632 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r4 0 [] [] = ⟨.ok c6 r5 [],[]⟩
    have v2 : c5.get 2=frame+16#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have vr : c5.get 19=c.get 19 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_store,v2,vr,BitVec.add_assoc,show 16#32+60#32=76#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 19 ha)
        (Memory.block_access hm (off := 76) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r5⟩ ⟨c7,r6⟩ := by
    refine Quiet.step_of (by change (0x80003e72#32).getLsbD 0=false;decide) rh2147499634 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r5 0 [] [] = ⟨.ok c7 r6 [],[]⟩
    have v2 : c6.get 2=frame+16#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have vr : c6.get 20=c.get 20 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_store,v2,vr,BitVec.add_assoc,show 16#32+56#32=72#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 18 ha)
        (Memory.block_access hm (off := 72) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,r6⟩ ⟨c8,r7⟩ := by
    refine Quiet.step_of (by change (0x80003e74#32).getLsbD 0=false;decide) rh2147499636 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r6 0 [] [] = ⟨.ok c8 r7 [],[]⟩
    have v2 : c7.get 2=frame+16#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have vr : c7.get 21=c.get 21 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_store,v2,vr,BitVec.add_assoc,show 16#32+52#32=68#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 17 ha)
        (Memory.block_access hm (off := 68) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,r7⟩ ⟨c9,r8⟩ := by
    refine Quiet.step_of (by change (0x80003e76#32).getLsbD 0=false;decide) rh2147499638 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r7 0 [] [] = ⟨.ok c9 r8 [],[]⟩
    have v2 : c8.get 2=frame+16#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have vr : c8.get 22=c.get 22 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_store,v2,vr,BitVec.add_assoc,show 16#32+48#32=64#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 16 ha)
        (Memory.block_access hm (off := 64) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,r8⟩ ⟨c10,r9⟩ := by
    refine Quiet.step_of (by change (0x80003e78#32).getLsbD 0=false;decide) rh2147499640 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) r8 0 [] [] = ⟨.ok c10 r9 [],[]⟩
    have v2 : c9.get 2=frame+16#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have vr : c9.get 23=c.get 23 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_store,v2,vr,BitVec.add_assoc,show 16#32+44#32=60#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 15 ha)
        (Memory.block_access hm (off := 60) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,r9⟩ ⟨c11,r10⟩ := by
    refine Quiet.step_of (by change (0x80003e7a#32).getLsbD 0=false;decide) rh2147499642 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) r9 0 [] [] = ⟨.ok c11 r10 [],[]⟩
    have v2 : c10.get 2=frame+16#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have vr : c10.get 24=c.get 24 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_store,v2,vr,BitVec.add_assoc,show 16#32+40#32=56#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 14 ha)
        (Memory.block_access hm (off := 56) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,r10⟩ ⟨c12,r11⟩ := by
    refine Quiet.step_of (by change (0x80003e7c#32).getLsbD 0=false;decide) rh2147499644 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) r10 0 [] [] = ⟨.ok c12 r11 [],[]⟩
    have v2 : c11.get 2=frame+16#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have vr : c11.get 25=c.get 25 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_store,v2,vr,BitVec.add_assoc,show 16#32+36#32=52#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 13 ha)
        (Memory.block_access hm (off := 52) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,r11⟩ ⟨c13,r12⟩ := by
    refine Quiet.step_of (by change (0x80003e7e#32).getLsbD 0=false;decide) rh2147499646 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) r11 0 [] [] = ⟨.ok c13 r12 [],[]⟩
    have v2 : c12.get 2=frame+16#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have vr : c12.get 26=c.get 26 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_store,v2,vr,BitVec.add_assoc,show 16#32+32#32=48#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 12 ha)
        (Memory.block_access hm (off := 48) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,r12⟩ ⟨c14,r13⟩ := by
    refine Quiet.step_of (by change (0x80003e80#32).getLsbD 0=false;decide) rh2147499648 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) r12 0 [] [] = ⟨.ok c14 r13 [],[]⟩
    have v2 : c13.get 2=frame+16#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have vr : c13.get 27=c.get 27 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_store,v2,vr,BitVec.add_assoc,show 16#32+28#32=44#32 by decide +kernel,
      Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 11 ha)
        (Memory.block_access hm (off := 44) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c14,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.single t13))))))))))))),rfl,?_ ,?_ ,by rfl⟩
  · simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · intro reg h2;simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h2]
end E5R.Thermostat.ResponseHeadSave
