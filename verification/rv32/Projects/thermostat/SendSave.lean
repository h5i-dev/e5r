import Projects.thermostat.SendCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.SendSave
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (frame : Word) (c : Core) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (frame+140#32) (c.get 1) .w) (frame+136#32) (c.get 8) .w) (frame+132#32) (c.get 9) .w) (frame+128#32) (c.get 18) .w) (frame+124#32) (c.get 19) .w) (frame+120#32) (c.get 20) .w) (frame+116#32) (c.get 21) .w) (frame+112#32) (c.get 22) .w) (frame+108#32) (c.get 23) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (frame : Word) (h2 : c.get 2=frame+144#32) (hm : Memory.Block B frame 144) (ha : frame.toNat%4=0)
    (hp : c.pc=0x8000030e#32) :
    ∃ d, Quiet.Steps B img 10 ⟨c,ram⟩ ⟨d,memory ram frame c⟩ ∧ d.pc=0x80000322#32 ∧
      d.get 2=frame+96#32 ∧ (∀ r : Reg, r≠2 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 2 (frame+96#32) 0x80000310#32
  let r1 := ramWrite ram (frame+140#32) (c.get 1) .w
  let c2 := c1.goto 0x80000312#32
  let r2 := ramWrite r1 (frame+136#32) (c.get 8) .w
  let c3 := c2.goto 0x80000314#32
  let r3 := ramWrite r2 (frame+132#32) (c.get 9) .w
  let c4 := c3.goto 0x80000316#32
  let r4 := ramWrite r3 (frame+128#32) (c.get 18) .w
  let c5 := c4.goto 0x80000318#32
  let r5 := ramWrite r4 (frame+124#32) (c.get 19) .w
  let c6 := c5.goto 0x8000031a#32
  let r6 := ramWrite r5 (frame+120#32) (c.get 20) .w
  let c7 := c6.goto 0x8000031c#32
  let r7 := ramWrite r6 (frame+116#32) (c.get 21) .w
  let c8 := c7.goto 0x8000031e#32
  let r8 := ramWrite r7 (frame+112#32) (c.get 22) .w
  let c9 := c8.goto 0x80000320#32
  let r9 := ramWrite r8 (frame+108#32) (c.get 23) .w
  let c10 := c9.goto 0x80000322#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact se2147484430) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,h2]
    change Observed.interp B img o (.done (c.wr 2 ((frame+144#32)+0xffffffd0#32) (c.pc+2#32))) ram 0 [] [] = _
    rw [BitVec.add_assoc,show 144#32+0xffffffd0#32=96#32 by decide +kernel,hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine Quiet.step_of (by change (0x80000310#32).getLsbD 0=false;decide) se2147484432 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 r1 [],[]⟩
    have v2 : c1.get 2=frame+96#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2]
    have v1 : c1.get 1=c.get 1 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_store,v2,v1,BitVec.add_assoc,show 96#32+44#32=140#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 35 ha) (Memory.block_access hm (off := 140) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,r2⟩ := by
    refine Quiet.step_of (by change (0x80000312#32).getLsbD 0=false;decide) se2147484434 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) r1 0 [] [] = ⟨.ok c3 r2 [],[]⟩
    have v2 : c2.get 2=frame+96#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have v8 : c2.get 8=c.get 8 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_store,v2,v8,BitVec.add_assoc,show 96#32+40#32=136#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 34 ha) (Memory.block_access hm (off := 136) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r2⟩ ⟨c4,r3⟩ := by
    refine Quiet.step_of (by change (0x80000314#32).getLsbD 0=false;decide) se2147484436 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r2 0 [] [] = ⟨.ok c4 r3 [],[]⟩
    have v2 : c3.get 2=frame+96#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have v9 : c3.get 9=c.get 9 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_store,v2,v9,BitVec.add_assoc,show 96#32+36#32=132#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 33 ha) (Memory.block_access hm (off := 132) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r3⟩ ⟨c5,r4⟩ := by
    refine Quiet.step_of (by change (0x80000316#32).getLsbD 0=false;decide) se2147484438 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r3 0 [] [] = ⟨.ok c5 r4 [],[]⟩
    have v2 : c4.get 2=frame+96#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have v18 : c4.get 18=c.get 18 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_store,v2,v18,BitVec.add_assoc,show 96#32+32#32=128#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 32 ha) (Memory.block_access hm (off := 128) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r4⟩ ⟨c6,r5⟩ := by
    refine Quiet.step_of (by change (0x80000318#32).getLsbD 0=false;decide) se2147484440 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r4 0 [] [] = ⟨.ok c6 r5 [],[]⟩
    have v2 : c5.get 2=frame+96#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have v19 : c5.get 19=c.get 19 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_store,v2,v19,BitVec.add_assoc,show 96#32+28#32=124#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 31 ha) (Memory.block_access hm (off := 124) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r5⟩ ⟨c7,r6⟩ := by
    refine Quiet.step_of (by change (0x8000031a#32).getLsbD 0=false;decide) se2147484442 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r5 0 [] [] = ⟨.ok c7 r6 [],[]⟩
    have v2 : c6.get 2=frame+96#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have v20 : c6.get 20=c.get 20 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_store,v2,v20,BitVec.add_assoc,show 96#32+24#32=120#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 30 ha) (Memory.block_access hm (off := 120) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,r6⟩ ⟨c8,r7⟩ := by
    refine Quiet.step_of (by change (0x8000031c#32).getLsbD 0=false;decide) se2147484444 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r6 0 [] [] = ⟨.ok c8 r7 [],[]⟩
    have v2 : c7.get 2=frame+96#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have v21 : c7.get 21=c.get 21 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_store,v2,v21,BitVec.add_assoc,show 96#32+20#32=116#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 29 ha) (Memory.block_access hm (off := 116) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,r7⟩ ⟨c9,r8⟩ := by
    refine Quiet.step_of (by change (0x8000031e#32).getLsbD 0=false;decide) se2147484446 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r7 0 [] [] = ⟨.ok c9 r8 [],[]⟩
    have v2 : c8.get 2=frame+96#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have v22 : c8.get 22=c.get 22 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_store,v2,v22,BitVec.add_assoc,show 96#32+16#32=112#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 28 ha) (Memory.block_access hm (off := 112) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,r8⟩ ⟨c10,r9⟩ := by
    refine Quiet.step_of (by change (0x80000320#32).getLsbD 0=false;decide) se2147484448 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) r8 0 [] [] = ⟨.ok c10 r9 [],[]⟩
    have v2 : c9.get 2=frame+96#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have v23 : c9.get 23=c.get 23 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_store,v2,v23,BitVec.add_assoc,show 96#32+12#32=108#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 27 ha) (Memory.block_access hm (off := 108) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c10,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.single t9))))))))),rfl,?_ ,?_ ,by rfl⟩
  · simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · intro reg h2;simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h2]
end E5R.Thermostat.SendSave
