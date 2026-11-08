import Projects.thermostat.SendCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.SendRestore
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (frame : Word) (h2 : c.get 2=frame+96#32) (hm : Memory.Block B frame 144) (ha : frame.toNat%4=0)
    (hp : c.pc=0x8000046e#32) :
    ∃ d, Quiet.Steps B img 11 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=((ramRead ram (frame+140#32) .w) &&& ~~~1) ∧
      d.get 1=ramRead ram (frame+140#32) .w ∧ d.get 8=ramRead ram (frame+136#32) .w ∧ d.get 9=ramRead ram (frame+132#32) .w ∧ d.get 18=ramRead ram (frame+128#32) .w ∧ d.get 19=ramRead ram (frame+124#32) .w ∧ d.get 20=ramRead ram (frame+120#32) .w ∧ d.get 21=ramRead ram (frame+116#32) .w ∧ d.get 22=ramRead ram (frame+112#32) .w ∧ d.get 23=ramRead ram (frame+108#32) .w ∧ d.get 2=frame+144#32 ∧ (∀ r : Reg, r≠1 → r≠8 → r≠9 → r≠18 → r≠19 → r≠20 → r≠21 → r≠22 → r≠23 → r≠2 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 1 (ramRead ram (frame+140#32) .w) 0x80000470#32
  let c2 := c1.wr 8 (ramRead ram (frame+136#32) .w) 0x80000472#32
  let c3 := c2.wr 9 (ramRead ram (frame+132#32) .w) 0x80000474#32
  let c4 := c3.wr 18 (ramRead ram (frame+128#32) .w) 0x80000476#32
  let c5 := c4.wr 19 (ramRead ram (frame+124#32) .w) 0x80000478#32
  let c6 := c5.wr 20 (ramRead ram (frame+120#32) .w) 0x8000047a#32
  let c7 := c6.wr 21 (ramRead ram (frame+116#32) .w) 0x8000047c#32
  let c8 := c7.wr 22 (ramRead ram (frame+112#32) .w) 0x8000047e#32
  let c9 := c8.wr 23 (ramRead ram (frame+108#32) .w) 0x80000480#32
  let c10 := c9.wr 2 (frame+144#32) 0x80000482#32
  let c11 := c10.goto ((ramRead ram (frame+140#32) .w) &&& ~~~1)
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact se2147484782) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v2 : c.get 2=frame+96#32 := by simp [Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_load,v2,BitVec.add_assoc,show 96#32+44#32=140#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 35 ha) (Memory.block_access hm (off := 140) (by decide) (by decide))];first | rfl | (rw [hp]; rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000470#32).getLsbD 0=false;decide) se2147484784 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v2 : c1.get 2=frame+96#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_load,v2,BitVec.add_assoc,show 96#32+40#32=136#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 34 ha) (Memory.block_access hm (off := 136) (by decide) (by decide))];first | rfl | (rw [hp]; rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80000472#32).getLsbD 0=false;decide) se2147484786 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v2 : c2.get 2=frame+96#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_load,v2,BitVec.add_assoc,show 96#32+36#32=132#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 33 ha) (Memory.block_access hm (off := 132) (by decide) (by decide))];first | rfl | (rw [hp]; rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80000474#32).getLsbD 0=false;decide) se2147484788 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v2 : c3.get 2=frame+96#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_load,v2,BitVec.add_assoc,show 96#32+32#32=128#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 32 ha) (Memory.block_access hm (off := 128) (by decide) (by decide))];first | rfl | (rw [hp]; rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80000476#32).getLsbD 0=false;decide) se2147484790 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v2 : c4.get 2=frame+96#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_load,v2,BitVec.add_assoc,show 96#32+28#32=124#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 31 ha) (Memory.block_access hm (off := 124) (by decide) (by decide))];first | rfl | (rw [hp]; rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80000478#32).getLsbD 0=false;decide) se2147484792 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v2 : c5.get 2=frame+96#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_load,v2,BitVec.add_assoc,show 96#32+24#32=120#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 30 ha) (Memory.block_access hm (off := 120) (by decide) (by decide))];first | rfl | (rw [hp]; rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x8000047a#32).getLsbD 0=false;decide) se2147484794 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v2 : c6.get 2=frame+96#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_load,v2,BitVec.add_assoc,show 96#32+20#32=116#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 29 ha) (Memory.block_access hm (off := 116) (by decide) (by decide))];first | rfl | (rw [hp]; rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x8000047c#32).getLsbD 0=false;decide) se2147484796 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v2 : c7.get 2=frame+96#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_load,v2,BitVec.add_assoc,show 96#32+16#32=112#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 28 ha) (Memory.block_access hm (off := 112) (by decide) (by decide))];first | rfl | (rw [hp]; rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x8000047e#32).getLsbD 0=false;decide) se2147484798 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have v2 : c8.get 2=frame+96#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_load,v2,BitVec.add_assoc,show 96#32+12#32=108#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 27 ha) (Memory.block_access hm (off := 108) (by decide) (by decide))];first | rfl | (rw [hp]; rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x80000480#32).getLsbD 0=false;decide) se2147484800 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v2 : c9.get 2=frame+96#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_opimm,v2]
    change Observed.interp B img o (.done (c9.wr 2 ((frame+96#32)+48#32) 0x80000482#32)) ram 0 [] [] = _
    rw [BitVec.add_assoc,show 96#32+48#32=144#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x80000482#32).getLsbD 0=false;decide) se2147484802 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    have v1 : c10.get 1=ramRead ram (frame+140#32) .w := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_jalr,v1,BitVec.add_zero]
    change Observed.interp B img o (jump c10 ((ramRead ram (frame+140#32) .w) &&& ~~~1)) ram 0 [] [] = _
    rw [jump_ok _ _ (clear_bit0 _)];first | rfl | (rw [hp];rfl)
  refine ⟨c11,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.single t10)))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · intro reg h1 h8 h9 h18 h19 h20 h21 h22 h23 h2;simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h1,h8,h9,h18,h19,h20,h21,h22,h23,h2]
end E5R.Thermostat.SendRestore
