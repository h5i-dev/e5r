import Projects.thermostat.ResponseHeadCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ResponseHeadRestore
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (frame tag len : Word) (h2 : c.get 2=frame+16#32) (h17 : c.get 17=tag) (h5 : c.get 5=len) (hm : Memory.Block B frame 96) (ha : frame.toNat%4=0)
    (hp : c.pc=0x80004100#32) :
    ∃ d, Quiet.Steps B img 17 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=(ramRead ram (frame+92#32) .w) &&& ~~~1 ∧
      d.get 1=ramRead ram (frame+92#32) .w ∧ d.get 8=ramRead ram (frame+88#32) .w ∧ d.get 9=ramRead ram (frame+84#32) .w ∧ d.get 18=ramRead ram (frame+80#32) .w ∧ d.get 19=ramRead ram (frame+76#32) .w ∧ d.get 20=ramRead ram (frame+72#32) .w ∧ d.get 21=ramRead ram (frame+68#32) .w ∧ d.get 22=ramRead ram (frame+64#32) .w ∧ d.get 23=ramRead ram (frame+60#32) .w ∧ d.get 24=ramRead ram (frame+56#32) .w ∧ d.get 25=ramRead ram (frame+52#32) .w ∧ d.get 26=ramRead ram (frame+48#32) .w ∧ d.get 27=ramRead ram (frame+44#32) .w ∧ d.get 2=frame+96#32 ∧ d.get 10=tag ∧ d.get 11=len ∧ (∀ r : Reg, r≠1 → r≠8 → r≠9 → r≠18 → r≠19 → r≠20 → r≠21 → r≠22 → r≠23 → r≠24 → r≠25 → r≠26 → r≠27 → r≠2 → r≠10 → r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 1 (ramRead ram (frame+92#32) .w) 0x80004102#32
  let c2 := c1.wr 8 (ramRead ram (frame+88#32) .w) 0x80004104#32
  let c3 := c2.wr 9 (ramRead ram (frame+84#32) .w) 0x80004106#32
  let c4 := c3.wr 18 (ramRead ram (frame+80#32) .w) 0x80004108#32
  let c5 := c4.wr 19 (ramRead ram (frame+76#32) .w) 0x8000410a#32
  let c6 := c5.wr 20 (ramRead ram (frame+72#32) .w) 0x8000410c#32
  let c7 := c6.wr 21 (ramRead ram (frame+68#32) .w) 0x8000410e#32
  let c8 := c7.wr 22 (ramRead ram (frame+64#32) .w) 0x80004110#32
  let c9 := c8.wr 23 (ramRead ram (frame+60#32) .w) 0x80004112#32
  let c10 := c9.wr 24 (ramRead ram (frame+56#32) .w) 0x80004114#32
  let c11 := c10.wr 25 (ramRead ram (frame+52#32) .w) 0x80004116#32
  let c12 := c11.wr 26 (ramRead ram (frame+48#32) .w) 0x80004118#32
  let c13 := c12.wr 27 (ramRead ram (frame+44#32) .w) 0x8000411a#32
  let c14 := c13.wr 2 (frame+96#32) 0x8000411c#32
  let c15 := c14.wr 10 (tag) 0x8000411e#32
  let c16 := c15.wr 11 (len) 0x80004120#32
  let c17 := c16.goto ((ramRead ram (frame+92#32) .w) &&& ~~~1)
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rh2147500288) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v2 : c.get 2=frame+16#32 := by simp [Core.wr_get_ne,Core.wr_get,h2,h17,h5]
    rw [exec_load,v2,BitVec.add_assoc,show 16#32+76#32=92#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 23 ha)
        (Memory.block_access hm (off := 92) (by decide) (by decide)),hp];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80004102#32).getLsbD 0=false;decide) rh2147500290 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v2 : c1.get 2=frame+16#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
    rw [exec_load,v2,BitVec.add_assoc,show 16#32+72#32=88#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 22 ha)
        (Memory.block_access hm (off := 88) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80004104#32).getLsbD 0=false;decide) rh2147500292 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v2 : c2.get 2=frame+16#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
    rw [exec_load,v2,BitVec.add_assoc,show 16#32+68#32=84#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 21 ha)
        (Memory.block_access hm (off := 84) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80004106#32).getLsbD 0=false;decide) rh2147500294 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v2 : c3.get 2=frame+16#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
    rw [exec_load,v2,BitVec.add_assoc,show 16#32+64#32=80#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 20 ha)
        (Memory.block_access hm (off := 80) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80004108#32).getLsbD 0=false;decide) rh2147500296 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v2 : c4.get 2=frame+16#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
    rw [exec_load,v2,BitVec.add_assoc,show 16#32+60#32=76#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 19 ha)
        (Memory.block_access hm (off := 76) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x8000410a#32).getLsbD 0=false;decide) rh2147500298 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v2 : c5.get 2=frame+16#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
    rw [exec_load,v2,BitVec.add_assoc,show 16#32+56#32=72#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 18 ha)
        (Memory.block_access hm (off := 72) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x8000410c#32).getLsbD 0=false;decide) rh2147500300 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v2 : c6.get 2=frame+16#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
    rw [exec_load,v2,BitVec.add_assoc,show 16#32+52#32=68#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 17 ha)
        (Memory.block_access hm (off := 68) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x8000410e#32).getLsbD 0=false;decide) rh2147500302 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v2 : c7.get 2=frame+16#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
    rw [exec_load,v2,BitVec.add_assoc,show 16#32+48#32=64#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 16 ha)
        (Memory.block_access hm (off := 64) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x80004110#32).getLsbD 0=false;decide) rh2147500304 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have v2 : c8.get 2=frame+16#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
    rw [exec_load,v2,BitVec.add_assoc,show 16#32+44#32=60#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 15 ha)
        (Memory.block_access hm (off := 60) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x80004112#32).getLsbD 0=false;decide) rh2147500306 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v2 : c9.get 2=frame+16#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
    rw [exec_load,v2,BitVec.add_assoc,show 16#32+40#32=56#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 14 ha)
        (Memory.block_access hm (off := 56) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x80004114#32).getLsbD 0=false;decide) rh2147500308 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    have v2 : c10.get 2=frame+16#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
    rw [exec_load,v2,BitVec.add_assoc,show 16#32+36#32=52#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 13 ha)
        (Memory.block_access hm (off := 52) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x80004116#32).getLsbD 0=false;decide) rh2147500310 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    have v2 : c11.get 2=frame+16#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
    rw [exec_load,v2,BitVec.add_assoc,show 16#32+32#32=48#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 12 ha)
        (Memory.block_access hm (off := 48) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine Quiet.step_of (by change (0x80004118#32).getLsbD 0=false;decide) rh2147500312 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) ram 0 [] [] = ⟨.ok c13 ram [],[]⟩
    have v2 : c12.get 2=frame+16#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
    rw [exec_load,v2,BitVec.add_assoc,show 16#32+28#32=44#32 by decide +kernel,
      Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned frame 11 ha)
        (Memory.block_access hm (off := 44) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine Quiet.step_of (by change (0x8000411a#32).getLsbD 0=false;decide) rh2147500314 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) ram 0 [] [] = ⟨.ok c14 ram [],[]⟩
    have v2 : c13.get 2=frame+16#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
    rw [exec_opimm,v2]
    change Observed.interp B img o (.done (c13.wr 2 ((frame+16#32)+80#32) 0x8000411c#32)) ram 0 [] [] = _
    rw [BitVec.add_assoc,show 16#32+80#32=96#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,ram⟩ ⟨c15,ram⟩ := by
    refine Quiet.step_of (by change (0x8000411c#32).getLsbD 0=false;decide) rh2147500316 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) ram 0 [] [] = ⟨.ok c15 ram [],[]⟩
    have v17 : c14.get 17=tag := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
    rw [exec_op,Core.get_zero,v17]
    change Observed.interp B img o (.done (c14.wr 10 (0#32+tag) 0x8000411e#32)) ram 0 [] [] = _
    rw [BitVec.zero_add];first | rfl | (rw [hp];rfl)
  have t15 : Quiet.Step B img ⟨c15,ram⟩ ⟨c16,ram⟩ := by
    refine Quiet.step_of (by change (0x8000411e#32).getLsbD 0=false;decide) rh2147500318 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) ram 0 [] [] = ⟨.ok c16 ram [],[]⟩
    have v5 : c15.get 5=len := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
    rw [exec_op,Core.get_zero,v5]
    change Observed.interp B img o (.done (c15.wr 11 (0#32+len) 0x80004120#32)) ram 0 [] [] = _
    rw [BitVec.zero_add];first | rfl | (rw [hp];rfl)
  have t16 : Quiet.Step B img ⟨c16,ram⟩ ⟨c17,ram⟩ := by
    refine Quiet.step_of (by change (0x80004120#32).getLsbD 0=false;decide) rh2147500320 fun o => ?_
    change Observed.interp B img o (exec c16 _ _) ram 0 [] [] = ⟨.ok c17 ram [],[]⟩
    have v1 : c16.get 1=ramRead ram (frame+92#32) .w := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
    rw [exec_jalr,v1,BitVec.add_zero]
    change Observed.interp B img o (jump c16 ((ramRead ram (frame+92#32) .w) &&& ~~~1)) ram 0 [] [] = _
    rw [jump_ok _ _ (clear_bit0 _)];first | rfl | (rw [hp];rfl)
  refine ⟨c17,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.single t16)))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
  · simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
  · simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
  · simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
  · simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
  · simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
  · simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
  · simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
  · simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
  · simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
  · simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
  · simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
  · simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
  · simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
  · simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
  · simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5]
  · intro reg h1 h8 h9 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h2 h10 h11;simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h17,h5,h1,h8,h9,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h2,h10,h11]
end E5R.Thermostat.ResponseHeadRestore
