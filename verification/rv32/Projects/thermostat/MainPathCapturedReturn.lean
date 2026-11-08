import Projects.thermostat.MainRouterCode
import Projects.thermostat.QuietRam
import Projects.thermostat.MainPathStateSave
import Projects.thermostat.Memory
import Projects.thermostat.ViewFrame
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainPathCapturedReturn
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (initial : Word → BitVec 8) (origin : Core) (ret : Word) (retAligned : ret.getLsbD 0=false) (retMask : ret &&& ~~~1=ret) (h2 : c.get 2=0x80ffeb50#32) (saved : ViewFrame.Region (MainPathStateSave.memory initial origin) ram 0x80ffeb30#32 96)
    (returnAddress : origin.get 1=ret) (stack : Memory.Block B 0x80ffeb50#32 64)
    (hp : c.pc=0x8000293a#32) :
    ∃ d, Quiet.Steps B img 15 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=ret ∧
      d.get 1=origin.get 1 ∧ d.get 8=origin.get 8 ∧ d.get 9=origin.get 9 ∧ d.get 18=origin.get 18 ∧ d.get 19=origin.get 19 ∧ d.get 20=origin.get 20 ∧ d.get 21=origin.get 21 ∧ d.get 22=origin.get 22 ∧ d.get 23=origin.get 23 ∧ d.get 24=origin.get 24 ∧ d.get 25=origin.get 25 ∧ d.get 26=origin.get 26 ∧ d.get 27=origin.get 27 ∧ d.get 2=0x80ffeb90#32 ∧ (∀ r : Reg, r≠1 → r≠8 → r≠9 → r≠18 → r≠19 → r≠20 → r≠21 → r≠22 → r≠23 → r≠24 → r≠25 → r≠26 → r≠27 → r≠2 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨w1,w8,w9,w18,w19,w20,w21,w22,w23,w24,w25,w26,w27⟩ := OuterSave.saved initial 0x80ffeb30#32 origin
  let c1 := c.wr 1 (origin.get 1) 0x8000293c#32
  let c2 := c1.wr 8 (origin.get 8) 0x8000293e#32
  let c3 := c2.wr 9 (origin.get 9) 0x80002940#32
  let c4 := c3.wr 18 (origin.get 18) 0x80002942#32
  let c5 := c4.wr 19 (origin.get 19) 0x80002944#32
  let c6 := c5.wr 20 (origin.get 20) 0x80002946#32
  let c7 := c6.wr 21 (origin.get 21) 0x80002948#32
  let c8 := c7.wr 22 (origin.get 22) 0x8000294a#32
  let c9 := c8.wr 23 (origin.get 23) 0x8000294c#32
  let c10 := c9.wr 24 (origin.get 24) 0x8000294e#32
  let c11 := c10.wr 25 (origin.get 25) 0x80002950#32
  let c12 := c11.wr 26 (origin.get 26) 0x80002952#32
  let c13 := c12.wr 27 (origin.get 27) 0x80002954#32
  let c14 := c13.wr 2 (0x80ffeb90#32) 0x80002956#32
  let c15 := c14.goto ret
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rt2147494202) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v2 : c.get 2=0x80ffeb50#32 := by simp [Core.wr_get_ne,Core.wr_get,h2]
    have wordValue : ramRead ram (0x80ffeb50#32+60#32) .w=origin.get 1 := by
      rw [show 0x80ffeb50#32+60#32=0x80ffeb30#32+92#32 by decide +kernel]
      rw [ViewFrame.word saved 92 (by decide),MainPathStateSave.memory_eq]
      exact w1
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned 0x80ffeb50#32 15 (by decide +kernel)) (Memory.block_access stack (off := 60) (by decide) (by decide)),wordValue];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x8000293c#32).getLsbD 0=false;decide) rt2147494204 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v2 : c1.get 2=0x80ffeb50#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2]
    have wordValue : ramRead ram (0x80ffeb50#32+56#32) .w=origin.get 8 := by
      rw [show 0x80ffeb50#32+56#32=0x80ffeb30#32+88#32 by decide +kernel]
      rw [ViewFrame.word saved 88 (by decide),MainPathStateSave.memory_eq]
      exact w8
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned 0x80ffeb50#32 14 (by decide +kernel)) (Memory.block_access stack (off := 56) (by decide) (by decide)),wordValue];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x8000293e#32).getLsbD 0=false;decide) rt2147494206 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v2 : c2.get 2=0x80ffeb50#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have wordValue : ramRead ram (0x80ffeb50#32+52#32) .w=origin.get 9 := by
      rw [show 0x80ffeb50#32+52#32=0x80ffeb30#32+84#32 by decide +kernel]
      rw [ViewFrame.word saved 84 (by decide),MainPathStateSave.memory_eq]
      exact w9
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned 0x80ffeb50#32 13 (by decide +kernel)) (Memory.block_access stack (off := 52) (by decide) (by decide)),wordValue];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80002940#32).getLsbD 0=false;decide) rt2147494208 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v2 : c3.get 2=0x80ffeb50#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have wordValue : ramRead ram (0x80ffeb50#32+48#32) .w=origin.get 18 := by
      rw [show 0x80ffeb50#32+48#32=0x80ffeb30#32+80#32 by decide +kernel]
      rw [ViewFrame.word saved 80 (by decide),MainPathStateSave.memory_eq]
      exact w18
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned 0x80ffeb50#32 12 (by decide +kernel)) (Memory.block_access stack (off := 48) (by decide) (by decide)),wordValue];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80002942#32).getLsbD 0=false;decide) rt2147494210 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v2 : c4.get 2=0x80ffeb50#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have wordValue : ramRead ram (0x80ffeb50#32+44#32) .w=origin.get 19 := by
      rw [show 0x80ffeb50#32+44#32=0x80ffeb30#32+76#32 by decide +kernel]
      rw [ViewFrame.word saved 76 (by decide),MainPathStateSave.memory_eq]
      exact w19
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned 0x80ffeb50#32 11 (by decide +kernel)) (Memory.block_access stack (off := 44) (by decide) (by decide)),wordValue];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80002944#32).getLsbD 0=false;decide) rt2147494212 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v2 : c5.get 2=0x80ffeb50#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have wordValue : ramRead ram (0x80ffeb50#32+40#32) .w=origin.get 20 := by
      rw [show 0x80ffeb50#32+40#32=0x80ffeb30#32+72#32 by decide +kernel]
      rw [ViewFrame.word saved 72 (by decide),MainPathStateSave.memory_eq]
      exact w20
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned 0x80ffeb50#32 10 (by decide +kernel)) (Memory.block_access stack (off := 40) (by decide) (by decide)),wordValue];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80002946#32).getLsbD 0=false;decide) rt2147494214 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v2 : c6.get 2=0x80ffeb50#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have wordValue : ramRead ram (0x80ffeb50#32+36#32) .w=origin.get 21 := by
      rw [show 0x80ffeb50#32+36#32=0x80ffeb30#32+68#32 by decide +kernel]
      rw [ViewFrame.word saved 68 (by decide),MainPathStateSave.memory_eq]
      exact w21
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned 0x80ffeb50#32 9 (by decide +kernel)) (Memory.block_access stack (off := 36) (by decide) (by decide)),wordValue];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x80002948#32).getLsbD 0=false;decide) rt2147494216 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v2 : c7.get 2=0x80ffeb50#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have wordValue : ramRead ram (0x80ffeb50#32+32#32) .w=origin.get 22 := by
      rw [show 0x80ffeb50#32+32#32=0x80ffeb30#32+64#32 by decide +kernel]
      rw [ViewFrame.word saved 64 (by decide),MainPathStateSave.memory_eq]
      exact w22
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned 0x80ffeb50#32 8 (by decide +kernel)) (Memory.block_access stack (off := 32) (by decide) (by decide)),wordValue];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x8000294a#32).getLsbD 0=false;decide) rt2147494218 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have v2 : c8.get 2=0x80ffeb50#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have wordValue : ramRead ram (0x80ffeb50#32+28#32) .w=origin.get 23 := by
      rw [show 0x80ffeb50#32+28#32=0x80ffeb30#32+60#32 by decide +kernel]
      rw [ViewFrame.word saved 60 (by decide),MainPathStateSave.memory_eq]
      exact w23
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned 0x80ffeb50#32 7 (by decide +kernel)) (Memory.block_access stack (off := 28) (by decide) (by decide)),wordValue];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x8000294c#32).getLsbD 0=false;decide) rt2147494220 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v2 : c9.get 2=0x80ffeb50#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have wordValue : ramRead ram (0x80ffeb50#32+24#32) .w=origin.get 24 := by
      rw [show 0x80ffeb50#32+24#32=0x80ffeb30#32+56#32 by decide +kernel]
      rw [ViewFrame.word saved 56 (by decide),MainPathStateSave.memory_eq]
      exact w24
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned 0x80ffeb50#32 6 (by decide +kernel)) (Memory.block_access stack (off := 24) (by decide) (by decide)),wordValue];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x8000294e#32).getLsbD 0=false;decide) rt2147494222 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    have v2 : c10.get 2=0x80ffeb50#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have wordValue : ramRead ram (0x80ffeb50#32+20#32) .w=origin.get 25 := by
      rw [show 0x80ffeb50#32+20#32=0x80ffeb30#32+52#32 by decide +kernel]
      rw [ViewFrame.word saved 52 (by decide),MainPathStateSave.memory_eq]
      exact w25
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned 0x80ffeb50#32 5 (by decide +kernel)) (Memory.block_access stack (off := 20) (by decide) (by decide)),wordValue];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x80002950#32).getLsbD 0=false;decide) rt2147494224 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    have v2 : c11.get 2=0x80ffeb50#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have wordValue : ramRead ram (0x80ffeb50#32+16#32) .w=origin.get 26 := by
      rw [show 0x80ffeb50#32+16#32=0x80ffeb30#32+48#32 by decide +kernel]
      rw [ViewFrame.word saved 48 (by decide),MainPathStateSave.memory_eq]
      exact w26
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned 0x80ffeb50#32 4 (by decide +kernel)) (Memory.block_access stack (off := 16) (by decide) (by decide)),wordValue];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine Quiet.step_of (by change (0x80002952#32).getLsbD 0=false;decide) rt2147494226 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) ram 0 [] [] = ⟨.ok c13 ram [],[]⟩
    have v2 : c12.get 2=0x80ffeb50#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have wordValue : ramRead ram (0x80ffeb50#32+12#32) .w=origin.get 27 := by
      rw [show 0x80ffeb50#32+12#32=0x80ffeb30#32+44#32 by decide +kernel]
      rw [ViewFrame.word saved 44 (by decide),MainPathStateSave.memory_eq]
      exact w27
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned 0x80ffeb50#32 3 (by decide +kernel)) (Memory.block_access stack (off := 12) (by decide) (by decide)),wordValue];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine Quiet.step_of (by change (0x80002954#32).getLsbD 0=false;decide) rt2147494228 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) ram 0 [] [] = ⟨.ok c14 ram [],[]⟩
    have v2 : c13.get 2=0x80ffeb50#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_opimm,v2]
    change Observed.interp B img o (.done (c13.wr 2 (0x80ffeb50#32+64#32) 0x80002956#32)) ram 0 [] []=_
    rw [show 0x80ffeb50#32+64#32=0x80ffeb90#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,ram⟩ ⟨c15,ram⟩ := by
    refine Quiet.step_of (by change (0x80002956#32).getLsbD 0=false;decide) rt2147494230 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) ram 0 [] [] = ⟨.ok c15 ram [],[]⟩
    have v1 : c14.get 1=origin.get 1 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_jalr,v1,returnAddress,BitVec.add_zero]
    change Observed.interp B img o (jump c14 (ret &&& ~~~1)) ram 0 [] []=_
    rw [retMask,jump_ok _ _ retAligned];first | rfl | (rw [hp];rfl)
  refine ⟨c15,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.single t14)))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · intro reg h1 h8 h9 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h2;simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h1,h8,h9,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h2]
end E5R.Thermostat.MainPathCapturedReturn
