import Projects.thermostat.MainRouterCode
import Projects.thermostat.QuietRam
import Projects.thermostat.OuterSave
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainPathStateSave
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (origin : Core) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (0x80ffeb30#32+92#32) (origin.get 1) .w) (0x80ffeb30#32+88#32) (origin.get 8) .w) (0x80ffeb30#32+84#32) (origin.get 9) .w) (0x80ffeb30#32+80#32) (origin.get 18) .w) (0x80ffeb30#32+76#32) (origin.get 19) .w) (0x80ffeb30#32+72#32) (origin.get 20) .w) (0x80ffeb30#32+68#32) (origin.get 21) .w) (0x80ffeb30#32+64#32) (origin.get 22) .w) (0x80ffeb30#32+60#32) (origin.get 23) .w) (0x80ffeb30#32+56#32) (origin.get 24) .w) (0x80ffeb30#32+52#32) (origin.get 25) .w) (0x80ffeb30#32+48#32) (origin.get 26) .w) (0x80ffeb30#32+44#32) (origin.get 27) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (origin : Core) (same : c=origin) (h2 : c.get 2=0x80ffeb90#32)
    (stack : Memory.Block B 0x80ffeb50#32 64)
    (hp : c.pc=0x8000283a#32) :
    ∃ d, Quiet.Steps B img 14 ⟨c,ram⟩ ⟨d,memory ram origin⟩ ∧ d.pc=0x80002856#32 ∧
      d.get 2=0x80ffeb50#32 ∧ (∀ r : Reg, r≠2 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 2 (0x80ffeb50#32) 0x8000283c#32
  let r1 := ramWrite ram (0x80ffeb30#32+92#32) (origin.get 1) .w
  let c2 := c1.goto 0x8000283e#32
  let r2 := ramWrite r1 (0x80ffeb30#32+88#32) (origin.get 8) .w
  let c3 := c2.goto 0x80002840#32
  let r3 := ramWrite r2 (0x80ffeb30#32+84#32) (origin.get 9) .w
  let c4 := c3.goto 0x80002842#32
  let r4 := ramWrite r3 (0x80ffeb30#32+80#32) (origin.get 18) .w
  let c5 := c4.goto 0x80002844#32
  let r5 := ramWrite r4 (0x80ffeb30#32+76#32) (origin.get 19) .w
  let c6 := c5.goto 0x80002846#32
  let r6 := ramWrite r5 (0x80ffeb30#32+72#32) (origin.get 20) .w
  let c7 := c6.goto 0x80002848#32
  let r7 := ramWrite r6 (0x80ffeb30#32+68#32) (origin.get 21) .w
  let c8 := c7.goto 0x8000284a#32
  let r8 := ramWrite r7 (0x80ffeb30#32+64#32) (origin.get 22) .w
  let c9 := c8.goto 0x8000284c#32
  let r9 := ramWrite r8 (0x80ffeb30#32+60#32) (origin.get 23) .w
  let c10 := c9.goto 0x8000284e#32
  let r10 := ramWrite r9 (0x80ffeb30#32+56#32) (origin.get 24) .w
  let c11 := c10.goto 0x80002850#32
  let r11 := ramWrite r10 (0x80ffeb30#32+52#32) (origin.get 25) .w
  let c12 := c11.goto 0x80002852#32
  let r12 := ramWrite r11 (0x80ffeb30#32+48#32) (origin.get 26) .w
  let c13 := c12.goto 0x80002854#32
  let r13 := ramWrite r12 (0x80ffeb30#32+44#32) (origin.get 27) .w
  let c14 := c13.goto 0x80002856#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rt2147493946) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v2 : c.get 2=0x80ffeb90#32 := by simp [Core.wr_get_ne,Core.wr_get,h2,←same]
    rw [exec_opimm,v2,hp]
    change Observed.interp B img o (.done (c.wr 2 (0x80ffeb90#32+0xffffffc0#32) 0x8000283c#32)) ram 0 [] []=_
    rw [show 0x80ffeb90#32+0xffffffc0#32=0x80ffeb50#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine Quiet.step_of (by change (0x8000283c#32).getLsbD 0=false;decide) rt2147493948 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 r1 [],[]⟩
    have v2 : c1.get 2=0x80ffeb50#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    have v1 : c1.get 1=origin.get 1 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    rw [exec_store,v2,v1,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned 0x80ffeb50#32 15 (by decide +kernel)) (Memory.block_access stack (off := 60) (by decide) (by decide))]
    change Observed.interp B img o (.done (c1.goto (c1.pc+2#32))) (ramWrite ram (0x80ffeb50#32+60#32) (origin.get 1) .w) 0 [] []=_
    rw [show 0x80ffeb50#32+60#32=0x80ffeb30#32+92#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,r2⟩ := by
    refine Quiet.step_of (by change (0x8000283e#32).getLsbD 0=false;decide) rt2147493950 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) r1 0 [] [] = ⟨.ok c3 r2 [],[]⟩
    have v2 : c2.get 2=0x80ffeb50#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    have v8 : c2.get 8=origin.get 8 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    rw [exec_store,v2,v8,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned 0x80ffeb50#32 14 (by decide +kernel)) (Memory.block_access stack (off := 56) (by decide) (by decide))]
    change Observed.interp B img o (.done (c2.goto (c2.pc+2#32))) (ramWrite r1 (0x80ffeb50#32+56#32) (origin.get 8) .w) 0 [] []=_
    rw [show 0x80ffeb50#32+56#32=0x80ffeb30#32+88#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r2⟩ ⟨c4,r3⟩ := by
    refine Quiet.step_of (by change (0x80002840#32).getLsbD 0=false;decide) rt2147493952 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r2 0 [] [] = ⟨.ok c4 r3 [],[]⟩
    have v2 : c3.get 2=0x80ffeb50#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    have v9 : c3.get 9=origin.get 9 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    rw [exec_store,v2,v9,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned 0x80ffeb50#32 13 (by decide +kernel)) (Memory.block_access stack (off := 52) (by decide) (by decide))]
    change Observed.interp B img o (.done (c3.goto (c3.pc+2#32))) (ramWrite r2 (0x80ffeb50#32+52#32) (origin.get 9) .w) 0 [] []=_
    rw [show 0x80ffeb50#32+52#32=0x80ffeb30#32+84#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r3⟩ ⟨c5,r4⟩ := by
    refine Quiet.step_of (by change (0x80002842#32).getLsbD 0=false;decide) rt2147493954 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r3 0 [] [] = ⟨.ok c5 r4 [],[]⟩
    have v2 : c4.get 2=0x80ffeb50#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    have v18 : c4.get 18=origin.get 18 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    rw [exec_store,v2,v18,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned 0x80ffeb50#32 12 (by decide +kernel)) (Memory.block_access stack (off := 48) (by decide) (by decide))]
    change Observed.interp B img o (.done (c4.goto (c4.pc+2#32))) (ramWrite r3 (0x80ffeb50#32+48#32) (origin.get 18) .w) 0 [] []=_
    rw [show 0x80ffeb50#32+48#32=0x80ffeb30#32+80#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r4⟩ ⟨c6,r5⟩ := by
    refine Quiet.step_of (by change (0x80002844#32).getLsbD 0=false;decide) rt2147493956 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r4 0 [] [] = ⟨.ok c6 r5 [],[]⟩
    have v2 : c5.get 2=0x80ffeb50#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    have v19 : c5.get 19=origin.get 19 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    rw [exec_store,v2,v19,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned 0x80ffeb50#32 11 (by decide +kernel)) (Memory.block_access stack (off := 44) (by decide) (by decide))]
    change Observed.interp B img o (.done (c5.goto (c5.pc+2#32))) (ramWrite r4 (0x80ffeb50#32+44#32) (origin.get 19) .w) 0 [] []=_
    rw [show 0x80ffeb50#32+44#32=0x80ffeb30#32+76#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r5⟩ ⟨c7,r6⟩ := by
    refine Quiet.step_of (by change (0x80002846#32).getLsbD 0=false;decide) rt2147493958 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r5 0 [] [] = ⟨.ok c7 r6 [],[]⟩
    have v2 : c6.get 2=0x80ffeb50#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    have v20 : c6.get 20=origin.get 20 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    rw [exec_store,v2,v20,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned 0x80ffeb50#32 10 (by decide +kernel)) (Memory.block_access stack (off := 40) (by decide) (by decide))]
    change Observed.interp B img o (.done (c6.goto (c6.pc+2#32))) (ramWrite r5 (0x80ffeb50#32+40#32) (origin.get 20) .w) 0 [] []=_
    rw [show 0x80ffeb50#32+40#32=0x80ffeb30#32+72#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,r6⟩ ⟨c8,r7⟩ := by
    refine Quiet.step_of (by change (0x80002848#32).getLsbD 0=false;decide) rt2147493960 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r6 0 [] [] = ⟨.ok c8 r7 [],[]⟩
    have v2 : c7.get 2=0x80ffeb50#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    have v21 : c7.get 21=origin.get 21 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    rw [exec_store,v2,v21,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned 0x80ffeb50#32 9 (by decide +kernel)) (Memory.block_access stack (off := 36) (by decide) (by decide))]
    change Observed.interp B img o (.done (c7.goto (c7.pc+2#32))) (ramWrite r6 (0x80ffeb50#32+36#32) (origin.get 21) .w) 0 [] []=_
    rw [show 0x80ffeb50#32+36#32=0x80ffeb30#32+68#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,r7⟩ ⟨c9,r8⟩ := by
    refine Quiet.step_of (by change (0x8000284a#32).getLsbD 0=false;decide) rt2147493962 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r7 0 [] [] = ⟨.ok c9 r8 [],[]⟩
    have v2 : c8.get 2=0x80ffeb50#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    have v22 : c8.get 22=origin.get 22 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    rw [exec_store,v2,v22,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned 0x80ffeb50#32 8 (by decide +kernel)) (Memory.block_access stack (off := 32) (by decide) (by decide))]
    change Observed.interp B img o (.done (c8.goto (c8.pc+2#32))) (ramWrite r7 (0x80ffeb50#32+32#32) (origin.get 22) .w) 0 [] []=_
    rw [show 0x80ffeb50#32+32#32=0x80ffeb30#32+64#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,r8⟩ ⟨c10,r9⟩ := by
    refine Quiet.step_of (by change (0x8000284c#32).getLsbD 0=false;decide) rt2147493964 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) r8 0 [] [] = ⟨.ok c10 r9 [],[]⟩
    have v2 : c9.get 2=0x80ffeb50#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    have v23 : c9.get 23=origin.get 23 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    rw [exec_store,v2,v23,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned 0x80ffeb50#32 7 (by decide +kernel)) (Memory.block_access stack (off := 28) (by decide) (by decide))]
    change Observed.interp B img o (.done (c9.goto (c9.pc+2#32))) (ramWrite r8 (0x80ffeb50#32+28#32) (origin.get 23) .w) 0 [] []=_
    rw [show 0x80ffeb50#32+28#32=0x80ffeb30#32+60#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,r9⟩ ⟨c11,r10⟩ := by
    refine Quiet.step_of (by change (0x8000284e#32).getLsbD 0=false;decide) rt2147493966 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) r9 0 [] [] = ⟨.ok c11 r10 [],[]⟩
    have v2 : c10.get 2=0x80ffeb50#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    have v24 : c10.get 24=origin.get 24 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    rw [exec_store,v2,v24,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned 0x80ffeb50#32 6 (by decide +kernel)) (Memory.block_access stack (off := 24) (by decide) (by decide))]
    change Observed.interp B img o (.done (c10.goto (c10.pc+2#32))) (ramWrite r9 (0x80ffeb50#32+24#32) (origin.get 24) .w) 0 [] []=_
    rw [show 0x80ffeb50#32+24#32=0x80ffeb30#32+56#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,r10⟩ ⟨c12,r11⟩ := by
    refine Quiet.step_of (by change (0x80002850#32).getLsbD 0=false;decide) rt2147493968 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) r10 0 [] [] = ⟨.ok c12 r11 [],[]⟩
    have v2 : c11.get 2=0x80ffeb50#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    have v25 : c11.get 25=origin.get 25 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    rw [exec_store,v2,v25,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned 0x80ffeb50#32 5 (by decide +kernel)) (Memory.block_access stack (off := 20) (by decide) (by decide))]
    change Observed.interp B img o (.done (c11.goto (c11.pc+2#32))) (ramWrite r10 (0x80ffeb50#32+20#32) (origin.get 25) .w) 0 [] []=_
    rw [show 0x80ffeb50#32+20#32=0x80ffeb30#32+52#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,r11⟩ ⟨c13,r12⟩ := by
    refine Quiet.step_of (by change (0x80002852#32).getLsbD 0=false;decide) rt2147493970 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) r11 0 [] [] = ⟨.ok c13 r12 [],[]⟩
    have v2 : c12.get 2=0x80ffeb50#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    have v26 : c12.get 26=origin.get 26 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    rw [exec_store,v2,v26,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned 0x80ffeb50#32 4 (by decide +kernel)) (Memory.block_access stack (off := 16) (by decide) (by decide))]
    change Observed.interp B img o (.done (c12.goto (c12.pc+2#32))) (ramWrite r11 (0x80ffeb50#32+16#32) (origin.get 26) .w) 0 [] []=_
    rw [show 0x80ffeb50#32+16#32=0x80ffeb30#32+48#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,r12⟩ ⟨c14,r13⟩ := by
    refine Quiet.step_of (by change (0x80002854#32).getLsbD 0=false;decide) rt2147493972 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) r12 0 [] [] = ⟨.ok c14 r13 [],[]⟩
    have v2 : c13.get 2=0x80ffeb50#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    have v27 : c13.get 27=origin.get 27 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    rw [exec_store,v2,v27,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned 0x80ffeb50#32 3 (by decide +kernel)) (Memory.block_access stack (off := 12) (by decide) (by decide))]
    change Observed.interp B img o (.done (c13.goto (c13.pc+2#32))) (ramWrite r12 (0x80ffeb50#32+12#32) (origin.get 27) .w) 0 [] []=_
    rw [show 0x80ffeb50#32+12#32=0x80ffeb30#32+44#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  refine ⟨c14,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.single t13))))))))))))),rfl,?_ ,?_ ,by rfl⟩
  · simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
  · intro reg h2;simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same,h2]
/-- Identical thirteen RAM word locations to the existing checked save model;
    the path matcher's actual SP is32bytes above that model's frame base. -/
theorem memory_eq (ram : Word → BitVec 8) (origin : Core) : memory ram origin=OuterSave.memory ram 0x80ffeb30#32 origin := rfl
end E5R.Thermostat.MainPathStateSave
