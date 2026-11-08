import Projects.thermostat.HttpParseCode00
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadStackSave
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp : Word) (saved : Reg → Word) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (sp+380#32) (saved 1) .w) (sp+376#32) (saved 8) .w) (sp+372#32) (saved 9) .w) (sp+368#32) (saved 18) .w) (sp+364#32) (saved 19) .w) (sp+360#32) (saved 20) .w) (sp+356#32) (saved 21) .w) (sp+352#32) (saved 22) .w) (sp+348#32) (saved 23) .w) (sp+344#32) (saved 24) .w) (sp+340#32) (saved 25) .w) (sp+336#32) (saved 26) .w) (sp+332#32) (saved 27) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (saved : Reg → Word) (h2 : c.get 2=sp+384#32) (hsaved : ∀ r : Reg, r≠2 → c.get r=saved r)
(hm : Memory.Block B sp 384) (ha : sp.toNat%4=0)
    (hp : c.pc=0x80002c46#32) :
    ∃ d, Quiet.Steps B img 14 ⟨c,ram⟩ ⟨d,memory ram sp saved⟩ ∧ d.pc=0x80002c7c#32 ∧
      d.get 2=sp ∧ (∀ r : Reg, r≠2 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 2 (sp) 0x80002c48#32
  let r1 := ramWrite ram (sp+380#32) (saved 1) .w
  let c2 := c1.goto 0x80002c4c#32
  let r2 := ramWrite r1 (sp+376#32) (saved 8) .w
  let c3 := c2.goto 0x80002c50#32
  let r3 := ramWrite r2 (sp+372#32) (saved 9) .w
  let c4 := c3.goto 0x80002c54#32
  let r4 := ramWrite r3 (sp+368#32) (saved 18) .w
  let c5 := c4.goto 0x80002c58#32
  let r5 := ramWrite r4 (sp+364#32) (saved 19) .w
  let c6 := c5.goto 0x80002c5c#32
  let r6 := ramWrite r5 (sp+360#32) (saved 20) .w
  let c7 := c6.goto 0x80002c60#32
  let r7 := ramWrite r6 (sp+356#32) (saved 21) .w
  let c8 := c7.goto 0x80002c64#32
  let r8 := ramWrite r7 (sp+352#32) (saved 22) .w
  let c9 := c8.goto 0x80002c68#32
  let r9 := ramWrite r8 (sp+348#32) (saved 23) .w
  let c10 := c9.goto 0x80002c6c#32
  let r10 := ramWrite r9 (sp+344#32) (saved 24) .w
  let c11 := c10.goto 0x80002c70#32
  let r11 := ramWrite r10 (sp+340#32) (saved 25) .w
  let c12 := c11.goto 0x80002c74#32
  let r12 := ramWrite r11 (sp+336#32) (saved 26) .w
  let c13 := c12.goto 0x80002c78#32
  let r13 := ramWrite r12 (sp+332#32) (saved 27) .w
  let c14 := c13.goto 0x80002c7c#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147494982) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,h2,hp]
    have add : alu .add (sp+384#32) 0xfffffe80#32=sp := by
     change (sp+384#32)+0xfffffe80#32=sp
     rw [BitVec.add_assoc,show 384#32+0xfffffe80#32=0#32 by decide +kernel,BitVec.add_zero]
    rw [add];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine Quiet.step_of (by change (0x80002c48#32).getLsbD 0=false;decide) hh2147494984 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 r1 [],[]⟩
    have v2 : c1.get 2=sp := by simp [c1,Core.wr_get_ne,Core.wr_get,h2]
    have vr : c1.get 1=saved 1 := by
     have hs := hsaved 1 (by decide)
     simpa [c1,Core.wr_get_ne,Core.wr_get,h2] using hs
    rw [exec_store,v2,vr,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 95 ha)
    (Memory.block_access hm (off := 380) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,r2⟩ := by
    refine Quiet.step_of (by change (0x80002c4c#32).getLsbD 0=false;decide) hh2147494988 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) r1 0 [] [] = ⟨.ok c3 r2 [],[]⟩
    have v2 : c2.get 2=sp := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have vr : c2.get 8=saved 8 := by
     have hs := hsaved 8 (by decide)
     simpa [c2,c1,Core.wr_get_ne,Core.wr_get,h2] using hs
    rw [exec_store,v2,vr,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 94 ha)
    (Memory.block_access hm (off := 376) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r2⟩ ⟨c4,r3⟩ := by
    refine Quiet.step_of (by change (0x80002c50#32).getLsbD 0=false;decide) hh2147494992 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r2 0 [] [] = ⟨.ok c4 r3 [],[]⟩
    have v2 : c3.get 2=sp := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have vr : c3.get 9=saved 9 := by
     have hs := hsaved 9 (by decide)
     simpa [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2] using hs
    rw [exec_store,v2,vr,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 93 ha)
    (Memory.block_access hm (off := 372) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r3⟩ ⟨c5,r4⟩ := by
    refine Quiet.step_of (by change (0x80002c54#32).getLsbD 0=false;decide) hh2147494996 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r3 0 [] [] = ⟨.ok c5 r4 [],[]⟩
    have v2 : c4.get 2=sp := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have vr : c4.get 18=saved 18 := by
     have hs := hsaved 18 (by decide)
     simpa [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2] using hs
    rw [exec_store,v2,vr,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 92 ha)
    (Memory.block_access hm (off := 368) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r4⟩ ⟨c6,r5⟩ := by
    refine Quiet.step_of (by change (0x80002c58#32).getLsbD 0=false;decide) hh2147495000 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r4 0 [] [] = ⟨.ok c6 r5 [],[]⟩
    have v2 : c5.get 2=sp := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have vr : c5.get 19=saved 19 := by
     have hs := hsaved 19 (by decide)
     simpa [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2] using hs
    rw [exec_store,v2,vr,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 91 ha)
    (Memory.block_access hm (off := 364) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r5⟩ ⟨c7,r6⟩ := by
    refine Quiet.step_of (by change (0x80002c5c#32).getLsbD 0=false;decide) hh2147495004 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r5 0 [] [] = ⟨.ok c7 r6 [],[]⟩
    have v2 : c6.get 2=sp := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have vr : c6.get 20=saved 20 := by
     have hs := hsaved 20 (by decide)
     simpa [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2] using hs
    rw [exec_store,v2,vr,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 90 ha)
    (Memory.block_access hm (off := 360) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,r6⟩ ⟨c8,r7⟩ := by
    refine Quiet.step_of (by change (0x80002c60#32).getLsbD 0=false;decide) hh2147495008 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r6 0 [] [] = ⟨.ok c8 r7 [],[]⟩
    have v2 : c7.get 2=sp := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have vr : c7.get 21=saved 21 := by
     have hs := hsaved 21 (by decide)
     simpa [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2] using hs
    rw [exec_store,v2,vr,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 89 ha)
    (Memory.block_access hm (off := 356) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,r7⟩ ⟨c9,r8⟩ := by
    refine Quiet.step_of (by change (0x80002c64#32).getLsbD 0=false;decide) hh2147495012 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r7 0 [] [] = ⟨.ok c9 r8 [],[]⟩
    have v2 : c8.get 2=sp := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have vr : c8.get 22=saved 22 := by
     have hs := hsaved 22 (by decide)
     simpa [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2] using hs
    rw [exec_store,v2,vr,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 88 ha)
    (Memory.block_access hm (off := 352) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,r8⟩ ⟨c10,r9⟩ := by
    refine Quiet.step_of (by change (0x80002c68#32).getLsbD 0=false;decide) hh2147495016 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) r8 0 [] [] = ⟨.ok c10 r9 [],[]⟩
    have v2 : c9.get 2=sp := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have vr : c9.get 23=saved 23 := by
     have hs := hsaved 23 (by decide)
     simpa [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2] using hs
    rw [exec_store,v2,vr,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 87 ha)
    (Memory.block_access hm (off := 348) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,r9⟩ ⟨c11,r10⟩ := by
    refine Quiet.step_of (by change (0x80002c6c#32).getLsbD 0=false;decide) hh2147495020 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) r9 0 [] [] = ⟨.ok c11 r10 [],[]⟩
    have v2 : c10.get 2=sp := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have vr : c10.get 24=saved 24 := by
     have hs := hsaved 24 (by decide)
     simpa [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2] using hs
    rw [exec_store,v2,vr,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 86 ha)
    (Memory.block_access hm (off := 344) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,r10⟩ ⟨c12,r11⟩ := by
    refine Quiet.step_of (by change (0x80002c70#32).getLsbD 0=false;decide) hh2147495024 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) r10 0 [] [] = ⟨.ok c12 r11 [],[]⟩
    have v2 : c11.get 2=sp := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have vr : c11.get 25=saved 25 := by
     have hs := hsaved 25 (by decide)
     simpa [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2] using hs
    rw [exec_store,v2,vr,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 85 ha)
    (Memory.block_access hm (off := 340) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,r11⟩ ⟨c13,r12⟩ := by
    refine Quiet.step_of (by change (0x80002c74#32).getLsbD 0=false;decide) hh2147495028 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) r11 0 [] [] = ⟨.ok c13 r12 [],[]⟩
    have v2 : c12.get 2=sp := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have vr : c12.get 26=saved 26 := by
     have hs := hsaved 26 (by decide)
     simpa [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2] using hs
    rw [exec_store,v2,vr,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 84 ha)
    (Memory.block_access hm (off := 336) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,r12⟩ ⟨c14,r13⟩ := by
    refine Quiet.step_of (by change (0x80002c78#32).getLsbD 0=false;decide) hh2147495032 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) r12 0 [] [] = ⟨.ok c14 r13 [],[]⟩
    have v2 : c13.get 2=sp := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    have vr : c13.get 27=saved 27 := by
     have hs := hsaved 27 (by decide)
     simpa [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2] using hs
    rw [exec_store,v2,vr,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 83 ha)
    (Memory.block_access hm (off := 332) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c14,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.single t13))))))))))))),rfl,?_ ,?_ ,by rfl⟩
  · simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
  · intro reg h2;simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h2]
end E5R.Thermostat.HeadStackSave
