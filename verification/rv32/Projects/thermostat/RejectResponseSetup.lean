import Projects.thermostat.RejectResponseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.RejectResponseSetup
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (io status : Word) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (0x80fff814#32+108#32) (0x80fff414#32) .w) (0x80fff814#32+112#32) (1024#32) .w) (0x80fff814#32+124#32) (io) .w) (0x80fff814#32+128#32) (1#32) .w) (0x80fff814#32+132#32) (0#32) .w) (0x80fff814#32+136#32) (0#32) .w) (0x80fff814#32+140#32) (status) .h) (0x80fff814#32+142#32) (1#32) .b) (0x80fff814#32+145#32) (0#32) .b) (0x80fff814#32+146#32) (0#32) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (io status : Word) (sp : c.get 2=0x80ffeb90#32) (fp : c.get 8=0x80fff814#32) (one : c.get 22=1#32) (tag : c.get 10=1#32) (replyStatus : c.get 27=status) (tx : ramRead ram (0x80fff814#32+64#32) .w=0x80fff414#32) (capacity : ramRead ram (0x80fff814#32+68#32) .w=1024#32) (ioWord : ramRead ram (0x80fff814#32+72#32) .w=io) (object : Memory.Block B 0x80fff814#32 148)
    (hp : c.pc=0x80001bbc#32) :
    ∃ d, Quiet.Steps B img 24 ⟨c,ram⟩ ⟨d,memory ram io status⟩ ∧ d.pc=0x8000030e#32 ∧
      d.get 9=0x80fff878#32 ∧ d.get 24=0xfffffffe#32 ∧ d.get 18=2#32 ∧ d.get 10=0x80fffd38#32 ∧ d.get 11=0x80fff878#32 ∧ d.get 12=io ∧ d.get 1=0x80001c0a#32 ∧ (∀ r : Reg, r≠9 → r≠24 → r≠18 → r≠10 → r≠11 → r≠12 → r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 9 (0x80fff38f#32) 0x80001bc0#32
  let c2 := c1.wr 9 (0x80fff878#32) 0x80001bc4#32
  let c3 := c2.wr 24 (0xfffffffe#32) 0x80001bc6#32
  let c4 := c3.wr 18 (2#32) 0x80001bc8#32
  let c5 := c4.goto 0x80001bd0#32
  let c6 := c5.wr 10 (0x80fff414#32) 0x80001bd2#32
  let c7 := c6.wr 11 (1024#32) 0x80001bd4#32
  let c8 := c7.wr 12 (io) 0x80001bd6#32
  let r1 := ramWrite ram (0x80fff814#32+108#32) (0x80fff414#32) .w
  let c9 := c8.goto 0x80001bd8#32
  let r2 := ramWrite r1 (0x80fff814#32+112#32) (1024#32) .w
  let c10 := c9.goto 0x80001bda#32
  let r3 := ramWrite r2 (0x80fff814#32+124#32) (io) .w
  let c11 := c10.goto 0x80001bdc#32
  let r4 := ramWrite r3 (0x80fff814#32+128#32) (1#32) .w
  let c12 := c11.goto 0x80001be0#32
  let r5 := ramWrite r4 (0x80fff814#32+132#32) (0#32) .w
  let c13 := c12.goto 0x80001be4#32
  let r6 := ramWrite r5 (0x80fff814#32+136#32) (0#32) .w
  let c14 := c13.goto 0x80001be8#32
  let r7 := ramWrite r6 (0x80fff814#32+140#32) (status) .h
  let c15 := c14.goto 0x80001bec#32
  let r8 := ramWrite r7 (0x80fff814#32+142#32) (1#32) .b
  let c16 := c15.goto 0x80001bf0#32
  let r9 := ramWrite r8 (0x80fff814#32+145#32) (0#32) .b
  let c17 := c16.goto 0x80001bf4#32
  let r10 := ramWrite r9 (0x80fff814#32+146#32) (0#32) .b
  let c18 := c17.goto 0x80001bf8#32
  let c19 := c18.wr 10 (4096#32) 0x80001bfa#32
  let c20 := c19.wr 10 (4520#32) 0x80001bfe#32
  let c21 := c20.wr 10 (0x80fffd38#32) 0x80001c00#32
  let c22 := c21.wr 11 (0x80fff878#32) 0x80001c02#32
  let c23 := c22.wr 1 (0x7ffffc02#32) 0x80001c06#32
  let c24 := c23.wr 1 (0x80001c0a#32) 0x8000030e#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact RejectResponseCode.rr2147490748) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v2 : c.get 2=0x80ffeb90#32 := by simp [Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
    rw [exec_opimm,v2];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80001bc0#32).getLsbD 0=false;decide) RejectResponseCode.rr2147490752 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v9 : c1.get 9=0x80fff38f#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
    rw [exec_opimm,v9];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80001bc4#32).getLsbD 0=false;decide) RejectResponseCode.rr2147490756 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80001bc6#32).getLsbD 0=false;decide) RejectResponseCode.rr2147490758 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80001bc8#32).getLsbD 0=false;decide) RejectResponseCode.rr2147490760 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v10 : c4.get 10=1#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
    have v22 : c4.get 22=1#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
    rw [exec_branch,v10,v22,show taken .eq 1#32 1#32=true by decide +kernel]
    simp only [ite_true]
    rw [show c4.pc=0x80001bc8#32 from rfl]
    rw [show 0x80001bc8#32+8#32=0x80001bd0#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80001bd0#32).getLsbD 0=false;decide) RejectResponseCode.rr2147490768 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v8 : c5.get 8=0x80fff814#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 16 (by decide))
      (Memory.block_access object (off := 64) (by decide) (by decide)),tx];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80001bd2#32).getLsbD 0=false;decide) RejectResponseCode.rr2147490770 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v8 : c6.get 8=0x80fff814#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 17 (by decide))
      (Memory.block_access object (off := 68) (by decide) (by decide)),capacity];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x80001bd4#32).getLsbD 0=false;decide) RejectResponseCode.rr2147490772 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v8 : c7.get 8=0x80fff814#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 18 (by decide))
      (Memory.block_access object (off := 72) (by decide) (by decide)),ioWord];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,r1⟩ := by
    refine Quiet.step_of (by change (0x80001bd6#32).getLsbD 0=false;decide) RejectResponseCode.rr2147490774 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 r1 [],[]⟩
    have v8 : c8.get 8=0x80fff814#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
    have v10 : c8.get 10=0x80fff414#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
    rw [exec_store,v8,v10,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 27 (by decide)) (Memory.block_access object (off := 108) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,r1⟩ ⟨c10,r2⟩ := by
    refine Quiet.step_of (by change (0x80001bd8#32).getLsbD 0=false;decide) RejectResponseCode.rr2147490776 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) r1 0 [] [] = ⟨.ok c10 r2 [],[]⟩
    have v8 : c9.get 8=0x80fff814#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
    have v11 : c9.get 11=1024#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
    rw [exec_store,v8,v11,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 28 (by decide)) (Memory.block_access object (off := 112) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,r2⟩ ⟨c11,r3⟩ := by
    refine Quiet.step_of (by change (0x80001bda#32).getLsbD 0=false;decide) RejectResponseCode.rr2147490778 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) r2 0 [] [] = ⟨.ok c11 r3 [],[]⟩
    have v8 : c10.get 8=0x80fff814#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
    have v12 : c10.get 12=io := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
    rw [exec_store,v8,v12,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 31 (by decide)) (Memory.block_access object (off := 124) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,r3⟩ ⟨c12,r4⟩ := by
    refine Quiet.step_of (by change (0x80001bdc#32).getLsbD 0=false;decide) RejectResponseCode.rr2147490780 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) r3 0 [] [] = ⟨.ok c12 r4 [],[]⟩
    have v8 : c11.get 8=0x80fff814#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
    have v22 : c11.get 22=1#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
    rw [exec_store,v8,v22,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 32 (by decide)) (Memory.block_access object (off := 128) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,r4⟩ ⟨c13,r5⟩ := by
    refine Quiet.step_of (by change (0x80001be0#32).getLsbD 0=false;decide) RejectResponseCode.rr2147490784 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) r4 0 [] [] = ⟨.ok c13 r5 [],[]⟩
    have v8 : c12.get 8=0x80fff814#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
    rw [exec_store,v8,Core.get_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 33 (by decide)) (Memory.block_access object (off := 132) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,r5⟩ ⟨c14,r6⟩ := by
    refine Quiet.step_of (by change (0x80001be4#32).getLsbD 0=false;decide) RejectResponseCode.rr2147490788 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) r5 0 [] [] = ⟨.ok c14 r6 [],[]⟩
    have v8 : c13.get 8=0x80fff814#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
    rw [exec_store,v8,Core.get_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 34 (by decide)) (Memory.block_access object (off := 136) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,r6⟩ ⟨c15,r7⟩ := by
    refine Quiet.step_of (by change (0x80001be8#32).getLsbD 0=false;decide) RejectResponseCode.rr2147490792 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) r6 0 [] [] = ⟨.ok c15 r7 [],[]⟩
    have v8 : c14.get 8=0x80fff814#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
    have v27 : c14.get 27=status := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
    rw [exec_store,v8,v27,Quiet.interp_store_ram (B := B) (img := img) (w := .h) o
      (Memory.half_aligned 0x80fff814#32 70 (by decide)) (Memory.block_access object (off := 140) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t15 : Quiet.Step B img ⟨c15,r7⟩ ⟨c16,r8⟩ := by
    refine Quiet.step_of (by change (0x80001bec#32).getLsbD 0=false;decide) RejectResponseCode.rr2147490796 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) r7 0 [] [] = ⟨.ok c16 r8 [],[]⟩
    have v8 : c15.get 8=0x80fff814#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
    have v22 : c15.get 22=1#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
    rw [exec_store,v8,v22,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o
      (by exact Nat.mod_one _) (Memory.block_access object (off := 142) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t16 : Quiet.Step B img ⟨c16,r8⟩ ⟨c17,r9⟩ := by
    refine Quiet.step_of (by change (0x80001bf0#32).getLsbD 0=false;decide) RejectResponseCode.rr2147490800 fun o => ?_
    change Observed.interp B img o (exec c16 _ _) r8 0 [] [] = ⟨.ok c17 r9 [],[]⟩
    have v8 : c16.get 8=0x80fff814#32 := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
    rw [exec_store,v8,Core.get_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o
      (by exact Nat.mod_one _) (Memory.block_access object (off := 145) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t17 : Quiet.Step B img ⟨c17,r9⟩ ⟨c18,r10⟩ := by
    refine Quiet.step_of (by change (0x80001bf4#32).getLsbD 0=false;decide) RejectResponseCode.rr2147490804 fun o => ?_
    change Observed.interp B img o (exec c17 _ _) r9 0 [] [] = ⟨.ok c18 r10 [],[]⟩
    have v8 : c17.get 8=0x80fff814#32 := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
    rw [exec_store,v8,Core.get_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o
      (by exact Nat.mod_one _) (Memory.block_access object (off := 146) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t18 : Quiet.Step B img ⟨c18,r10⟩ ⟨c19,r10⟩ := by
    refine Quiet.step_of (by change (0x80001bf8#32).getLsbD 0=false;decide) RejectResponseCode.rr2147490808 fun o => ?_
    change Observed.interp B img o (exec c18 _ _) r10 0 [] [] = ⟨.ok c19 r10 [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t19 : Quiet.Step B img ⟨c19,r10⟩ ⟨c20,r10⟩ := by
    refine Quiet.step_of (by change (0x80001bfa#32).getLsbD 0=false;decide) RejectResponseCode.rr2147490810 fun o => ?_
    change Observed.interp B img o (exec c19 _ _) r10 0 [] [] = ⟨.ok c20 r10 [],[]⟩
    have v10 : c19.get 10=4096#32 := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
    rw [exec_opimm,v10];first | rfl | (rw [hp];rfl)
  have t20 : Quiet.Step B img ⟨c20,r10⟩ ⟨c21,r10⟩ := by
    refine Quiet.step_of (by change (0x80001bfe#32).getLsbD 0=false;decide) RejectResponseCode.rr2147490814 fun o => ?_
    change Observed.interp B img o (exec c20 _ _) r10 0 [] [] = ⟨.ok c21 r10 [],[]⟩
    have v10 : c20.get 10=4520#32 := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
    have v2 : c20.get 2=0x80ffeb90#32 := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
    rw [exec_op,v10,v2];first | rfl | (rw [hp];rfl)
  have t21 : Quiet.Step B img ⟨c21,r10⟩ ⟨c22,r10⟩ := by
    refine Quiet.step_of (by change (0x80001c00#32).getLsbD 0=false;decide) RejectResponseCode.rr2147490816 fun o => ?_
    change Observed.interp B img o (exec c21 _ _) r10 0 [] [] = ⟨.ok c22 r10 [],[]⟩
    have v9 : c21.get 9=0x80fff878#32 := by simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
    rw [exec_op,Core.get_zero,v9];first | rfl | (rw [hp];rfl)
  have t22 : Quiet.Step B img ⟨c22,r10⟩ ⟨c23,r10⟩ := by
    refine Quiet.step_of (by change (0x80001c02#32).getLsbD 0=false;decide) RejectResponseCode.rr2147490818 fun o => ?_
    change Observed.interp B img o (exec c22 _ _) r10 0 [] [] = ⟨.ok c23 r10 [],[]⟩
    rw [exec_auipc, show c22.pc=0x80001c02#32 from rfl]; rfl
  have t23 : Quiet.Step B img ⟨c23,r10⟩ ⟨c24,r10⟩ := by
    refine Quiet.step_of (by change (0x80001c06#32).getLsbD 0=false;decide) RejectResponseCode.rr2147490822 fun o => ?_
    change Observed.interp B img o (exec c23 _ _) r10 0 [] [] = ⟨.ok c24 r10 [],[]⟩
    have v1 : c23.get 1=0x7ffffc02#32 := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
    rw [exec_jalr,v1]
    change Observed.interp B img o (jump (c23.set 1 0x80001c0a#32) 0x8000030e#32) r10 0 [] []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c24,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.step t16 (.step t17 (.step t18 (.step t19 (.step t20 (.step t21 (.step t22 (.single t23))))))))))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
  · simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
  · simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
  · simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
  · simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
  · simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
  · simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus]
  · intro reg h9 h24 h18 h10 h11 h12 h1;simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,sp,fp,one,tag,replyStatus,h9,h24,h18,h10,h11,h12,h1]
end E5R.Thermostat.RejectResponseSetup
