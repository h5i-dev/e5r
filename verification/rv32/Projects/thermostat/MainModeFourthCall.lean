import Projects.thermostat.MainModeRouterCode
import Projects.thermostat.QuietRam
import Projects.thermostat.FrameOffsets
import Projects.thermostat.ViewFrame
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainModeFourthCall
open E5R E5R.Thermostat
abbrev sp : Word := 0x80ffeb90#32

def memory (ram : Word → BitVec 8) (path : Word) :=
  ramWrite (ram) (sp+3824#32) (1#32) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (path : Word) (h2 : c.get 2=0x80ffeb90#32) (h8 : c.get 8=0x80fff814#32) (h10 : c.get 10=0#32) (h22 : c.get 22=1#32)
    (stack : Memory.Block B 0x80ffeb90#32 5232)
    (futureRouter : ramRead ram 2164259392#32 .w=2164255712#32) (futureRequest : ramRead ram 2164259396#32 .w=0x80fff880#32)
    (patternPointer : ramRead ram 2164255712#32 .w=2147507095#32) (patternLength : ramRead ram 2164255716#32 .w=5#32)
    (requestPath : ramRead ram 0x80fff9b0#32 .w=path) (requestLength : ramRead ram 0x80fff9b4#32 .w=5#32)
    (hp : c.pc=0x8000146c#32) :
    ∃ d, Quiet.Steps B img 11 ⟨c,ram⟩ ⟨d,memory ram path⟩ ∧ d.pc=0x8000283a#32 ∧
      d.get 11=5#32 ∧ d.get 14=2164259280#32 ∧ d.get 10=2147507095#32 ∧ d.get 12=path ∧ d.get 13=5#32 ∧ d.get 1=2147488950#32 ∧ (∀ r : Reg, r≠11 → r≠14 → r≠10 → r≠12 → r≠13 → r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80001492#32
  let c2 := c1.wr 11 (2164255712#32) 0x80001496#32
  let c3 := c2.wr 14 (2164258944#32) 0x8000149a#32
  let r1 := ramWrite ram (sp+3824#32) (1#32) .b
  let c4 := c3.goto 0x8000149e#32
  let c5 := c4.wr 10 (2147507095#32) 0x800014a0#32
  let c6 := c5.wr 11 (5#32) 0x800014a2#32
  let c7 := c6.wr 12 (path) 0x800014a6#32
  let c8 := c7.wr 13 (5#32) 0x800014aa#32
  let c9 := c8.wr 14 (2164259280#32) 0x800014ae#32
  let c10 := c9.wr 1 (2147493038#32) 0x800014b2#32
  let c11 := c10.wr 1 (2147488950#32) 0x8000283a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact mo2147488876) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v10 : c.get 10=0#32 := by simp [Core.wr_get_ne,Core.wr_get,h2,h8,h10,h22]
    have v22 : c.get 22=1#32 := by simp [Core.wr_get_ne,Core.wr_get,h2,h8,h10,h22]
    rw [exec_branch,v10,v22,show taken .ne 0#32 1#32=true by decide +kernel]
    rw [ite_eq_left rfl,hp,show 2147488876#32+38#32=2147488914#32 by decide +kernel]
    change Observed.interp B img o (jump c 2147488914#32) ram 0 [] []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80001492#32).getLsbD 0=false;decide) mo2147488914 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v8 : c1.get 8=2164258836#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h22]
    rw [exec_load,v8,show 2164258836#32+556#32=sp+3760#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 940 (by decide +kernel)) (Memory.block_access stack (off := 3760) (by decide) (by decide))]
    have kept : ramRead ram (sp+3760#32) .w=ramRead ram (sp+3760#32) .w := by
      rfl
    change Observed.interp B img o (.done (c1.wr 11 (extend .w true (ramRead ram (sp+3760#32) .w)) (c1.pc+4#32))) ram 0 [] []=_
    rw [kept,show sp+3760#32=2164259392#32 by decide +kernel,futureRouter];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80001496#32).getLsbD 0=false;decide) mo2147488918 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v8 : c2.get 8=2164258836#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h22]
    rw [exec_load,v8,show 2164258836#32+560#32=sp+3764#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 941 (by decide +kernel)) (Memory.block_access stack (off := 3764) (by decide) (by decide))]
    have kept : ramRead ram (sp+3764#32) .w=ramRead ram (sp+3764#32) .w := by
      rfl
    change Observed.interp B img o (.done (c2.wr 14 (extend .w true (ramRead ram (sp+3764#32) .w)) (c2.pc+4#32))) ram 0 [] []=_
    rw [kept,show sp+3764#32=2164259396#32 by decide +kernel,futureRequest];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,r1⟩ := by
    refine Quiet.step_of (by change (0x8000149a#32).getLsbD 0=false;decide) mo2147488922 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 r1 [],[]⟩
    have v8 : c3.get 8=2164258836#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h22]
    have v22 : c3.get 22=1#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h22]
    rw [exec_store,v8,v22,show 2164258836#32+620#32=sp+3824#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3824) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r1⟩ ⟨c5,r1⟩ := by
    refine Quiet.step_of (by change (0x8000149e#32).getLsbD 0=false;decide) mo2147488926 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r1 0 [] [] = ⟨.ok c5 r1 [],[]⟩
    have v11 : c4.get 11=2164255712#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h22]
    rw [exec_load,v11,show 2164255712#32+0#32=sp+80#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 20 (by decide +kernel)) (Memory.block_access stack (off := 80) (by decide) (by decide))]
    have kept : ramRead r1 (sp+80#32) .w=ramRead ram (sp+80#32) .w := by
      exact FrameOffsets.word ram sp 1#32 80 3824 .b (by decide) (by decide) (by decide)
    change Observed.interp B img o (.done (c4.wr 10 (extend .w true (ramRead r1 (sp+80#32) .w)) (c4.pc+2#32))) r1 0 [] []=_
    rw [kept,show sp+80#32=2164255712#32 by decide +kernel,patternPointer];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r1⟩ ⟨c6,r1⟩ := by
    refine Quiet.step_of (by change (0x800014a0#32).getLsbD 0=false;decide) mo2147488928 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r1 0 [] [] = ⟨.ok c6 r1 [],[]⟩
    have v11 : c5.get 11=2164255712#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h22]
    rw [exec_load,v11,show 2164255712#32+4#32=sp+84#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 21 (by decide +kernel)) (Memory.block_access stack (off := 84) (by decide) (by decide))]
    have kept : ramRead r1 (sp+84#32) .w=ramRead ram (sp+84#32) .w := by
      exact FrameOffsets.word ram sp 1#32 84 3824 .b (by decide) (by decide) (by decide)
    change Observed.interp B img o (.done (c5.wr 11 (extend .w true (ramRead r1 (sp+84#32) .w)) (c5.pc+2#32))) r1 0 [] []=_
    rw [kept,show sp+84#32=2164255716#32 by decide +kernel,patternLength];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r1⟩ ⟨c7,r1⟩ := by
    refine Quiet.step_of (by change (0x800014a2#32).getLsbD 0=false;decide) mo2147488930 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r1 0 [] [] = ⟨.ok c7 r1 [],[]⟩
    have v14 : c6.get 14=2164258944#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h22]
    rw [exec_load,v14,show 2164258944#32+304#32=sp+3616#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 904 (by decide +kernel)) (Memory.block_access stack (off := 3616) (by decide) (by decide))]
    have kept : ramRead r1 (sp+3616#32) .w=ramRead ram (sp+3616#32) .w := by
      exact FrameOffsets.word ram sp 1#32 3616 3824 .b (by decide) (by decide) (by decide)
    change Observed.interp B img o (.done (c6.wr 12 (extend .w true (ramRead r1 (sp+3616#32) .w)) (c6.pc+4#32))) r1 0 [] []=_
    rw [kept,show sp+3616#32=2164259248#32 by decide +kernel,requestPath];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,r1⟩ ⟨c8,r1⟩ := by
    refine Quiet.step_of (by change (0x800014a6#32).getLsbD 0=false;decide) mo2147488934 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r1 0 [] [] = ⟨.ok c8 r1 [],[]⟩
    have v14 : c7.get 14=2164258944#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h22]
    rw [exec_load,v14,show 2164258944#32+308#32=sp+3620#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 905 (by decide +kernel)) (Memory.block_access stack (off := 3620) (by decide) (by decide))]
    have kept : ramRead r1 (sp+3620#32) .w=ramRead ram (sp+3620#32) .w := by
      exact FrameOffsets.word ram sp 1#32 3620 3824 .b (by decide) (by decide) (by decide)
    change Observed.interp B img o (.done (c7.wr 13 (extend .w true (ramRead r1 (sp+3620#32) .w)) (c7.pc+4#32))) r1 0 [] []=_
    rw [kept,show sp+3620#32=2164259252#32 by decide +kernel,requestLength];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,r1⟩ ⟨c9,r1⟩ := by
    refine Quiet.step_of (by change (0x800014aa#32).getLsbD 0=false;decide) mo2147488938 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r1 0 [] [] = ⟨.ok c9 r1 [],[]⟩
    have v14 : c8.get 14=2164258944#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h22]
    rw [exec_opimm,v14,show alu .add 2164258944#32 336#32=2164259280#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,r1⟩ ⟨c10,r1⟩ := by
    refine Quiet.step_of (by change (0x800014ae#32).getLsbD 0=false;decide) mo2147488942 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) r1 0 [] [] = ⟨.ok c10 r1 [],[]⟩
    rw [exec_auipc];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,r1⟩ ⟨c11,r1⟩ := by
    refine Quiet.step_of (by change (0x800014b2#32).getLsbD 0=false;decide) mo2147488946 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) r1 0 [] [] = ⟨.ok c11 r1 [],[]⟩
    have v1 : c10.get 1=2147493038#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h22]
    rw [exec_jalr,v1]
    change Observed.interp B img o (jump (c10.set 1 2147488950#32) 2147493946#32) r1 0 [] []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c11,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.single t10)))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h22]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h22]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h22]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h22]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h22]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h22]
  · intro reg h11 h14 h10 h12 h13 h1;simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h10,h22,h11,h14,h10,h12,h13,h1]

theorem frame (ram : Word → BitVec 8) (path : Word) (off size : Nat) (bound : off+size≤5232)
    (apart : off+size≤3824 ∨ 3825≤off) : ViewFrame.Region ram (memory ram path) (sp+BitVec.ofNat 32 off) size := by
  intro i
  unfold memory
  apply StoreBytes.frame
  intro j
  exact FrameOffsets.ne sp off 3824 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<1 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<1 at hj;rcases apart with h|h <;>omega)
end E5R.Thermostat.MainModeFourthCall
