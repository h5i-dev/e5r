-- Common candidate call after path/method refusal; preserves the actual404/405 flag.
-- Generalized actual request-length load; route pattern constants are unchanged.
import Projects.thermostat.MainTempRouterCode
import Projects.thermostat.QuietRam
import Projects.thermostat.FrameOffsets
import Projects.thermostat.ViewFrame
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.RouteSecondCore
open E5R E5R.Thermostat
abbrev sp : Word := 0x80ffeb90#32

def memory (ram : Word → BitVec 8) (path : Word) :=
  ramWrite (ram) (sp+3912#32) (1#32) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (path pathSize : Word) (h2 : c.get 2=0x80ffeb90#32) (h8 : c.get 8=0x80fff814#32) (h22 : c.get 22=1#32)
    (stack : Memory.Block B 0x80ffeb90#32 5232)
    (futureRouter : ramRead ram 2164259480#32 .w=2164255728#32) (futureRequest : ramRead ram 2164259484#32 .w=0x80fff880#32)
    (patternPointer : ramRead ram 2164255728#32 .w=2147507081#32) (patternLength : ramRead ram 2164255732#32 .w=9#32)
    (requestPath : ramRead ram 0x80fff9b0#32 .w=path) (requestLength : ramRead ram 0x80fff9b4#32 .w=pathSize)
    (hp : c.pc=0x800013fe#32) :
    ∃ d, Quiet.Steps B img 10 ⟨c,ram⟩ ⟨d,memory ram path⟩ ∧ d.pc=0x8000283a#32 ∧
      d.get 9=c.get 9 ∧ d.get 11=9#32 ∧ d.get 14=2164259280#32 ∧ d.get 10=2147507081#32 ∧ d.get 12=path ∧ d.get 13=pathSize ∧ d.get 1=2147488802#32 ∧ (∀ r : Reg, r≠9 → r≠11 → r≠14 → r≠10 → r≠12 → r≠13 → r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c3 := c.wr 11 (2164255728#32) 0x80001402#32
  let c4 := c3.wr 14 (2164258944#32) 0x80001406#32
  let r1 := ramWrite ram (sp+3912#32) (1#32) .b
  let c5 := c4.goto 0x8000140a#32
  let c6 := c5.wr 10 (2147507081#32) 0x8000140c#32
  let c7 := c6.wr 11 (9#32) 0x8000140e#32
  let c8 := c7.wr 12 (path) 0x80001412#32
  let c9 := c8.wr 13 (pathSize) 0x80001416#32
  let c10 := c9.wr 14 (2164259280#32) 0x8000141a#32
  let c11 := c10.wr 1 (2147492890#32) 0x8000141e#32
  let c12 := c11.wr 1 (2147488802#32) 0x8000283a#32
  have t2 : Quiet.Step B img ⟨c,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact tc2147488766) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v8 : c.get 8=2164258836#32 := by simp [Core.wr_get_ne,Core.wr_get,h2,h8,h22]
    rw [exec_load,v8,show 2164258836#32+644#32=sp+3848#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 962 (by decide +kernel)) (Memory.block_access stack (off := 3848) (by decide) (by decide))]
    have kept : ramRead ram (sp+3848#32) .w=ramRead ram (sp+3848#32) .w := by
      rfl
    change Observed.interp B img o (.done (c.wr 11 (extend .w true (ramRead ram (sp+3848#32) .w)) (c.pc+4#32))) ram 0 [] []=_
    rw [kept,show sp+3848#32=2164259480#32 by decide +kernel,futureRouter];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80001402#32).getLsbD 0=false;decide) tc2147488770 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v8 : c3.get 8=2164258836#32 := by simp [c3,Core.wr_get_ne,Core.wr_get,h2,h8,h22]
    rw [exec_load,v8,show 2164258836#32+648#32=sp+3852#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 963 (by decide +kernel)) (Memory.block_access stack (off := 3852) (by decide) (by decide))]
    have kept : ramRead ram (sp+3852#32) .w=ramRead ram (sp+3852#32) .w := by
      rfl
    change Observed.interp B img o (.done (c3.wr 14 (extend .w true (ramRead ram (sp+3852#32) .w)) (c3.pc+4#32))) ram 0 [] []=_
    rw [kept,show sp+3852#32=2164259484#32 by decide +kernel,futureRequest];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,r1⟩ := by
    refine Quiet.step_of (by change (0x80001406#32).getLsbD 0=false;decide) tc2147488774 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 r1 [],[]⟩
    have v8 : c4.get 8=2164258836#32 := by simp [c4,c3,Core.wr_get_ne,Core.wr_get,h2,h8,h22]
    have v22 : c4.get 22=1#32 := by simp [c4,c3,Core.wr_get_ne,Core.wr_get,h2,h8,h22]
    rw [exec_store,v8,v22,show 2164258836#32+708#32=sp+3912#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3912) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r1⟩ ⟨c6,r1⟩ := by
    refine Quiet.step_of (by change (0x8000140a#32).getLsbD 0=false;decide) tc2147488778 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r1 0 [] [] = ⟨.ok c6 r1 [],[]⟩
    have v11 : c5.get 11=2164255728#32 := by simp [c5,c4,c3,Core.wr_get_ne,Core.wr_get,h2,h8,h22]
    rw [exec_load,v11,show 2164255728#32+0#32=sp+96#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 24 (by decide +kernel)) (Memory.block_access stack (off := 96) (by decide) (by decide))]
    have kept : ramRead r1 (sp+96#32) .w=ramRead ram (sp+96#32) .w := by
      exact FrameOffsets.word ram sp 1#32 96 3912 .b (by decide) (by decide) (by decide)
    change Observed.interp B img o (.done (c5.wr 10 (extend .w true (ramRead r1 (sp+96#32) .w)) (c5.pc+2#32))) r1 0 [] []=_
    rw [kept,show sp+96#32=2164255728#32 by decide +kernel,patternPointer];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r1⟩ ⟨c7,r1⟩ := by
    refine Quiet.step_of (by change (0x8000140c#32).getLsbD 0=false;decide) tc2147488780 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r1 0 [] [] = ⟨.ok c7 r1 [],[]⟩
    have v11 : c6.get 11=2164255728#32 := by simp [c6,c5,c4,c3,Core.wr_get_ne,Core.wr_get,h2,h8,h22]
    rw [exec_load,v11,show 2164255728#32+4#32=sp+100#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 25 (by decide +kernel)) (Memory.block_access stack (off := 100) (by decide) (by decide))]
    have kept : ramRead r1 (sp+100#32) .w=ramRead ram (sp+100#32) .w := by
      exact FrameOffsets.word ram sp 1#32 100 3912 .b (by decide) (by decide) (by decide)
    change Observed.interp B img o (.done (c6.wr 11 (extend .w true (ramRead r1 (sp+100#32) .w)) (c6.pc+2#32))) r1 0 [] []=_
    rw [kept,show sp+100#32=2164255732#32 by decide +kernel,patternLength];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,r1⟩ ⟨c8,r1⟩ := by
    refine Quiet.step_of (by change (0x8000140e#32).getLsbD 0=false;decide) tc2147488782 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r1 0 [] [] = ⟨.ok c8 r1 [],[]⟩
    have v14 : c7.get 14=2164258944#32 := by simp [c7,c6,c5,c4,c3,Core.wr_get_ne,Core.wr_get,h2,h8,h22]
    rw [exec_load,v14,show 2164258944#32+304#32=sp+3616#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 904 (by decide +kernel)) (Memory.block_access stack (off := 3616) (by decide) (by decide))]
    have kept : ramRead r1 (sp+3616#32) .w=ramRead ram (sp+3616#32) .w := by
      exact FrameOffsets.word ram sp 1#32 3616 3912 .b (by decide) (by decide) (by decide)
    change Observed.interp B img o (.done (c7.wr 12 (extend .w true (ramRead r1 (sp+3616#32) .w)) (c7.pc+4#32))) r1 0 [] []=_
    rw [kept,show sp+3616#32=2164259248#32 by decide +kernel,requestPath];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,r1⟩ ⟨c9,r1⟩ := by
    refine Quiet.step_of (by change (0x80001412#32).getLsbD 0=false;decide) tc2147488786 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r1 0 [] [] = ⟨.ok c9 r1 [],[]⟩
    have v14 : c8.get 14=2164258944#32 := by simp [c8,c7,c6,c5,c4,c3,Core.wr_get_ne,Core.wr_get,h2,h8,h22]
    rw [exec_load,v14,show 2164258944#32+308#32=sp+3620#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 905 (by decide +kernel)) (Memory.block_access stack (off := 3620) (by decide) (by decide))]
    have kept : ramRead r1 (sp+3620#32) .w=ramRead ram (sp+3620#32) .w := by
      exact FrameOffsets.word ram sp 1#32 3620 3912 .b (by decide) (by decide) (by decide)
    change Observed.interp B img o (.done (c8.wr 13 (extend .w true (ramRead r1 (sp+3620#32) .w)) (c8.pc+4#32))) r1 0 [] []=_
    rw [kept,show sp+3620#32=2164259252#32 by decide +kernel,requestLength];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,r1⟩ ⟨c10,r1⟩ := by
    refine Quiet.step_of (by change (0x80001416#32).getLsbD 0=false;decide) tc2147488790 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) r1 0 [] [] = ⟨.ok c10 r1 [],[]⟩
    have v14 : c9.get 14=2164258944#32 := by simp [c9,c8,c7,c6,c5,c4,c3,Core.wr_get_ne,Core.wr_get,h2,h8,h22]
    rw [exec_opimm,v14,show alu .add 2164258944#32 336#32=2164259280#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,r1⟩ ⟨c11,r1⟩ := by
    refine Quiet.step_of (by change (0x8000141a#32).getLsbD 0=false;decide) tc2147488794 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) r1 0 [] [] = ⟨.ok c11 r1 [],[]⟩
    rw [exec_auipc];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,r1⟩ ⟨c12,r1⟩ := by
    refine Quiet.step_of (by change (0x8000141e#32).getLsbD 0=false;decide) tc2147488798 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) r1 0 [] [] = ⟨.ok c12 r1 [],[]⟩
    have v1 : c11.get 1=2147492890#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,Core.wr_get_ne,Core.wr_get,h2,h8,h22]
    rw [exec_jalr,v1]
    change Observed.interp B img o (jump (c11.set 1 2147488802#32) 2147493946#32) r1 0 [] []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c12,.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.single t11))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,Core.wr_get_ne,Core.wr_get,h2,h8,h22]
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,Core.wr_get_ne,Core.wr_get,h2,h8,h22]
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,Core.wr_get_ne,Core.wr_get,h2,h8,h22]
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,Core.wr_get_ne,Core.wr_get,h2,h8,h22]
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,Core.wr_get_ne,Core.wr_get,h2,h8,h22]
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,Core.wr_get_ne,Core.wr_get,h2,h8,h22]
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,Core.wr_get_ne,Core.wr_get,h2,h8,h22]
  · intro reg h9 h11 h14 h10 h12 h13 h1;simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,Core.wr_get_ne,Core.wr_get,h2,h8,h22,h9,h11,h14,h10,h12,h13,h1]

theorem frame (ram : Word → BitVec 8) (path : Word) (off size : Nat) (bound : off+size≤5232)
    (apart : off+size≤3912 ∨ 3913≤off) : ViewFrame.Region ram (memory ram path) (sp+BitVec.ofNat 32 off) size := by
  intro i
  unfold memory
  apply StoreBytes.frame
  intro j
  exact FrameOffsets.ne sp off 3912 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;change j.val<1 at this;omega) (by have := i.isLt;have hj := j.isLt;change j.val<1 at hj;rcases apart with h|h <;>omega)
end E5R.Thermostat.RouteSecondCore
