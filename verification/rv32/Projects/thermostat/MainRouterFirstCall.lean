import Projects.thermostat.MainRouterCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainRouterFirstCall
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (path : Word) (pathLength : Nat) (h13 : c.get 13=0x80ffebf8#32) (h14 : c.get 14=0x80fff880#32)
    (stack : Memory.Block B 0x80ffeb90#32 5232)
    (statePattern : ramRead ram 0x80ffebf8#32 .w=0x80005b83#32)
    (stateLength : ramRead ram 0x80ffebfc#32 .w=6#32)
    (pathPointer : ramRead ram 0x80fff9b0#32 .w=path)
    (pathSize : ramRead ram 0x80fff9b4#32 .w=BitVec.ofNat 32 pathLength)
    (hp : c.pc=0x800013ba#32) :
    ∃ d, Quiet.Steps B img 7 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000283a#32 ∧
      d.get 10=0x80005b83#32 ∧ d.get 11=6#32 ∧ d.get 12=path ∧ d.get 13=BitVec.ofNat 32 pathLength ∧ d.get 14=0x80fff9d0#32 ∧ d.get 1=0x800013d2#32 ∧ (∀ r : Reg, r≠10 → r≠11 → r≠12 → r≠13 → r≠14 → r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (0x80005b83#32) 0x800013bc#32
  let c2 := c1.wr 11 (6#32) 0x800013be#32
  let c3 := c2.wr 12 (path) 0x800013c2#32
  let c4 := c3.wr 13 (BitVec.ofNat 32 pathLength) 0x800013c6#32
  let c5 := c4.wr 14 (0x80fff9d0#32) 0x800013ca#32
  let c6 := c5.wr 1 (0x800023ca#32) 0x800013ce#32
  let c7 := c6.wr 1 (0x800013d2#32) 0x8000283a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rt2147488698) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v13 : c.get 13=0x80ffebf8#32 := by simp [Core.wr_get_ne,Core.wr_get,h13,h14]
    rw [exec_load,v13,show 0x80ffebf8#32+0#32=0x80ffeb90#32+104#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned 0x80ffeb90#32 26 (by decide +kernel)) (Memory.block_access stack (off := 104) (by decide) (by decide))]
    change Observed.interp B img o (.done (c.wr 10 (extend .w true (ramRead ram 0x80ffebf8#32 .w)) (c.pc+2#32))) ram 0 [] []=_
    rw [statePattern];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800013bc#32).getLsbD 0=false;decide) rt2147488700 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v13 : c1.get 13=0x80ffebf8#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h13,h14]
    rw [exec_load,v13,show 0x80ffebf8#32+4#32=0x80ffeb90#32+108#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned 0x80ffeb90#32 27 (by decide +kernel)) (Memory.block_access stack (off := 108) (by decide) (by decide))]
    change Observed.interp B img o (.done (c1.wr 11 (extend .w true (ramRead ram 0x80ffebfc#32 .w)) (c1.pc+2#32))) ram 0 [] []=_
    rw [stateLength];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800013be#32).getLsbD 0=false;decide) rt2147488702 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v14 : c2.get 14=0x80fff880#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h13,h14]
    rw [exec_load,v14,show 0x80fff880#32+304#32=0x80ffeb90#32+3616#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned 0x80ffeb90#32 904 (by decide +kernel)) (Memory.block_access stack (off := 3616) (by decide) (by decide))]
    change Observed.interp B img o (.done (c2.wr 12 (extend .w true (ramRead ram 0x80fff9b0#32 .w)) (c2.pc+4#32))) ram 0 [] []=_
    rw [pathPointer];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x800013c2#32).getLsbD 0=false;decide) rt2147488706 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v14 : c3.get 14=0x80fff880#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h14]
    rw [exec_load,v14,show 0x80fff880#32+308#32=0x80ffeb90#32+3620#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned 0x80ffeb90#32 905 (by decide +kernel)) (Memory.block_access stack (off := 3620) (by decide) (by decide))]
    change Observed.interp B img o (.done (c3.wr 13 (extend .w true (ramRead ram 0x80fff9b4#32 .w)) (c3.pc+4#32))) ram 0 [] []=_
    rw [pathSize];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x800013c6#32).getLsbD 0=false;decide) rt2147488710 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v14 : c4.get 14=0x80fff880#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h14]
    rw [exec_opimm,v14]
    change Observed.interp B img o (.done (c4.wr 14 (0x80fff880#32+336#32) 0x800013ca#32)) ram 0 [] []=_
    rw [show 0x80fff880#32+336#32=0x80fff9d0#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x800013ca#32).getLsbD 0=false;decide) rt2147488714 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    rw [exec_auipc];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x800013ce#32).getLsbD 0=false;decide) rt2147488718 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v1 : c6.get 1=0x800023ca#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h14]
    rw [exec_jalr,v1]
    change Observed.interp B img o (jump (c6.set 1 0x800013d2#32) ((0x800023ca#32+1136#32) &&& ~~~1)) ram 0 [] []=_
    rw [show (0x800023ca#32+1136#32) &&& ~~~1=0x8000283a#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c7,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.single t6)))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h14]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h14]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h14]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h14]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h14]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h14]
  · intro reg h10 h11 h12 h13 h14 h1;simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h13,h14,h10,h11,h12,h13,h14,h1]
end E5R.Thermostat.MainRouterFirstCall
