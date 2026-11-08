import Projects.thermostat.MainRouterCode
import Projects.thermostat.QuietRam
import Projects.thermostat.WireCallerBytes
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainReadWireReturn
open E5R E5R.Thermostat
abbrev sp : Word := 0x80ffeb90#32

def memory (ram : Word → BitVec 8) (w : Word) :=
  ramWrite (ramWrite (ramWrite (ram) (sp+3968#32) (w) .b) (sp+3969#32) (w >>> 8) .b) (sp+3970#32) (w >>> 16) .h

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (w : Word) (h8 : c.get 8=0x80fff814#32) (h10 : c.get 10=w) (tag : byteOf w 0=4#8)
    (stack : Memory.Block B 0x80ffeb90#32 5232)
    (hp : c.pc=0x800019e8#32) :
    ∃ d, Quiet.Steps B img 9 ⟨c,ram⟩ ⟨d,memory ram w⟩ ∧ d.pc=0x80001a08#32 ∧
      d.get 11=w ∧ d.get 12=w >>> 8 ∧ d.get 10=w >>> 16 ∧ d.get 13=255#32 ∧ (∀ r : Reg, r≠11 → r≠12 → r≠10 → r≠13 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 11 (w) 0x800019ea#32
  let c2 := c1.wr 12 (4#32) 0x800019ee#32
  let c3 := c2.wr 10 (w >>> 16) 0x800019f0#32
  let c4 := c3.wr 13 (255#32) 0x800019f4#32
  let c5 := c4.goto 0x800019f8#32
  let c6 := c5.wr 12 (w >>> 8) 0x800019fc#32
  let r1 := ramWrite ram (sp+3968#32) (w) .b
  let c7 := c6.goto 0x80001a00#32
  let r2 := ramWrite r1 (sp+3969#32) (w >>> 8) .b
  let c8 := c7.goto 0x80001a04#32
  let r3 := ramWrite r2 (sp+3970#32) (w >>> 16) .h
  let c9 := c8.goto 0x80001a08#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rt2147490280) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v10 : c.get 10=w := by simp [Core.wr_get_ne,Core.wr_get,h8,h10]
    rw [exec_op,Core.get_zero,v10]
    change Observed.interp B img o (.done (c.wr 11 (0#32+w) (c.pc+2#32))) ram 0 [] []=_
    rw [BitVec.zero_add,hp];rfl
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800019ea#32).getLsbD 0=false;decide) rt2147490282 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v10 : c1.get 10=w := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    rw [exec_opimm,v10]
    change Observed.interp B img o (.done (c1.wr 12 (w &&& 255#32) 0x800019ee#32)) ram 0 [] []=_
    rw [WireCallerBytes.low_mask,tag];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800019ee#32).getLsbD 0=false;decide) rt2147490286 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v10 : c2.get 10=w := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    rw [exec_opimm,v10];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x800019f0#32).getLsbD 0=false;decide) rt2147490288 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x800019f4#32).getLsbD 0=false;decide) rt2147490292 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v12 : c4.get 12=4#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    have v13 : c4.get 13=255#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    rw [exec_branch,v12,v13];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x800019f8#32).getLsbD 0=false;decide) rt2147490296 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v11 : c5.get 11=w := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    rw [exec_opimm,v11];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,r1⟩ := by
    refine Quiet.step_of (by change (0x800019fc#32).getLsbD 0=false;decide) rt2147490300 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 r1 [],[]⟩
    have v8 : c6.get 8=0x80fff814#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    have v11 : c6.get 11=w := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    rw [exec_store,v8,v11,show 0x80fff814#32+764#32=sp+3968#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3968) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,r1⟩ ⟨c8,r2⟩ := by
    refine Quiet.step_of (by change (0x80001a00#32).getLsbD 0=false;decide) rt2147490304 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r1 0 [] [] = ⟨.ok c8 r2 [],[]⟩
    have v8 : c7.get 8=0x80fff814#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    have v12 : c7.get 12=w >>> 8 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    rw [exec_store,v8,v12,show 0x80fff814#32+765#32=sp+3969#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3969) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,r2⟩ ⟨c9,r3⟩ := by
    refine Quiet.step_of (by change (0x80001a04#32).getLsbD 0=false;decide) rt2147490308 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r2 0 [] [] = ⟨.ok c9 r3 [],[]⟩
    have v8 : c8.get 8=0x80fff814#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    have v10 : c8.get 10=w >>> 16 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
    rw [exec_store,v8,v10,show 0x80fff814#32+766#32=sp+3970#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned sp 1985 (by decide +kernel)) (Memory.block_access stack (off := 3970) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c9,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.single t8)))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10]
  · intro reg h11 h12 h10 h13;simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h11,h12,h10,h13]

/-- Exactly the already-verified enum byte stores, at this caller's real slot. -/
theorem memory_eq (ram : Word → BitVec 8) (w : Word) :
    memory ram w=WireCallerBytes.memory ram 0x80fffb06#32 w := by rfl
end E5R.Thermostat.MainReadWireReturn
