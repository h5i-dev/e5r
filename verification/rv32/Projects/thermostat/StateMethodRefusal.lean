import Projects.thermostat.ReadBytes
import Projects.thermostat.StateRefusalCode
import Projects.thermostat.RouteLiteralEnd
import Projects.thermostat.Literal
import Projects.thermostat.MainRouterCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.StateMethodRefusal
open E5R E5R.Thermostat
abbrev sp : Word := 0x80ffeb90#32

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (method : BitVec 8) (h8 : c.get 8=0x80fff814#32) (h10 : c.get 10=1#32) (h22 : c.get 22=1#32)
    (stack : Memory.Block B sp 5232) (futureRouter : ramRead ram 0x80fffac4#32 .w=0x80ffebf8#32)
    (futureRequest : ramRead ram 0x80fffac8#32 .w=0x80fff880#32) (methodByte : ram 0x80fff9f4#32=method)
    (routeGet : ram 0x80ffec00#32=0#8) (notGet : method≠0#8) (notHead : method≠1#8)
    (hp : c.pc=0x800013d2#32) :
    ∃ d, Quiet.Steps B img 12 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800013fe#32 ∧
      d.get 13=0#32 ∧ d.get 10=0x80fff880#32 ∧ d.get 12=0#32 ∧ d.get 9=2#32 ∧ (∀ r : Reg, r≠13 → r≠10 → r≠12 → r≠9 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x800013d6#32
  let c2 := c1.wr 13 (0x80ffebf8#32) 0x800013da#32
  let c3 := c2.wr 10 (0x80fff880#32) 0x800013de#32
  let c4 := c3.wr 12 (BitVec.ofNat 32 method.toNat) 0x800013e2#32
  let c5 := c4.wr 13 (0#32) 0x800013e6#32
  let c6 := c5.goto 0x800013ea#32
  let c7 := c6.wr 12 ((BitVec.ofNat 32 method.toNat ^^^ 1#32)) 0x800013ee#32
  let c8 := c7.wr 12 ((BitVec.ofNat 32 method.toNat ^^^ 1#32)) 0x800013f0#32
  let c9 := c8.wr 12 (0#32) 0x800013f4#32
  let c10 := c9.goto 0x800013f8#32
  let c11 := c10.wr 9 (2#32) 0x800013fa#32
  let c12 := c11.goto 0x800013fe#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rt2147488722) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_branch,h10,h22,show taken .ne 1#32 1#32=false by decide +kernel];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800013d6#32).getLsbD 0=false;decide) rt2147488726 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have value : c1.get 8=0x80fff814#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_load,value,show 0x80fff814#32+688#32=sp+3892#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 973 (by decide +kernel)) (Memory.block_access stack (off := 3892) (by decide) (by decide))]
    rw [show sp+3892#32=0x80fffac4#32 by decide +kernel,futureRouter];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800013da#32).getLsbD 0=false;decide) rt2147488730 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have value : c2.get 8=0x80fff814#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_load,value,show 0x80fff814#32+692#32=sp+3896#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 974 (by decide +kernel)) (Memory.block_access stack (off := 3896) (by decide) (by decide))]
    rw [show sp+3896#32=0x80fffac8#32 by decide +kernel,futureRequest];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x800013de#32).getLsbD 0=false;decide) rt2147488734 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have value : c3.get 10=0x80fff880#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_load,value,show 0x80fff880#32+372#32=sp+3684#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3684) (by decide) (by decide))]
    change Observed.interp B img o (.done (c3.wr 12 (extend .b false (BitVec.ofNat 32 (ram 0x80fff9f4#32).toNat)) 0x800013e2#32)) ram 0 [] []=_
    rw [methodByte,ReadBytes.extend_byte,←Memory.ofNat_width];rfl
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x800013e2#32).getLsbD 0=false;decide) rt2147488738 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have value : c4.get 13=0x80ffebf8#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_load,value,show 0x80ffebf8#32+8#32=sp+112#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 112) (by decide) (by decide))]
    change Observed.interp B img o (.done (c4.wr 13 (extend .b false (BitVec.ofNat 32 (ram 0x80ffec00#32).toNat)) 0x800013e6#32)) ram 0 [] []=_
    rw [routeGet];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x800013e6#32).getLsbD 0=false;decide) rt2147488742 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have route : c5.get 13=0#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    have requested : c5.get 12=BitVec.ofNat 32 method.toNat := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    have apart : 0#32≠BitVec.ofNat 32 method.toNat := by
      have word : BitVec.ofNat 32 method.toNat≠BitVec.ofNat 32 (0#8).toNat := by simpa only [ne_eq,Literal.byte_injective] using notGet
      exact Ne.symm word
    rw [exec_branch,route,requested,show taken .eq 0#32 (BitVec.ofNat 32 method.toNat)=false from decide_eq_false apart];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x800013ea#32).getLsbD 0=false;decide) sh2147488746 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have value : c6.get 12=BitVec.ofNat 32 method.toNat := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_opimm,value];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x800013ee#32).getLsbD 0=false;decide) sh2147488750 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have value : c7.get 12=(BitVec.ofNat 32 method.toNat ^^^ 1#32) := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    have route : c7.get 13=0#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_op,value,route];simp only [alu,BitVec.or_zero];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x800013f0#32).getLsbD 0=false;decide) sh2147488752 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have value : c8.get 12=(BitVec.ofNat 32 method.toNat ^^^ 1#32) := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    have apart : BitVec.ofNat 32 method.toNat≠1#32 := by
      have word : BitVec.ofNat 32 method.toNat≠BitVec.ofNat 32 (1#8).toNat := by simpa only [ne_eq,Literal.byte_injective] using notHead
      exact word
    rw [exec_opimm,value,RouteLiteralEnd.flag,ite_eq_right apart];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x800013f4#32).getLsbD 0=false;decide) sh2147488756 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have value : c9.get 12=0#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_branch,value,Core.get_zero,show taken .ne 0#32 (0 : Word)=false by decide +kernel];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x800013f8#32).getLsbD 0=false;decide) sr2147488760 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x800013fa#32).getLsbD 0=false;decide) sr2147488762 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    rw [exec_jal]
    change Observed.interp B img o (jump (c11.set 0 0x800013fc#32) 0x800013fe#32) ram 0 [] []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c12,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.single t11))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
  · intro reg h13 h10 h12 h9;simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22,h13,h10,h12,h9]
end E5R.Thermostat.StateMethodRefusal
