import Projects.thermostat.ReadBytes
import Projects.thermostat.MainTempRouterCode
import Projects.thermostat.RouteMethodMath
import Projects.thermostat.Literal
import Projects.thermostat.MainRouterCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.TempMethodRefusal
open E5R E5R.Thermostat
abbrev sp : Word := 0x80ffeb90#32

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (method : BitVec 8) (h8 : c.get 8=0x80fff814#32) (h10 : c.get 10=1#32) (h22 : c.get 22=1#32)
    (stack : Memory.Block B sp 5232) (futureRouter : ramRead ram 0x80fffa6c#32 .w=0x80ffebe8#32)
    (futureRequest : ramRead ram 0x80fffa70#32 .w=0x80fff880#32) (methodByte : ram 0x80fff9f4#32=method)
    (routeMethod : ram 0x80ffec08#32=2#8) (notWanted : method≠2#8)
    (hp : c.pc=0x8000146c#32) :
    ∃ d, Quiet.Steps B img 11 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001492#32 ∧
      d.get 13=2#32 ∧ d.get 10=0x80fff880#32 ∧ d.get 12=0#32 ∧ d.get 9=2#32 ∧ (∀ r : Reg, r≠13 → r≠10 → r≠12 → r≠9 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x80001470#32
  let c2 := c1.wr 13 (0x80ffebe8#32) 0x80001474#32
  let c3 := c2.wr 10 (0x80fff880#32) 0x80001478#32
  let c4 := c3.wr 12 (BitVec.ofNat 32 method.toNat) 0x8000147c#32
  let c5 := c4.wr 13 (2#32) 0x80001480#32
  let c6 := c5.goto 0x80001484#32
  let c7 := c6.wr 12 ((BitVec.ofNat 32 method.toNat ^^^ 1#32)) 0x80001488#32
  let c8 := c7.wr 12 (((BitVec.ofNat 32 method.toNat ^^^ 1#32) ||| 2#32)) 0x8000148a#32
  let c9 := c8.wr 12 (0#32) 0x8000148e#32
  let c10 := c9.goto 0x80001490#32
  let c11 := c10.wr 9 (2#32) 0x80001492#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact tc2147488876) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_branch,h10,h22,show taken .ne 1#32 1#32=false by decide +kernel];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80001470#32).getLsbD 0=false;decide) tc2147488880 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have value : c1.get 8=0x80fff814#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_load,value,show 0x80fff814#32+600#32=sp+3804#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 951 (by decide +kernel)) (Memory.block_access stack (off := 3804) (by decide) (by decide))]
    rw [show sp+3804#32=0x80fffa6c#32 by decide +kernel,futureRouter];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80001474#32).getLsbD 0=false;decide) tc2147488884 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have value : c2.get 8=0x80fff814#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_load,value,show 0x80fff814#32+604#32=sp+3808#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 952 (by decide +kernel)) (Memory.block_access stack (off := 3808) (by decide) (by decide))]
    rw [show sp+3808#32=0x80fffa70#32 by decide +kernel,futureRequest];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80001478#32).getLsbD 0=false;decide) tc2147488888 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have value : c3.get 10=0x80fff880#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_load,value,show 0x80fff880#32+372#32=sp+3684#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3684) (by decide) (by decide))]
    change Observed.interp B img o (.done (c3.wr 12 (extend .b false (BitVec.ofNat 32 (ram 0x80fff9f4#32).toNat)) 0x8000147c#32)) ram 0 [] []=_
    rw [methodByte,ReadBytes.extend_byte,←Memory.ofNat_width];rfl
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x8000147c#32).getLsbD 0=false;decide) tc2147488892 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have value : c4.get 13=0x80ffebe8#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_load,value,show 0x80ffebe8#32+32#32=sp+120#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 120) (by decide) (by decide))]
    change Observed.interp B img o (.done (c4.wr 13 (extend .b false (BitVec.ofNat 32 (ram 0x80ffec08#32).toNat)) 0x80001480#32)) ram 0 [] []=_
    rw [routeMethod];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80001480#32).getLsbD 0=false;decide) tc2147488896 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have route : c5.get 13=2#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    have requested : c5.get 12=BitVec.ofNat 32 method.toNat := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    have apart : 2#32≠BitVec.ofNat 32 method.toNat := by
      have word : BitVec.ofNat 32 method.toNat≠BitVec.ofNat 32 (2#8).toNat := by simpa only [ne_eq,Literal.byte_injective] using notWanted
      exact Ne.symm word
    rw [exec_branch,route,requested,show taken .eq 2#32 (BitVec.ofNat 32 method.toNat)=false from decide_eq_false apart];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80001484#32).getLsbD 0=false;decide) tc2147488900 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have value : c6.get 12=BitVec.ofNat 32 method.toNat := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_opimm,value];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x80001488#32).getLsbD 0=false;decide) tc2147488904 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have value : c7.get 12=(BitVec.ofNat 32 method.toNat ^^^ 1#32) := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    have route : c7.get 13=2#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_op,value,route];rfl
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x8000148a#32).getLsbD 0=false;decide) tc2147488906 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have value : c8.get 12=((BitVec.ofNat 32 method.toNat ^^^ 1#32) ||| 2#32) := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_opimm,value,RouteMethodMath.refuse _ 2#32 (by decide)];rfl
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x8000148e#32).getLsbD 0=false;decide) tc2147488910 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have value : c9.get 12=0#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_branch,value,Core.get_zero,show taken .ne 0#32 (0 : Word)=false by decide +kernel];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x80001490#32).getLsbD 0=false;decide) tc2147488912 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  refine ⟨c11,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.single t10)))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
  · intro reg h13 h10 h12 h9;simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22,h13,h10,h12,h9]
end E5R.Thermostat.TempMethodRefusal
