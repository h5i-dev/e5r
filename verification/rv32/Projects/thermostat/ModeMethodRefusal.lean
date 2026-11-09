import Projects.thermostat.ReadBytes
import Projects.thermostat.MainModeRouterCode
import Projects.thermostat.RouteMethodMath
import Projects.thermostat.Literal
import Projects.thermostat.MainRouterCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ModeMethodRefusal
open E5R E5R.Thermostat
abbrev sp : Word := 0x80ffeb90#32

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (method : BitVec 8) (h8 : c.get 8=0x80fff814#32) (h10 : c.get 10=1#32) (h22 : c.get 22=1#32)
    (stack : Memory.Block B sp 5232) (futureRouter : ramRead ram 0x80fffa40#32 .w=0x80ffebe0#32)
    (futureRequest : ramRead ram 0x80fffa44#32 .w=0x80fff880#32) (methodByte : ram 0x80fff9f4#32=method)
    (routeMethod : ram 0x80ffec0c#32=3#8) (notWanted : method≠3#8)
    (hp : c.pc=0x800014b6#32) :
    ∃ d, Quiet.Steps B img 12 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001832#32 ∧
      d.get 13=3#32 ∧ d.get 10=0x80fff880#32 ∧ d.get 12=0#32 ∧ d.get 9=2#32 ∧ (∀ r : Reg, r≠13 → r≠10 → r≠12 → r≠9 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x800014ba#32
  let c2 := c1.wr 13 (0x80ffebe0#32) 0x800014be#32
  let c3 := c2.wr 10 (0x80fff880#32) 0x800014c2#32
  let c4 := c3.wr 12 (BitVec.ofNat 32 method.toNat) 0x800014c6#32
  let c5 := c4.wr 13 (3#32) 0x800014ca#32
  let c6 := c5.wr 9 4#32 0x800014cc#32
  let c7 := c6.goto 0x800014d0#32
  let c8 := c7.wr 12 ((BitVec.ofNat 32 method.toNat ^^^ 1#32)) 0x800014d4#32
  let c9 := c8.wr 12 (((BitVec.ofNat 32 method.toNat ^^^ 1#32) ||| 3#32)) 0x800014d6#32
  let c10 := c9.wr 12 (0#32) 0x800014da#32
  let c11 := c10.goto 0x80001830#32
  let c12 := c11.wr 9 (2#32) 0x80001832#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact mo2147488950) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_branch,h10,h22,show taken .ne 1#32 1#32=false by decide +kernel];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800014ba#32).getLsbD 0=false;decide) mo2147488954 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have value : c1.get 8=0x80fff814#32 := by simp [c6,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_load,value,show 0x80fff814#32+556#32=sp+3760#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 940 (by decide +kernel)) (Memory.block_access stack (off := 3760) (by decide) (by decide))]
    rw [show sp+3760#32=0x80fffa40#32 by decide +kernel,futureRouter];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800014be#32).getLsbD 0=false;decide) mo2147488958 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have value : c2.get 8=0x80fff814#32 := by simp [c6,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_load,value,show 0x80fff814#32+560#32=sp+3764#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 941 (by decide +kernel)) (Memory.block_access stack (off := 3764) (by decide) (by decide))]
    rw [show sp+3764#32=0x80fffa44#32 by decide +kernel,futureRequest];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x800014c2#32).getLsbD 0=false;decide) mo2147488962 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have value : c3.get 10=0x80fff880#32 := by simp [c6,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_load,value,show 0x80fff880#32+372#32=sp+3684#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3684) (by decide) (by decide))]
    change Observed.interp B img o (.done (c3.wr 12 (extend .b false (BitVec.ofNat 32 (ram 0x80fff9f4#32).toNat)) 0x800014c6#32)) ram 0 [] []=_
    rw [methodByte,ReadBytes.extend_byte,←Memory.ofNat_width];rfl
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x800014c6#32).getLsbD 0=false;decide) mo2147488966 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have value : c4.get 13=0x80ffebe0#32 := by simp [c6,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_load,value,show 0x80ffebe0#32+44#32=sp+124#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 124) (by decide) (by decide))]
    change Observed.interp B img o (.done (c4.wr 13 (extend .b false (BitVec.ofNat 32 (ram 0x80ffec0c#32).toNat)) 0x800014ca#32)) ram 0 [] []=_
    rw [routeMethod];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x800014ca#32).getLsbD 0=false;decide) mo2147488970 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] []=⟨.ok c6 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];rfl
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x800014cc#32).getLsbD 0=false;decide) mo2147488972 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have route : c6.get 13=3#32 := by simp [c6,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    have requested : c6.get 12=BitVec.ofNat 32 method.toNat := by simp [c6,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    have apart : 3#32≠BitVec.ofNat 32 method.toNat := by
      have word : BitVec.ofNat 32 method.toNat≠BitVec.ofNat 32 (3#8).toNat := by simpa only [ne_eq,Literal.byte_injective] using notWanted
      exact Ne.symm word
    rw [exec_branch,route,requested,show taken .eq 3#32 (BitVec.ofNat 32 method.toNat)=false from decide_eq_false apart];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x800014d0#32).getLsbD 0=false;decide) mo2147488976 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have value : c7.get 12=BitVec.ofNat 32 method.toNat := by simp [c6,c7,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_opimm,value];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x800014d4#32).getLsbD 0=false;decide) mo2147488980 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have value : c8.get 12=(BitVec.ofNat 32 method.toNat ^^^ 1#32) := by simp [c6,c8,c7,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    have route : c8.get 13=3#32 := by simp [c6,c8,c7,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_op,value,route];rfl
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x800014d6#32).getLsbD 0=false;decide) mo2147488982 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have value : c9.get 12=((BitVec.ofNat 32 method.toNat ^^^ 1#32) ||| 3#32) := by simp [c6,c9,c8,c7,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_opimm,value,RouteMethodMath.refuse _ 3#32 (by decide)];rfl
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x800014da#32).getLsbD 0=false;decide) mo2147488986 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    have value : c10.get 12=0#32 := by simp [c6,c10,c9,c8,c7,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_branch,value,Core.get_zero,show taken .eq 0#32 (0 : Word)=true by decide +kernel,ite_eq_left rfl,
      show c10.pc=0x800014da#32 from rfl,show 0x800014da#32+854#32=0x80001830#32 by decide +kernel]
    rw [jump_ok _ _ (by decide)];rfl
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x80001830#32).getLsbD 0=false;decide) (show fetchDecode img 0x80001830#32=some (.opimm .add 9 0 2#32,2#32) from by exact PackedFetch.fetchDecode_of 2147489840#32 (by decide) (by decide) (bits := 0x00004489#32) (by decide +kernel) (by decide +kernel)) fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  refine ⟨c12,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.single t11))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c12,c11,c10,c9,c8,c7,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
  · simp [c6,c12,c11,c10,c9,c8,c7,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
  · simp [c6,c12,c11,c10,c9,c8,c7,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
  · simp [c6,c12,c11,c10,c9,c8,c7,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
  · intro reg h13 h10 h12 h9;simp [c6,c12,c11,c10,c9,c8,c7,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22,h13,h10,h12,h9]
end E5R.Thermostat.ModeMethodRefusal
