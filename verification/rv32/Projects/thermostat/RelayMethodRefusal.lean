import Projects.thermostat.QuietDet
import Projects.thermostat.ReadBytes
import Projects.thermostat.RelayMethodCode
import Projects.thermostat.RouteMethodMath
import Projects.thermostat.Literal
import Projects.thermostat.MainRouterCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.RelayMethodRefusal
open E5R E5R.Thermostat
abbrev sp : Word := 0x80ffeb90#32

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (method : BitVec 8) (h2 : c.get 2=sp) (h8 : c.get 8=0x80fff814#32) (h10 : c.get 10=1#32) (h22 : c.get 22=1#32)
    (stack : Memory.Block B sp 5232) (futureRouter : ramRead ram 0x80fffa14#32 .w=0x80ffebd8#32)
    (futureRequest : ramRead ram 0x80fffa18#32 .w=0x80fff880#32) (methodByte : ram 0x80fff9f4#32=method)
    (routeMethod : ram 0x80ffec10#32=3#8) (notWanted : method≠3#8)
    (hp : c.pc=0x80001856#32) :
    ∃ d, Quiet.Steps B img 11 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x8000187c#32 ∧
      d.get 13=3#32 ∧ d.get 10=0x80fff880#32 ∧ d.get 12=0#32 ∧ d.get 6=ramRead ram (sp+20#32) .w ∧ (∀ r : Reg, r≠13 → r≠10 → r≠12 → r≠6 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.goto 0x8000185a#32
  let c2 := c1.wr 13 (0x80ffebd8#32) 0x8000185e#32
  let c3 := c2.wr 10 (0x80fff880#32) 0x80001862#32
  let c4 := c3.wr 12 (BitVec.ofNat 32 method.toNat) 0x80001866#32
  let c5 := c4.wr 13 (3#32) 0x8000186a#32
  let extra := c5.wr 6 (ramRead ram (sp+20#32) .w) 0x8000186c#32
  let c6 := extra.goto 0x80001870#32
  let c7 := c6.wr 12 ((BitVec.ofNat 32 method.toNat ^^^ 1#32)) 0x80001874#32
  let c8 := c7.wr 12 (((BitVec.ofNat 32 method.toNat ^^^ 1#32) ||| 3#32)) 0x80001876#32
  let c9 := c8.wr 12 (0#32) 0x8000187a#32
  let c10 := c9.goto 0x8000187c#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rl2147489878) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_branch,h10,h22,show taken .ne 1#32 1#32=false by decide +kernel];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x8000185a#32).getLsbD 0=false;decide) rl2147489882 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have value : c1.get 8=0x80fff814#32 := by simp [extra,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_load,value,show 0x80fff814#32+512#32=sp+3716#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 929 (by decide +kernel)) (Memory.block_access stack (off := 3716) (by decide) (by decide))]
    rw [show sp+3716#32=0x80fffa14#32 by decide +kernel,futureRouter];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x8000185e#32).getLsbD 0=false;decide) rl2147489886 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have value : c2.get 8=0x80fff814#32 := by simp [extra,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_load,value,show 0x80fff814#32+516#32=sp+3720#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 930 (by decide +kernel)) (Memory.block_access stack (off := 3720) (by decide) (by decide))]
    rw [show sp+3720#32=0x80fffa18#32 by decide +kernel,futureRequest];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80001862#32).getLsbD 0=false;decide) rl2147489890 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have value : c3.get 10=0x80fff880#32 := by simp [extra,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_load,value,show 0x80fff880#32+372#32=sp+3684#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3684) (by decide) (by decide))]
    change Observed.interp B img o (.done (c3.wr 12 (extend .b false (BitVec.ofNat 32 (ram 0x80fff9f4#32).toNat)) 0x80001866#32)) ram 0 [] []=_
    rw [methodByte,ReadBytes.extend_byte,←Memory.ofNat_width];rfl
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80001866#32).getLsbD 0=false;decide) rl2147489894 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have value : c4.get 13=0x80ffebd8#32 := by simp [extra,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_load,value,show 0x80ffebd8#32+56#32=sp+128#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 128) (by decide) (by decide))]
    change Observed.interp B img o (.done (c4.wr 13 (extend .b false (BitVec.ofNat 32 (ram 0x80ffec10#32).toNat)) 0x8000186a#32)) ram 0 [] []=_
    rw [routeMethod];first | rfl | (rw [hp];rfl)
  have extraStep : Quiet.Step B img ⟨c5,ram⟩ ⟨extra,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000186a#32).getLsbD 0=false;decide) rl2147489898 fun o => ?_
    change interp B img o (exec c5 _ _) ram 0 []=.ok extra ram []
    have base : c5.get 2=sp := by simp [extra,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2]
    rw [exec_load,base,interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 5 (by decide +kernel)) (Memory.block_access stack (off := 20) (by decide) (by decide))];rfl
  have t5 : Quiet.Step B img ⟨extra,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x8000186c#32).getLsbD 0=false;decide) rl2147489900 fun o => ?_
    change Observed.interp B img o (exec extra _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have route : extra.get 13=3#32 := by simp [extra,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    have requested : extra.get 12=BitVec.ofNat 32 method.toNat := by simp [extra,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    have apart : 3#32≠BitVec.ofNat 32 method.toNat := by
      have word : BitVec.ofNat 32 method.toNat≠BitVec.ofNat 32 (3#8).toNat := by simpa only [ne_eq,Literal.byte_injective] using notWanted
      exact Ne.symm word
    rw [exec_branch,route,requested,show taken .eq 3#32 (BitVec.ofNat 32 method.toNat)=false from decide_eq_false apart];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80001870#32).getLsbD 0=false;decide) rl2147489904 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have value : c6.get 12=BitVec.ofNat 32 method.toNat := by simp [extra,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_opimm,value];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x80001874#32).getLsbD 0=false;decide) rl2147489908 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have value : c7.get 12=(BitVec.ofNat 32 method.toNat ^^^ 1#32) := by simp [extra,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    have route : c7.get 13=3#32 := by simp [extra,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_op,value,route];rfl
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x80001876#32).getLsbD 0=false;decide) rl2147489910 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have value : c8.get 12=((BitVec.ofNat 32 method.toNat ^^^ 1#32) ||| 3#32) := by simp [extra,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_opimm,value,RouteMethodMath.refuse _ 3#32 (by decide)];rfl
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x8000187a#32).getLsbD 0=false;decide) rl2147489914 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have value : c9.get 12=0#32 := by simp [extra,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
    rw [exec_branch,value,Core.get_zero,show taken .ne 0#32 (0 : Word)=false by decide +kernel];first | rfl | (rw [hp];rfl)
  refine ⟨c10,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step extraStep (.step t5 (.step t6 (.step t7 (.step t8 (.single t9)))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [extra,c10,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
  · simp [extra,c10,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
  · simp [extra,c10,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
  · simp [extra,c10,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22]
  · intro reg h13 h10 h12 h6;simp [extra,c10,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h10,h22,h13,h10,h12,h6]
end E5R.Thermostat.RelayMethodRefusal
