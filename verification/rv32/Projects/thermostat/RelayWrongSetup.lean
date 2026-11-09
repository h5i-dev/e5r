import Projects.thermostat.RelayWrongSetupCode
import Projects.thermostat.MainWriteFlags
import Projects.thermostat.QuietDet
import Projects.thermostat.FrameOffsets
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 5000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.RelayWrongSetup
open E5R E5R.Thermostat
abbrev sp : Word := 2164255632#32
abbrev fp : Word := 2164258836#32

/-- Actual final not-found/wrong-method selection, with the real poll flag
    store and status bytes. The connection-close byte is not forced here. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (h2 : c.get 2=sp) (h8 : c.get 8=fp)
    (stack : Memory.Block B sp 5232) (pc : c.pc=2147489916#32) :
    ∃ d,Quiet.Steps B img 10 ⟨c,ram⟩ ⟨d,MainWriteFlags.memory ram fp⟩ ∧ d.pc=2147489576#32 ∧
      d.get 10=405#32 ∧ d.get 11=0#32 ∧ d.get 20=0#32 ∧ d.get 13=0#32 ∧ d.get 12=1#32 ∧
      d.get 9=2164258936#32 ∧ d.get 24=4294967294#32 ∧ d.get 6=c.get 6 ∧
      (∀ r : Reg,r≠11 → r≠20 → r≠13 → r≠9 → r≠12 → r≠10 → r≠24 → r≠6 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 11 (0#32) 2147489918#32
  let c2 := c1.wr 20 (0#32) 2147489920#32
  let c3 := c2.wr 13 (0#32) 2147489922#32
  let c4 := c3.wr 12 (1#32) 2147489924#32
  let c5 := c4.goto 2147489928#32
  let c6 := c5.wr 10 (405#32) 2147489932#32
  let c7 := c6.wr 9 ((sp+2047#32)) 2147489936#32
  let c8 := c7.wr 9 (2164258936#32) 2147489940#32
  let c9 := c8.wr 24 (4294967294#32) 2147489942#32
  let c10 := c9.goto 2147489576#32
  let changed := MainWriteFlags.memory ram fp
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [pc];decide) (by rw [pc];exact wm2147489916) fun o => ?_
    change interp B img o (exec c _ _) ram 0 []=.ok c1 ram []
    have value : c.get 0=0#32 := by simp [Core.wr_get_ne,Core.wr_get,h2,h8,h8]
    rw [exec_opimm,value,show alu .add 0#32 0#32=0#32 by decide +kernel]
    rw [pc]
    rfl
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (2147489918#32).getLsbD 0=false;decide) wm2147489918 fun o => ?_
    change interp B img o (exec c1 _ _) ram 0 []=.ok c2 ram []
    have value : c1.get 0=0#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h8,h8]
    rw [exec_opimm,value,show alu .add 0#32 0#32=0#32 by decide +kernel]
    rfl
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (2147489920#32).getLsbD 0=false;decide) wm2147489920 fun o => ?_
    change interp B img o (exec c2 _ _) ram 0 []=.ok c3 ram []
    have value : c2.get 0=0#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h8]
    rw [exec_opimm,value,show alu .add 0#32 0#32=0#32 by decide +kernel]
    rfl
  have t4 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (2147489922#32).getLsbD 0=false;decide) wm2147489922 fun o => ?_
    change interp B img o (exec c3 _ _) ram 0 []=.ok c4 ram []
    have value : c3.get 0=0#32 := by simp [c3,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h8]
    rw [exec_opimm,value,show alu .add 0#32 1#32=1#32 by decide +kernel]
    rfl
  have t6 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,changed⟩ := by
    refine QuietDet.step_of (by change (2147489924#32).getLsbD 0=false;decide) wm2147489924 fun o => ?_
    change interp B img o (exec c4 _ _) ram 0 []=.ok c5 changed []
    have v8 : c4.get 8=fp := by simp [c4,c4,c3,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h8]
    have v12 : c4.get 12=1#32 := by simp [c4,c4,c3,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h8]
    rw [exec_store,v8,v12]
    have addr : fp+532#32=sp+3736#32 := by decide +kernel
    rw [addr,interp_store_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3736) (by decide) (by decide))];rfl
  have t7 : Quiet.Step B img ⟨c5,changed⟩ ⟨c6,changed⟩ := by
    refine QuietDet.step_of (by change (2147489928#32).getLsbD 0=false;decide) wm2147489928 fun o => ?_
    change interp B img o (exec c5 _ _) changed 0 []=.ok c6 changed []
    rw [exec_opimm,Core.get_zero,show alu .add (0 : Word) 405#32=405#32 by decide +kernel];rfl
  have t8 : Quiet.Step B img ⟨c6,changed⟩ ⟨c7,changed⟩ := by
    refine QuietDet.step_of (by change (2147489932#32).getLsbD 0=false;decide) wm2147489932 fun o => ?_
    change interp B img o (exec c6 _ _) changed 0 []=.ok c7 changed []
    have value : c6.get 2=sp := by simp [c6,c5,c4,c4,c3,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h8]
    rw [exec_opimm,value,show alu .add sp 2047#32=(sp+2047#32) by rfl]
    rfl
  have t9 : Quiet.Step B img ⟨c7,changed⟩ ⟨c8,changed⟩ := by
    refine QuietDet.step_of (by change (2147489936#32).getLsbD 0=false;decide) wm2147489936 fun o => ?_
    change interp B img o (exec c7 _ _) changed 0 []=.ok c8 changed []
    have value : c7.get 9=(sp+2047#32) := by simp [c7,c6,c5,c4,c4,c3,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h8]
    rw [exec_opimm,value,show alu .add (sp+2047#32) 1257#32=2164258936#32 by decide +kernel]
    rfl
  have t10 : Quiet.Step B img ⟨c8,changed⟩ ⟨c9,changed⟩ := by
    refine QuietDet.step_of (by change (2147489940#32).getLsbD 0=false;decide) wm2147489940 fun o => ?_
    change interp B img o (exec c8 _ _) changed 0 []=.ok c9 changed []
    have value : c8.get 0=0#32 := by simp [c8,c7,c6,c5,c4,c4,c3,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h8]
    rw [exec_opimm,value,show alu .add 0#32 4294967294#32=4294967294#32 by decide +kernel]
    rfl
  have t12 : Quiet.Step B img ⟨c9,changed⟩ ⟨c10,changed⟩ := by
    refine QuietDet.step_of (by change (2147489942#32).getLsbD 0=false;decide) wm2147489942 fun o => ?_
    change interp B img o (exec c9 _ _) changed 0 []=.ok c10 changed []
    rw [exec_jal,show c9.pc=2147489942#32 by rfl]
    change interp B img o (jump (c9.set 0 2147489944#32) 2147489576#32) changed 0 []=_
    rw [jump_ok _ _ (by decide)];rfl
  refine ⟨c10,.step t0 (.step t1 (.step t2 (.step t4 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.single t12))))))))),rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,rfl⟩
  all_goals first | (intro r n11 n20 n13 n9 n12 n10 n24 n6;simp [c10,c9,c9,c8,c7,c6,c5,c4,c4,c3,c3,c2,c1,Core.wr_get_ne,Core.wr_get,n11,n20,n13,n9,n12,n10,n24,n6]) | simp [c10,c9,c9,c8,c7,c6,c5,c4,c4,c3,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
end E5R.Thermostat.RelayWrongSetup
