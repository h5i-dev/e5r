import Projects.thermostat.UnmatchedCode
import Projects.thermostat.MainWriteFlags
import Projects.thermostat.QuietDet
import Projects.thermostat.FrameOffsets
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 5000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.UnmatchedCore
open E5R E5R.Thermostat
abbrev sp : Word := 0x80ffeb90#32
abbrev fp : Word := 0x80fff814#32

/-- Actual final not-found/wrong-method selection, with the real poll flag
    store and status bytes. The connection-close byte is not forced here. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (known : Bool)
    (h2 : c.get 2=sp) (h8 : c.get 8=fp) (h9 : c.get 9=(if known then 2#32 else 3#32))
    (stack : Memory.Block B sp 5232) (pc : c.pc=0x80001898#32) :
    ∃ d,Quiet.Steps B img 13 ⟨c,ram⟩ ⟨d,MainWriteFlags.memory ram fp⟩ ∧ d.pc=0x80001728#32 ∧
      d.get 10=(if known then 405#32 else 404#32) ∧ d.get 11=0#32 ∧ d.get 20=0#32 ∧ d.get 13=0#32 ∧ d.get 12=1#32 ∧
      d.get 9=0x80fff878#32 ∧ d.get 24=0xfffffffe#32 ∧ d.get 6=ramRead ram (sp+20#32) .w ∧
      (∀ r : Reg,r≠11 → r≠20 → r≠13 → r≠9 → r≠12 → r≠10 → r≠24 → r≠6 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 11 (0#32) 2147489946#32
  let c2 := c1.wr 20 (0#32) 2147489948#32
  let c3 := c2.wr 13 (0#32) 2147489950#32
  let c4 := c3.wr 9 ((if known then 0xffffffff#32 else 0#32)) 2147489952#32
  let c5 := c4.wr 12 (1#32) 2147489954#32
  let c6 := c5.wr 10 ((if known then 0#32 else 1#32)) 2147489958#32
  let c7 := c6.goto 2147489962#32
  let c8 := c7.wr 10 ((if known then 405#32 else 404#32)) 2147489966#32
  let c9 := c8.wr 9 ((sp+2047#32)) 2147489970#32
  let c10 := c9.wr 9 (0x80fff878#32) 2147489974#32
  let c11 := c10.wr 24 (0xfffffffe#32) 2147489976#32
  let c12 := c11.wr 6 (ramRead ram (sp+20#32) .w) 2147489978#32
  let c13 := c12.goto 2147489576#32
  let changed := MainWriteFlags.memory ram fp
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine QuietDet.step_of (by rw [pc];decide) (by rw [pc];exact um2147489944) fun o => ?_
    change interp B img o (exec c _ _) ram 0 []=.ok c1 ram []
    have value : c.get 0=0#32 := by simp [Core.wr_get_ne,Core.wr_get,h2,h8,h9]
    rw [exec_opimm,value,show alu .add 0#32 0#32=0#32 by decide +kernel]
    rw [pc]
    rfl
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine QuietDet.step_of (by change (2147489946#32).getLsbD 0=false;decide) um2147489946 fun o => ?_
    change interp B img o (exec c1 _ _) ram 0 []=.ok c2 ram []
    have value : c1.get 0=0#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h8,h9]
    rw [exec_opimm,value,show alu .add 0#32 0#32=0#32 by decide +kernel]
    rfl
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine QuietDet.step_of (by change (2147489948#32).getLsbD 0=false;decide) um2147489948 fun o => ?_
    change interp B img o (exec c2 _ _) ram 0 []=.ok c3 ram []
    have value : c2.get 0=0#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h9]
    rw [exec_opimm,value,show alu .add 0#32 0#32=0#32 by decide +kernel]
    rfl
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine QuietDet.step_of (by change (2147489950#32).getLsbD 0=false;decide) um2147489950 fun o => ?_
    change interp B img o (exec c3 _ _) ram 0 []=.ok c4 ram []
    have value : c3.get 9=(if known then 2#32 else 3#32) := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h9]
    rw [exec_opimm,value,show alu .add (if known then 2#32 else 3#32) 0xfffffffd#32=(if known then 0xffffffff#32 else 0#32) by cases known <;> decide +kernel]
    rfl
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine QuietDet.step_of (by change (2147489952#32).getLsbD 0=false;decide) um2147489952 fun o => ?_
    change interp B img o (exec c4 _ _) ram 0 []=.ok c5 ram []
    have value : c4.get 0=0#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h9]
    rw [exec_opimm,value,show alu .add 0#32 1#32=1#32 by decide +kernel]
    rfl
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine QuietDet.step_of (by change (2147489954#32).getLsbD 0=false;decide) um2147489954 fun o => ?_
    change interp B img o (exec c5 _ _) ram 0 []=.ok c6 ram []
    have value : c5.get 9=(if known then 0xffffffff#32 else 0#32) := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h9]
    rw [exec_opimm,value,show alu .sltu (if known then 0xffffffff#32 else 0#32) 1#32=(if known then 0#32 else 1#32) by cases known <;> decide +kernel]
    rfl
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,changed⟩ := by
    refine QuietDet.step_of (by change (2147489958#32).getLsbD 0=false;decide) um2147489958 fun o => ?_
    change interp B img o (exec c6 _ _) ram 0 []=.ok c7 changed []
    have v8 : c6.get 8=fp := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h9]
    have v12 : c6.get 12=1#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h9]
    rw [exec_store,v8,v12]
    have addr : fp+532#32=sp+3736#32 := by decide +kernel
    rw [addr,interp_store_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3736) (by decide) (by decide))];rfl
  have t7 : Quiet.Step B img ⟨c7,changed⟩ ⟨c8,changed⟩ := by
    refine QuietDet.step_of (by change (2147489962#32).getLsbD 0=false;decide) um2147489962 fun o => ?_
    change interp B img o (exec c7 _ _) changed 0 []=.ok c8 changed []
    have value : c7.get 10=(if known then 0#32 else 1#32) := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h9]
    rw [exec_opimm,value,show alu .xor (if known then 0#32 else 1#32) 405#32=(if known then 405#32 else 404#32) by cases known <;> decide +kernel]
    rfl
  have t8 : Quiet.Step B img ⟨c8,changed⟩ ⟨c9,changed⟩ := by
    refine QuietDet.step_of (by change (2147489966#32).getLsbD 0=false;decide) um2147489966 fun o => ?_
    change interp B img o (exec c8 _ _) changed 0 []=.ok c9 changed []
    have value : c8.get 2=sp := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h9]
    rw [exec_opimm,value,show alu .add sp 2047#32=(sp+2047#32) by rfl]
    rfl
  have t9 : Quiet.Step B img ⟨c9,changed⟩ ⟨c10,changed⟩ := by
    refine QuietDet.step_of (by change (2147489970#32).getLsbD 0=false;decide) um2147489970 fun o => ?_
    change interp B img o (exec c9 _ _) changed 0 []=.ok c10 changed []
    have value : c9.get 9=(sp+2047#32) := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h9]
    rw [exec_opimm,value,show alu .add (sp+2047#32) 1257#32=0x80fff878#32 by decide +kernel]
    rfl
  have t10 : Quiet.Step B img ⟨c10,changed⟩ ⟨c11,changed⟩ := by
    refine QuietDet.step_of (by change (2147489974#32).getLsbD 0=false;decide) um2147489974 fun o => ?_
    change interp B img o (exec c10 _ _) changed 0 []=.ok c11 changed []
    have value : c10.get 0=0#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h9]
    rw [exec_opimm,value,show alu .add 0#32 0xfffffffe#32=0xfffffffe#32 by decide +kernel]
    rfl
  have t11 : Quiet.Step B img ⟨c11,changed⟩ ⟨c12,changed⟩ := by
    refine QuietDet.step_of (by change (2147489976#32).getLsbD 0=false;decide) um2147489976 fun o => ?_
    change interp B img o (exec c11 _ _) changed 0 []=.ok c12 changed []
    have v2 : c11.get 2=sp := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h8,h9]
    rw [exec_load,v2,interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 5 (by decide +kernel)) (Memory.block_access stack (off := 20) (by decide) (by decide))]
    have kept : ramRead changed (sp+20#32) .w=ramRead ram (sp+20#32) .w := by
      unfold changed MainWriteFlags.memory
      rw [show fp+532#32=sp+3736#32 by decide +kernel]
      exact FrameOffsets.word ram sp 1#32 20 3736 .b (by decide) (by decide) (Or.inl (by decide))
    rw [kept];rfl
  have t12 : Quiet.Step B img ⟨c12,changed⟩ ⟨c13,changed⟩ := by
    refine QuietDet.step_of (by change (2147489978#32).getLsbD 0=false;decide) um2147489978 fun o => ?_
    change interp B img o (exec c12 _ _) changed 0 []=.ok c13 changed []
    rw [exec_jal,show c12.pc=2147489978#32 by rfl]
    change interp B img o (jump (c12.set 0 2147489980#32) 0x80001728#32) changed 0 []=_
    rw [jump_ok _ _ (by decide)];rfl
  refine ⟨c13,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.single t12)))))))))))),rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,rfl⟩
  all_goals first | (intro r n11 n20 n13 n9 n12 n10 n24 n6;simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,n11,n20,n13,n9,n12,n10,n24,n6]) | simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get]
end E5R.Thermostat.UnmatchedCore
