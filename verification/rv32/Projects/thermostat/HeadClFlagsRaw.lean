import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadClFlagsRaw
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp cl te trailing : Word) (h2 : c.get 2=sp) (h23 : c.get 23=te) (hflag : BitVec.ofNat 32 (ram (sp+325#32)).toNat=cl) (htrailing : ramRead ram (sp+0#32) .w=trailing) (stack : Memory.Block B sp 327) (ha : sp.toNat%4=0)
    (hp : c.pc=0x800031dc#32) :
    ∃ d, Quiet.Steps B img 6 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800031ee#32 ∧
      d.get 10=alu .and (alu .or cl (alu .or (alu .sltu (0 : Word) trailing) te)) 1#32 ∧ d.get 12=alu .or (alu .sltu (0 : Word) trailing) te ∧ (∀ r : Reg, r≠10 → r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (cl) 0x800031e0#32
  let c2 := c1.wr 12 (trailing) 0x800031e2#32
  let c3 := c2.wr 12 (alu .sltu (0 : Word) trailing) 0x800031e6#32
  let c4 := c3.wr 12 (alu .or (alu .sltu (0 : Word) trailing) te) 0x800031ea#32
  let c5 := c4.wr 10 (alu .or cl (alu .or (alu .sltu (0 : Word) trailing) te)) 0x800031ec#32
  let c6 := c5.wr 10 (alu .and (alu .or cl (alu .or (alu .sltu (0 : Word) trailing) te)) 1#32) 0x800031ee#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496412) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_load,h2,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access stack (off := 325) (by decide) (by decide)),Memory.load_byte,hflag];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800031e0#32).getLsbD 0=false;decide) hh2147496416 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v2 : c1.get 2=sp := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h23]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 0 ha) (Memory.block_access stack (off := 0) (by decide) (by decide)),htrailing];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800031e2#32).getLsbD 0=false;decide) hh2147496418 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v12 : c2.get 12=trailing := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h23]
    rw [exec_op,Core.get_zero,v12];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x800031e6#32).getLsbD 0=false;decide) hh2147496422 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v12 : c3.get 12=alu .sltu (0 : Word) trailing := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h23]
    have v23 : c3.get 23=te := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h23]
    rw [exec_op,v12,v23];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x800031ea#32).getLsbD 0=false;decide) hh2147496426 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v10 : c4.get 10=cl := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h23]
    have v12 : c4.get 12=alu .or (alu .sltu (0 : Word) trailing) te := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h23]
    rw [exec_op,v10,v12];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x800031ec#32).getLsbD 0=false;decide) hh2147496428 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v10 : c5.get 10=alu .or cl (alu .or (alu .sltu (0 : Word) trailing) te) := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h23]
    rw [exec_opimm,v10];first | rfl | (rw [hp];rfl)
  refine ⟨c6,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.single t5))))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h23]
  · simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h23]
  · intro reg h10 h12;simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h23,h10,h12]
end E5R.Thermostat.HeadClFlagsRaw
