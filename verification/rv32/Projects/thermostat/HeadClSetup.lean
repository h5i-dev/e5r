import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadClSetup
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp start length buf : Word) (h2 : c.get 2=sp) (h24 : c.get 24=start) (hraw : ramRead ram (sp+48#32) .w=length) (hbuf : ramRead ram (sp+44#32) .w=buf)
(stack : Memory.Block B sp 56) (ha : sp.toNat%4=0)
    (hp : c.pc=0x8000319e#32) :
    ∃ d, Quiet.Steps B img 7 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800031b2#32 ∧
      d.get 10=14#32 ∧ d.get 13=length-start ∧ d.get 31=buf+start ∧ d.get 30=0x80005de0#32 ∧ (∀ r : Reg, r≠10 → r≠13 → r≠31 → r≠30 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (length) 0x800031a0#32
  let c2 := c1.wr 13 (length-start) 0x800031a4#32
  let c3 := c2.wr 31 (buf) 0x800031a6#32
  let c4 := c3.wr 31 (buf+start) 0x800031a8#32
  let c5 := c4.wr 10 (14#32) 0x800031aa#32
  let c6 := c5.wr 30 (0x80006000#32) 0x800031ae#32
  let c7 := c6.wr 30 (0x80005de0#32) 0x800031b2#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496350) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_load,h2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 12 ha)
     (Memory.block_access stack (off := 48) (by decide) (by decide)),hraw];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800031a0#32).getLsbD 0=false;decide) hh2147496352 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v10 : c1.get 10=length := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h24]
    have v24 : c1.get 24=start := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h24]
    rw [exec_op,v10,v24];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800031a4#32).getLsbD 0=false;decide) hh2147496356 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v2 : c2.get 2=sp := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 11 ha)
     (Memory.block_access stack (off := 44) (by decide) (by decide)),hbuf];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x800031a6#32).getLsbD 0=false;decide) hh2147496358 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v31 : c3.get 31=buf := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
    have v24 : c3.get 24=start := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
    rw [exec_op,v31,v24];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x800031a8#32).getLsbD 0=false;decide) hh2147496360 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x800031aa#32).getLsbD 0=false;decide) hh2147496362 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x800031ae#32).getLsbD 0=false;decide) hh2147496366 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v30 : c6.get 30=0x80006000#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
    rw [exec_opimm,v30];first | rfl | (rw [hp];rfl)
  refine ⟨c7,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.single t6)))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
  · intro reg h10 h13 h31 h30;simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h10,h13,h31,h30]
end E5R.Thermostat.HeadClSetup
