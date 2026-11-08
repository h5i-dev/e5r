import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadClStoreRaw
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp low : Word) :=
  ramWrite (ramWrite (ramWrite (ram) (sp+312#32) (low) .w) (sp+316#32) (0#32) .w) (sp+325#32) (1#32) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp low : Word) (h2 : c.get 2=sp) (h14 : c.get 14=low) (h13 : c.get 13=0#32) (stack : Memory.Block B sp 327) (ha : sp.toNat%4=0)
    (hp : c.pc=0x8000325e#32) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,memory ram sp low⟩ ∧ d.pc=0x800033b6#32 ∧
      d.get 10=1#32 ∧ (∀ r : Reg, r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let r1 := ramWrite ram (sp+312#32) (low) .w
  let c1 := c.goto 0x80003262#32
  let r2 := ramWrite r1 (sp+316#32) (0#32) .w
  let c2 := c1.goto 0x80003266#32
  let c3 := c2.wr 10 (1#32) 0x80003268#32
  let r3 := ramWrite r2 (sp+325#32) (1#32) .b
  let c4 := c3.goto 0x8000326c#32
  let c5 := c4.goto 0x800033b6#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,r1⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496542) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 r1 [],[]⟩
    rw [exec_store,h2,h14,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 78 ha)
     (Memory.block_access stack (off := 312) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,r1⟩ ⟨c2,r2⟩ := by
    refine Quiet.step_of (by change (0x80003262#32).getLsbD 0=false;decide) hh2147496546 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) r1 0 [] [] = ⟨.ok c2 r2 [],[]⟩
    have v2 : c1.get 2=sp := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h14,h13]
    have v13 : c1.get 13=0#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h14,h13]
    rw [exec_store,v2,v13,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 79 ha)
     (Memory.block_access stack (off := 316) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,r2⟩ ⟨c3,r2⟩ := by
    refine Quiet.step_of (by change (0x80003266#32).getLsbD 0=false;decide) hh2147496550 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) r2 0 [] [] = ⟨.ok c3 r2 [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r2⟩ ⟨c4,r3⟩ := by
    refine Quiet.step_of (by change (0x80003268#32).getLsbD 0=false;decide) hh2147496552 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r2 0 [] [] = ⟨.ok c4 r3 [],[]⟩
    have v2 : c3.get 2=sp := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h14,h13]
    have v10 : c3.get 10=1#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h14,h13]
    rw [exec_store,v2,v10,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _)
     (Memory.block_access stack (off := 325) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r3⟩ ⟨c5,r3⟩ := by
    refine Quiet.step_of (by change (0x8000326c#32).getLsbD 0=false;decide) hh2147496556 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r3 0 [] [] = ⟨.ok c5 r3 [],[]⟩
    rw [exec_jal]
    change Observed.interp B img o (jump (c4.set 0 (c4.pc+2#32)) (0x8000326c#32+0x14a#32)) r3 0 [] [] = _
    rw [show 0x8000326c#32+0x14a#32=0x800033b6#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c5,.step t0 (.step t1 (.step t2 (.step t3 (.single t4)))),rfl,?_ ,?_ ,by rfl⟩
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h14,h13]
  · intro reg h10;simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h14,h13,h10]
end E5R.Thermostat.HeadClStoreRaw
