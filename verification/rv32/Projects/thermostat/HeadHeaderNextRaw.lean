import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadHeaderNextRaw
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp span start cap : Word) (h2 : c.get 2=sp) (h21 : c.get 21=span) (h24 : c.get 24=start) (hcap : ramRead ram (sp+40#32) .w=cap)
(stack : Memory.Block B sp 327) (ha : sp.toNat%4=0)
    (hp : c.pc=0x800033de#32) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800033e6#32 ∧
      d.get 21=span+start ∧ d.get 24=(span+start)+2#32 ∧ d.get 10=cap ∧ (∀ r : Reg, r≠21 → r≠24 → r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 21 (span+start) 0x800033e0#32
  let c2 := c1.wr 24 ((span+start)+2#32) 0x800033e4#32
  let c3 := c2.wr 10 (cap) 0x800033e6#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496926) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_op,h21,h24];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800033e0#32).getLsbD 0=false;decide) hh2147496928 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v21 : c1.get 21=span+start := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h21,h24]
    rw [exec_opimm,v21];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800033e4#32).getLsbD 0=false;decide) hh2147496932 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v2 : c2.get 2=sp := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,h24]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 10 ha)
     (Memory.block_access stack (off := 40) (by decide) (by decide)),hcap];first | rfl | (rw [hp];rfl)
  refine ⟨c3,.step t0 (.step t1 (.single t2)),rfl,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,h24]
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,h24]
  · simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,h24]
  · intro reg h21 h24 h10;simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h21,h24,h21,h24,h10]
end E5R.Thermostat.HeadHeaderNextRaw
