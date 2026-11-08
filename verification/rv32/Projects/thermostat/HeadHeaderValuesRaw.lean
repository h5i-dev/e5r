import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadHeaderValuesRaw
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp count p vs ve : Word) :=
  ramWrite (ramWrite (ram) (p+8#32) (vs) .w) (p+12#32) (ve) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp count p vs ve : Word) (h2 : c.get 2=sp) (h9 : c.get 9=count) (h15 : c.get 15=vs) (h25 : c.get 25=ve)
(hslot : (sp+56#32)+alu .sll count 4#32=p) (pmem : Memory.Block B p 16) (aligned : p.toNat%4=0)
    (hp : c.pc=0x800033b6#32) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,memory ram sp count p vs ve⟩ ∧ d.pc=0x800033c2#32 ∧
      d.get 9=alu .sll count 4#32 ∧ d.get 10=p ∧ (∀ r : Reg, r≠9 → r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 9 (alu .sll count 4#32) 0x800033b8#32
  let c2 := c1.wr 10 (sp+56#32) 0x800033ba#32
  let c3 := c2.wr 10 (p) 0x800033bc#32
  let r1 := ramWrite ram (p+8#32) (vs) .w
  let c4 := c3.goto 0x800033be#32
  let r2 := ramWrite r1 (p+12#32) (ve) .w
  let c5 := c4.goto 0x800033c2#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496886) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_opimm,h9];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800033b8#32).getLsbD 0=false;decide) hh2147496888 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v2 : c1.get 2=sp := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h9,h15,h25]
    rw [exec_opimm,v2];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800033ba#32).getLsbD 0=false;decide) hh2147496890 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v10 : c2.get 10=sp+56#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h9,h15,h25]
    have v9 : c2.get 9=alu .sll count 4#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h9,h15,h25]
    rw [exec_op,v10,v9]
    change Observed.interp B img o (.done (c2.wr 10 ((sp+56#32)+alu .sll count 4#32) 0x800033bc#32)) ram 0 [] [] = _
    rw [hslot];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,r1⟩ := by
    refine Quiet.step_of (by change (0x800033bc#32).getLsbD 0=false;decide) hh2147496892 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 r1 [],[]⟩
    have v10 : c3.get 10=p := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h9,h15,h25]
    have v15 : c3.get 15=vs := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h9,h15,h25]
    rw [exec_store,v10,v15,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned p 2 aligned)
     (Memory.block_access pmem (off := 8) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r1⟩ ⟨c5,r2⟩ := by
    refine Quiet.step_of (by change (0x800033be#32).getLsbD 0=false;decide) hh2147496894 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r1 0 [] [] = ⟨.ok c5 r2 [],[]⟩
    have v10 : c4.get 10=p := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h9,h15,h25]
    have v25 : c4.get 25=ve := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h9,h15,h25]
    rw [exec_store,v10,v25,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned p 3 aligned)
     (Memory.block_access pmem (off := 12) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c5,.step t0 (.step t1 (.step t2 (.step t3 (.single t4)))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h9,h15,h25]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h9,h15,h25]
  · intro reg h9 h10;simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h9,h15,h25,h9,h10]
end E5R.Thermostat.HeadHeaderValuesRaw
