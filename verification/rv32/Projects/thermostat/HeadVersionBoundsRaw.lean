import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadVersionBoundsRaw
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp pos length : Word) (h7 : c.get 7=pos) (h2 : c.get 2=sp) (hword : ramRead ram (sp+48#32) .w=length)
(hm : Memory.Block B sp 56) (ha : sp.toNat%4=0)
(ht7 : taken .geu (pos+7#32) length=false)
(ht8 : taken .geu (pos+8#32) length=false)
(ht9 : taken .geu (pos+9#32) length=false)
    (hp : c.pc=0x80002e8c#32) :
    ∃ d, Quiet.Steps B img 9 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002eaa#32 ∧
      d.get 10=pos+9#32 ∧ d.get 11=length ∧ (∀ r : Reg, r≠10 → r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (pos+7#32) 0x80002e90#32
  let c2 := c1.wr 11 (length) 0x80002e92#32
  let c3 := c2.goto 0x80002e96#32
  let c4 := c3.wr 10 (pos+8#32) 0x80002e9a#32
  let c5 := c4.wr 11 (length) 0x80002e9c#32
  let c6 := c5.goto 0x80002ea0#32
  let c7 := c6.wr 10 (pos+9#32) 0x80002ea4#32
  let c8 := c7.wr 11 (length) 0x80002ea6#32
  let c9 := c8.goto 0x80002eaa#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495564) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v7 : c.get 7=pos := by simp [Core.wr_get_ne,Core.wr_get,h7,h2]
    rw [exec_opimm,v7];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80002e90#32).getLsbD 0=false;decide) hh2147495568 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v2 : c1.get 2=sp := by simp [c1,Core.wr_get_ne,Core.wr_get,h7,h2]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 12 ha)
      (Memory.block_access hm (off := 48) (by decide) (by decide)),hword];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80002e92#32).getLsbD 0=false;decide) hh2147495570 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v10 : c2.get 10=pos+7#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h7,h2]
    have v11 : c2.get 11=length := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h7,h2]
    rw [exec_branch,v10,v11,ht7];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80002e96#32).getLsbD 0=false;decide) hh2147495574 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v7 : c3.get 7=pos := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h7,h2]
    rw [exec_opimm,v7];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80002e9a#32).getLsbD 0=false;decide) hh2147495578 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v2 : c4.get 2=sp := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h7,h2]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 12 ha)
      (Memory.block_access hm (off := 48) (by decide) (by decide)),hword];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80002e9c#32).getLsbD 0=false;decide) hh2147495580 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v10 : c5.get 10=pos+8#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h7,h2]
    have v11 : c5.get 11=length := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h7,h2]
    rw [exec_branch,v10,v11,ht8];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80002ea0#32).getLsbD 0=false;decide) hh2147495584 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v7 : c6.get 7=pos := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h7,h2]
    rw [exec_opimm,v7];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x80002ea4#32).getLsbD 0=false;decide) hh2147495588 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v2 : c7.get 2=sp := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h7,h2]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 12 ha)
      (Memory.block_access hm (off := 48) (by decide) (by decide)),hword];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x80002ea6#32).getLsbD 0=false;decide) hh2147495590 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have v10 : c8.get 10=pos+9#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h7,h2]
    have v11 : c8.get 11=length := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h7,h2]
    rw [exec_branch,v10,v11,ht9];first | rfl | (rw [hp];rfl)
  refine ⟨c9,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.single t8)))))))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h7,h2]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h7,h2]
  · intro reg h10 h11;simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h7,h2,h10,h11]
end E5R.Thermostat.HeadVersionBoundsRaw
