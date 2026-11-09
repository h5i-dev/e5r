import Projects.thermostat.LoopKeepPrefixCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.LoopKeepPrefix
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (used : Word) (fp : c.get 8=0x80fff814#32) (capacity : ramRead ram (0x80fff814#32+60#32) .w=2048#32) (filled : ramRead ram (0x80fff814#32+84#32) .w=used) (consumed : ramRead ram (0x80fff814#32+92#32) .w=used) (rx : ramRead ram (0x80fff814#32+56#32) .w=0x80ffec14#32) (bound : used.toNat≤2048) (object : Memory.Block B 0x80fff814#32 96)
    (hp : c.pc=0x800017be#32) :
    ∃ d, Quiet.Steps B img 11 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800056a0#32 ∧
      d.get 12=0#32 ∧ d.get 11=0x80ffec14#32+used ∧ d.get 10=0x80ffec14#32 ∧ d.get 13=0x80ffec14#32 ∧ d.get 1=0x800017e0#32 ∧ (∀ r : Reg, r≠12 → r≠11 → r≠10 → r≠13 → r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 (2048#32) 0x800017c0#32
  let c2 := c1.wr 11 (used) 0x800017c2#32
  let c3 := c2.goto 0x800017c6#32
  let c4 := c3.wr 10 (used) 0x800017c8#32
  let c5 := c4.goto 0x800017cc#32
  let c6 := c5.wr 13 (0x80ffec14#32) 0x800017ce#32
  let c7 := c6.wr 12 (0#32) 0x800017d2#32
  let c8 := c7.wr 11 (0x80ffec14#32+used) 0x800017d6#32
  let c9 := c8.wr 10 (0x80ffec14#32) 0x800017d8#32
  let c10 := c9.wr 1 (0x800057d8#32) 0x800017dc#32
  let c11 := c10.wr 1 (0x800017e0#32) 0x800056a0#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact LoopKeepPrefixCode.at2147489726) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v8 : c.get 8=0x80fff814#32 := by simp [Core.wr_get_ne,Core.wr_get,fp]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 15 (by decide))
      (Memory.block_access object (off := 60) (by decide) (by decide)),capacity];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800017c0#32).getLsbD 0=false;decide) LoopKeepPrefixCode.at2147489728 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v8 : c1.get 8=0x80fff814#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,fp]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 21 (by decide))
      (Memory.block_access object (off := 84) (by decide) (by decide)),filled];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800017c2#32).getLsbD 0=false;decide) LoopKeepPrefixCode.at2147489730 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v12 : c2.get 12=2048#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,fp]
    have v11 : c2.get 11=used := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,fp]
    rw [exec_branch,v12,v11,show taken .ltu 2048#32 used=false by
      have small : ¬2048<used.toNat := by omega
      simp [taken,BitVec.ult,small]];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x800017c6#32).getLsbD 0=false;decide) LoopKeepPrefixCode.at2147489734 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v8 : c3.get 8=0x80fff814#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,fp]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 23 (by decide))
      (Memory.block_access object (off := 92) (by decide) (by decide)),consumed];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x800017c8#32).getLsbD 0=false;decide) LoopKeepPrefixCode.at2147489736 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v11 : c4.get 11=used := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,fp]
    have v10 : c4.get 10=used := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,fp]
    rw [exec_branch,v11,v10,show taken .ltu used used=false by simp [taken,BitVec.ult]];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x800017cc#32).getLsbD 0=false;decide) LoopKeepPrefixCode.at2147489740 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v8 : c5.get 8=0x80fff814#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,fp]
    rw [exec_load,v8,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned 0x80fff814#32 14 (by decide))
      (Memory.block_access object (off := 56) (by decide) (by decide)),rx];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x800017ce#32).getLsbD 0=false;decide) LoopKeepPrefixCode.at2147489742 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v11 : c6.get 11=used := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,fp]
    have v10 : c6.get 10=used := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,fp]
    rw [exec_op,v11,v10,show alu .sub used used=0#32 from BitVec.sub_self used];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x800017d2#32).getLsbD 0=false;decide) LoopKeepPrefixCode.at2147489746 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v13 : c7.get 13=0x80ffec14#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,fp]
    have v10 : c7.get 10=used := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,fp]
    rw [exec_op,v13,v10];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x800017d6#32).getLsbD 0=false;decide) LoopKeepPrefixCode.at2147489750 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have v13 : c8.get 13=0x80ffec14#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,fp]
    rw [exec_op,Core.get_zero,v13];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x800017d8#32).getLsbD 0=false;decide) LoopKeepPrefixCode.at2147489752 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    rw [exec_auipc];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x800017dc#32).getLsbD 0=false;decide) LoopKeepPrefixCode.at2147489756 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    have v1 : c10.get 1=0x800057d8#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,fp]
    rw [exec_jalr,v1]
    change Observed.interp B img o (jump (c10.set 1 0x800017e0#32) 0x800056a0#32) ram 0 [] []=_
    rw [jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c11,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.single t10)))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,fp]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,fp]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,fp]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,fp]
  · simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,fp]
  · intro reg h12 h11 h10 h13 h1;simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,fp,h12,h11,h10,h13,h1]
end E5R.Thermostat.LoopKeepPrefix
