import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadNameInitRaw
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp start span negative length buf next before : Word) (h2 : c.get 2=sp) (h24 : c.get 24=start) (h21 : c.get 21=span) (h22 : c.get 22=negative)
(hlen : ramRead ram (sp+48#32) .w=length) (hbuf : ramRead ram (sp+44#32) .w=buf)
(hnext : ramRead ram (sp+16#32) .w=next) (hbefore : ramRead ram (sp+12#32) .w=before)
(ht : taken .eq length start=false) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0)
    (hp : c.pc=0x80002fbc#32) :
    ∃ d, Quiet.Steps B img 12 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002ff0#32 ∧
      d.get 10=next+start ∧ d.get 14=0#32 ∧ d.get 15=span+0xffffffff#32 ∧ d.get 13=negative+start ∧ d.get 20=buf+start ∧ d.get 12=before ∧ d.get 31=before-start ∧ (∀ r : Reg, r≠10 → r≠14 → r≠15 → r≠13 → r≠20 → r≠12 → r≠31 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (length) 0x80002fbe#32
  let c2 := c1.goto 0x80002fc2#32
  let c3 := c2.wr 14 (0#32) 0x80002fc4#32
  let c4 := c3.wr 15 (span+0xffffffff#32) 0x80002fc8#32
  let c5 := c4.wr 13 (negative+start) 0x80002fcc#32
  let c6 := c5.wr 20 (buf) 0x80002fce#32
  let c7 := c6.wr 20 (buf+start) 0x80002fd0#32
  let c8 := c7.wr 10 (next) 0x80002fd2#32
  let c9 := c8.wr 10 (next+start) 0x80002fd4#32
  let c10 := c9.wr 12 (before) 0x80002fd6#32
  let c11 := c10.wr 31 (before-start) 0x80002fda#32
  let c12 := c11.goto 0x80002ff0#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495868) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_load,h2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 12 ha)
     (Memory.block_access stack (off := 48) (by decide) (by decide)),hlen];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80002fbe#32).getLsbD 0=false;decide) hh2147495870 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v10 : c1.get 10=length := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h24,h21,h22]
    have v24 : c1.get 24=start := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h24,h21,h22]
    rw [exec_branch,v10,v24,ht];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80002fc2#32).getLsbD 0=false;decide) hh2147495874 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80002fc4#32).getLsbD 0=false;decide) hh2147495876 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v21 : c3.get 21=span := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h21,h22]
    rw [exec_opimm,v21];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80002fc8#32).getLsbD 0=false;decide) hh2147495880 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v22 : c4.get 22=negative := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h21,h22]
    have v24 : c4.get 24=start := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h21,h22]
    rw [exec_op,v22,v24];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80002fcc#32).getLsbD 0=false;decide) hh2147495884 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v2 : c5.get 2=sp := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h21,h22]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 11 ha)
     (Memory.block_access stack (off := 44) (by decide) (by decide)),hbuf];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80002fce#32).getLsbD 0=false;decide) hh2147495886 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v20 : c6.get 20=buf := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h21,h22]
    have v24 : c6.get 24=start := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h21,h22]
    rw [exec_op,v20,v24];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x80002fd0#32).getLsbD 0=false;decide) hh2147495888 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v2 : c7.get 2=sp := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h21,h22]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 4 ha)
     (Memory.block_access stack (off := 16) (by decide) (by decide)),hnext];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x80002fd2#32).getLsbD 0=false;decide) hh2147495890 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have v10 : c8.get 10=next := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h21,h22]
    have v24 : c8.get 24=start := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h21,h22]
    rw [exec_op,v10,v24];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x80002fd4#32).getLsbD 0=false;decide) hh2147495892 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    have v2 : c9.get 2=sp := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h21,h22]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 3 ha)
     (Memory.block_access stack (off := 12) (by decide) (by decide)),hbefore];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x80002fd6#32).getLsbD 0=false;decide) hh2147495894 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    have v12 : c10.get 12=before := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h21,h22]
    have v24 : c10.get 24=start := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h21,h22]
    rw [exec_op,v12,v24];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x80002fda#32).getLsbD 0=false;decide) hh2147495898 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    rw [exec_jal,Core.set_zero]
    change Observed.interp B img o (jump c11 (0x80002fda#32+0x16#32)) ram 0 [] [] = _
    rw [show 0x80002fda#32+0x16#32=0x80002ff0#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  refine ⟨c12,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.single t11))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h21,h22]
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h21,h22]
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h21,h22]
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h21,h22]
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h21,h22]
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h21,h22]
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h21,h22]
  · intro reg h10 h14 h15 h13 h20 h12 h31;simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h21,h22,h10,h14,h15,h13,h20,h12,h31]
end E5R.Thermostat.HeadNameInitRaw
