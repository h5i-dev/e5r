import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadFieldsScanInit
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf index length : Word) (h2 : c.get 2=sp) (h24 : c.get 24=index)
(hlen : ramRead ram (sp+48#32) .w=length) (hbuf : ramRead ram (sp+44#32) .w=buf)
(ht : taken .ltu length index=false) (hm : Memory.Block B sp 56) (ha : sp.toNat%4=0)
    (hp : c.pc=0x80002f58#32) :
    ∃ d, Quiet.Steps B img 9 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80002f6e#32 ∧
      d.get 10=length ∧ d.get 11=index ∧ d.get 21=0#32 ∧ d.get 13=index-length ∧ d.get 25=0xffffffff#32 ∧ d.get 14=buf ∧ (∀ r : Reg, r≠10 → r≠11 → r≠21 → r≠13 → r≠25 → r≠14 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (index) 0x80002f5a#32
  let c2 := c1.wr 11 (length) 0x80002f5c#32
  let c3 := c2.goto 0x80002f60#32
  let c4 := c3.wr 10 (length) 0x80002f62#32
  let c5 := c4.wr 21 (0#32) 0x80002f64#32
  let c6 := c5.wr 13 (index-length) 0x80002f68#32
  let c7 := c6.wr 25 (0xffffffff#32) 0x80002f6a#32
  let c8 := c7.wr 11 (index) 0x80002f6c#32
  let c9 := c8.wr 14 (buf) 0x80002f6e#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147495768) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_op,Core.get_zero,h24,show alu .add (0 : Word) index=index from BitVec.zero_add _];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80002f5a#32).getLsbD 0=false;decide) hh2147495770 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v2 : c1.get 2=sp := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h24]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 12 ha)
      (Memory.block_access hm (off := 48) (by decide) (by decide)),hlen];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80002f5c#32).getLsbD 0=false;decide) hh2147495772 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v11 : c2.get 11=length := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
    have v24 : c2.get 24=index := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
    rw [exec_branch,v11,v24,ht];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80002f60#32).getLsbD 0=false;decide) hh2147495776 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v2 : c3.get 2=sp := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 12 ha)
      (Memory.block_access hm (off := 48) (by decide) (by decide)),hlen];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80002f62#32).getLsbD 0=false;decide) hh2147495778 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x80002f64#32).getLsbD 0=false;decide) hh2147495780 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v24 : c5.get 24=index := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
    have v10 : c5.get 10=length := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
    rw [exec_op,v24,v10];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x80002f68#32).getLsbD 0=false;decide) hh2147495784 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    rw [exec_opimm,Core.get_zero];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x80002f6a#32).getLsbD 0=false;decide) hh2147495786 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v24 : c7.get 24=index := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
    rw [exec_op,Core.get_zero,v24,show alu .add (0 : Word) index=index from BitVec.zero_add _];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x80002f6c#32).getLsbD 0=false;decide) hh2147495788 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have v2 : c8.get 2=sp := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 11 ha)
      (Memory.block_access hm (off := 44) (by decide) (by decide)),hbuf];first | rfl | (rw [hp];rfl)
  refine ⟨c9,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.single t8)))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24]
  · intro reg h10 h11 h21 h13 h25 h14;simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h24,h10,h11,h21,h13,h25,h14]
end E5R.Thermostat.HeadFieldsScanInit
