import Projects.thermostat.HttpParseCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HeadHeaderNamesRaw
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp p ns count te : Word) :=
  ramWrite (ram) (p+0#32) (ns) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp p ns count te : Word) (h2 : c.get 2=sp) (h10 : c.get 10=p) (h24 : c.get 24=ns)
(hcount : ramRead ram (sp+320#32) .w=count) (hflag : BitVec.ofNat 32 (ram (sp+326#32)).toNat=te)
(stack : Memory.Block B sp 327) (ha : sp.toNat%4=0) (pmem : Memory.Block B p 16) (aligned : p.toNat%4=0)
    (hp : c.pc=0x800033c2#32) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,memory ram sp p ns count te⟩ ∧ d.pc=0x800033d0#32 ∧
      d.get 9=count+1#32 ∧ d.get 23=te ∧ (∀ r : Reg, r≠9 → r≠23 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 9 (count) 0x800033c6#32
  let c2 := c1.wr 23 (te) 0x800033ca#32
  let c3 := c2.wr 9 (count+1#32) 0x800033cc#32
  let r1 := ramWrite ram (p+0#32) (ns) .w
  let c4 := c3.goto 0x800033d0#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact hh2147496898) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    rw [exec_load,h2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 80 ha)
     (Memory.block_access stack (off := 320) (by decide) (by decide)),hcount];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x800033c6#32).getLsbD 0=false;decide) hh2147496902 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v2 : c1.get 2=sp := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h10,h24]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _)
     (Memory.block_access stack (off := 326) (by decide) (by decide)),Memory.load_byte,hflag];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x800033ca#32).getLsbD 0=false;decide) hh2147496906 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v9 : c2.get 9=count := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h24]
    rw [exec_opimm,v9];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,r1⟩ := by
    refine Quiet.step_of (by change (0x800033cc#32).getLsbD 0=false;decide) hh2147496908 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 r1 [],[]⟩
    have v10 : c3.get 10=p := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h24]
    have v24 : c3.get 24=ns := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h24]
    rw [exec_store,v10,v24,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned p 0 aligned)
     (Memory.block_access pmem (off := 0) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c4,.step t0 (.step t1 (.step t2 (.single t3))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h24]
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h24]
  · intro reg h9 h23;simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h10,h24,h9,h23]
end E5R.Thermostat.HeadHeaderNamesRaw
