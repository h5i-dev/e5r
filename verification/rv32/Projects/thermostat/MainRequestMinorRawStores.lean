import Projects.thermostat.MainRequestBuildCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainRequestMinorRawStores
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp minor rx used : Word) :=
  ramWrite (ramWrite (ramWrite (ram) (sp+3608#32) (minor) .b) (sp+3640#32) (rx) .w) (sp+3644#32) (used) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp minor rx used : Word) (h8 : c.get 8=sp+3204#32) (stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0)(h2 : c.get 2=sp) (h21 : c.get 21=rx) (h24 : c.get 24=used)
(hminor : ramRead ram (sp+40#32) .w=minor)
    (hp : c.pc=0x80001222#32) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,memory ram sp minor rx used⟩ ∧ d.pc=0x80001230#32 ∧
      d.get 9=minor ∧ (∀ r : Reg, r≠9 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 9 (minor) 0x80001224#32
  let r1 := ramWrite ram (sp+3608#32) (minor) .b
  let c2 := c1.goto 0x80001228#32
  let r2 := ramWrite r1 (sp+3640#32) (rx) .w
  let c3 := c2.goto 0x8000122c#32
  let r3 := ramWrite r2 (sp+3644#32) (used) .w
  let c4 := c3.goto 0x80001230#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147488290) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v2 : c.get 2=sp := by simp [Core.wr_get_ne,Core.wr_get,h8,h2,h21,h24]
    rw [exec_load,v2,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 10 aligned) (Memory.block_access stack (off := 40) (by decide) (by decide)),hminor];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine Quiet.step_of (by change (0x80001224#32).getLsbD 0=false;decide) re2147488292 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 r1 [],[]⟩
    have v8 : c1.get 8=sp+3204#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h2,h21,h24]
    have v9 : c1.get 9=minor := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h2,h21,h24]
    rw [exec_store,v8,v9,BitVec.add_assoc,show 3204#32+404#32=3608#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3608) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,r2⟩ := by
    refine Quiet.step_of (by change (0x80001228#32).getLsbD 0=false;decide) re2147488296 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) r1 0 [] [] = ⟨.ok c3 r2 [],[]⟩
    have v8 : c2.get 8=sp+3204#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h21,h24]
    have v21 : c2.get 21=rx := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h21,h24]
    rw [exec_store,v8,v21,BitVec.add_assoc,show 3204#32+436#32=3640#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 910 aligned) (Memory.block_access stack (off := 3640) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r2⟩ ⟨c4,r3⟩ := by
    refine Quiet.step_of (by change (0x8000122c#32).getLsbD 0=false;decide) re2147488300 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r2 0 [] [] = ⟨.ok c4 r3 [],[]⟩
    have v8 : c3.get 8=sp+3204#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h21,h24]
    have v24 : c3.get 24=used := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h21,h24]
    rw [exec_store,v8,v24,BitVec.add_assoc,show 3204#32+440#32=3644#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 911 aligned) (Memory.block_access stack (off := 3644) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c4,.step t0 (.step t1 (.step t2 (.single t3))),rfl,?_ ,?_ ,by rfl⟩
  · simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h21,h24]
  · intro reg h9;simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h21,h24,h9]
end E5R.Thermostat.MainRequestMinorRawStores
