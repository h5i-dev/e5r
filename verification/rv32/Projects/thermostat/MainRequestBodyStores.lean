import Projects.thermostat.MainRequestBuildCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainRequestBodyStores
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp bodyPtr bodyLen method : Word) :=
  ramWrite (ramWrite (ramWrite (ram) (sp+3632#32) (bodyPtr) .w) (sp+3636#32) (bodyLen) .w) (sp+3684#32) (method) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp bodyPtr bodyLen method : Word) (h8 : c.get 8=sp+3204#32) (stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0)
(h20 : c.get 20=bodyPtr) (h15 : c.get 15=bodyLen) (h14 : c.get 14=method)
    (hp : c.pc=0x80001176#32) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,memory ram sp bodyPtr bodyLen method⟩ ∧ d.pc=0x80001182#32 ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  let r1 := ramWrite ram (sp+3632#32) (bodyPtr) .w
  let c1 := c.goto 0x8000117a#32
  let r2 := ramWrite r1 (sp+3636#32) (bodyLen) .w
  let c2 := c1.goto 0x8000117e#32
  let r3 := ramWrite r2 (sp+3684#32) (method) .b
  let c3 := c2.goto 0x80001182#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,r1⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147488118) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 r1 [],[]⟩
    have v8 : c.get 8=sp+3204#32 := by simp [Core.wr_get_ne,Core.wr_get,h8,h20,h15,h14]
    have v20 : c.get 20=bodyPtr := by simp [Core.wr_get_ne,Core.wr_get,h8,h20,h15,h14]
    rw [exec_store,v8,v20,BitVec.add_assoc,show 3204#32+428#32=3632#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 908 aligned) (Memory.block_access stack (off := 3632) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,r1⟩ ⟨c2,r2⟩ := by
    refine Quiet.step_of (by change (0x8000117a#32).getLsbD 0=false;decide) re2147488122 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) r1 0 [] [] = ⟨.ok c2 r2 [],[]⟩
    have v8 : c1.get 8=sp+3204#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h20,h15,h14]
    have v15 : c1.get 15=bodyLen := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h20,h15,h14]
    rw [exec_store,v8,v15,BitVec.add_assoc,show 3204#32+432#32=3636#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 909 aligned) (Memory.block_access stack (off := 3636) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,r2⟩ ⟨c3,r3⟩ := by
    refine Quiet.step_of (by change (0x8000117e#32).getLsbD 0=false;decide) re2147488126 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) r2 0 [] [] = ⟨.ok c3 r3 [],[]⟩
    have v8 : c2.get 8=sp+3204#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20,h15,h14]
    have v14 : c2.get 14=method := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20,h15,h14]
    rw [exec_store,v8,v14,BitVec.add_assoc,show 3204#32+480#32=3684#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3684) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c3,.step t0 (.step t1 (.single t2)),rfl,?_ ,by rfl⟩
  · intro reg ;simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h20,h15,h14]
end E5R.Thermostat.MainRequestBodyStores
