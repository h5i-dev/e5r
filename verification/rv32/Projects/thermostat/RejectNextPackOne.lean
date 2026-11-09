import Projects.thermostat.MainServeNextCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.RejectNextPackOne
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp word half byte : Word) :=
  ramWrite (ramWrite (ramWrite (ram) (sp+3960#32) (word) .w) (sp+3964#32) (half) .h) (sp+3966#32) (byte) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp word half byte : Word) (h8 : c.get 8=sp+3204#32) (stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0)
(h9 : c.get 9=3#32) (h18 : c.get 18=0#32)
(hword : ramRead ram (sp+4896#32) .w=word)
(hhalf : extend .h true (ramRead ram (sp+4900#32) .h)=half)
(hbyte : extend .b false (ramRead ram (sp+4902#32) .b)=byte)
    (hp : c.pc=0x80000aca#32) :
    ∃ d, Quiet.Steps B img 7 ⟨c,ram⟩ ⟨d,memory ram sp word half byte⟩ ∧ d.pc=0x80000ae6#32 ∧
      d.get 10=word ∧ d.get 11=half ∧ d.get 12=byte ∧ d.get 13=0#32 ∧ (∀ r : Reg, r≠10 → r≠11 → r≠12 → r≠13 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (word) 0x80000ace#32
  let c2 := c1.wr 11 (half) 0x80000ad2#32
  let c3 := c2.wr 12 (byte) 0x80000ad6#32
  let c4 := c3.wr 13 (0#32) 0x80000ada#32
  let r1 := ramWrite ram (sp+3960#32) (word) .w
  let c5 := c4.goto 0x80000ade#32
  let r2 := ramWrite r1 (sp+3964#32) (half) .h
  let c6 := c5.goto 0x80000ae2#32
  let r3 := ramWrite r2 (sp+3966#32) (byte) .b
  let c7 := c6.goto 0x80000ae6#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact sn2147486410) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v8 : c.get 8=sp+3204#32 := by simp [Core.wr_get_ne,Core.wr_get,h8,h9,h18]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+1692#32=4896#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1224 aligned) (Memory.block_access stack (off := 4896) (by decide) (by decide)),hword];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000ace#32).getLsbD 0=false;decide) sn2147486414 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v8 : c1.get 8=sp+3204#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+1696#32=4900#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned sp 2450 (by omega)) (Memory.block_access stack (off := 4900) (by decide) (by decide)),hhalf];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80000ad2#32).getLsbD 0=false;decide) sn2147486418 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v8 : c2.get 8=sp+3204#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+1698#32=4902#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access stack (off := 4902) (by decide) (by decide)),hbyte];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80000ad6#32).getLsbD 0=false;decide) sn2147486422 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v9 : c3.get 9=3#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
    have v18 : c3.get 18=0#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
    rw [exec_op,v9,v18];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,r1⟩ := by
    refine Quiet.step_of (by change (0x80000ada#32).getLsbD 0=false;decide) sn2147486426 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 r1 [],[]⟩
    have v8 : c4.get 8=sp+3204#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
    have v10 : c4.get 10=word := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
    rw [exec_store,v8,v10,BitVec.add_assoc,show 3204#32+756#32=3960#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 990 aligned) (Memory.block_access stack (off := 3960) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r1⟩ ⟨c6,r2⟩ := by
    refine Quiet.step_of (by change (0x80000ade#32).getLsbD 0=false;decide) sn2147486430 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r1 0 [] [] = ⟨.ok c6 r2 [],[]⟩
    have v8 : c5.get 8=sp+3204#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
    have v11 : c5.get 11=half := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
    rw [exec_store,v8,v11,BitVec.add_assoc,show 3204#32+760#32=3964#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned sp 1982 (by omega)) (Memory.block_access stack (off := 3964) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r2⟩ ⟨c7,r3⟩ := by
    refine Quiet.step_of (by change (0x80000ae2#32).getLsbD 0=false;decide) sn2147486434 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r2 0 [] [] = ⟨.ok c7 r3 [],[]⟩
    have v8 : c6.get 8=sp+3204#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
    have v12 : c6.get 12=byte := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
    rw [exec_store,v8,v12,BitVec.add_assoc,show 3204#32+762#32=3966#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access stack (off := 3966) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c7,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.single t6)))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
  · simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18]
  · intro reg h10 h11 h12 h13;simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h9,h18,h10,h11,h12,h13]
end E5R.Thermostat.RejectNextPackOne
