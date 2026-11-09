import Projects.thermostat.MainNextLengthPayloadWords
import Projects.thermostat.MainServeNextCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.RejectNextFront
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp word half : Word) :=
  ramWrite (ramWrite (ramWrite (ram) (sp+3652#32) (1#32) .b) (sp+4232#32) (word) .w) (sp+4236#32) (half) .h

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp word half : Word) (h8 : c.get 8=sp+3204#32) (h22 : c.get 22=1#32) (hword : ramRead ram (sp+5168#32) .w=word) (hhalf : extend .h true (ramRead ram (sp+5172#32) .h)=half)
(stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0)
    (hp : c.pc=0x80000a9a#32) :
    ∃ d, Quiet.Steps B img 5 ⟨c,ram⟩ ⟨d,memory ram sp word half⟩ ∧ d.pc=0x80000aae#32 ∧
      d.get 10=word ∧ d.get 11=half ∧ (∀ r : Reg, r≠10 → r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 10 (word) 0x80000a9e#32
  let c2 := c1.wr 11 (half) 0x80000aa2#32
  let r1 := ramWrite ram (sp+3652#32) (1#32) .b
  let c3 := c2.goto 0x80000aa6#32
  let r2 := ramWrite r1 (sp+4232#32) (word) .w
  let c4 := c3.goto 0x80000aaa#32
  let r3 := ramWrite r2 (sp+4236#32) (half) .h
  let c5 := c4.goto 0x80000aae#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact sn2147486362) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v8 : c.get 8=sp+3204#32 := by simp [Core.wr_get_ne,Core.wr_get,h8,h22]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+1964#32=5168#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1292 aligned) (Memory.block_access stack (off := 5168) (by decide) (by decide)),hword];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80000a9e#32).getLsbD 0=false;decide) sn2147486366 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v8 : c1.get 8=sp+3204#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h22]
    rw [exec_load,v8,BitVec.add_assoc,show 3204#32+1968#32=5172#32 by decide +kernel,Quiet.interp_load_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned sp 2586 (by omega)) (Memory.block_access stack (off := 5172) (by decide) (by decide)),hhalf];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,r1⟩ := by
    refine Quiet.step_of (by change (0x80000aa2#32).getLsbD 0=false;decide) sn2147486370 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 r1 [],[]⟩
    have v8 : c2.get 8=sp+3204#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h22]
    have v22 : c2.get 22=1#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h22]
    rw [exec_store,v8,v22,BitVec.add_assoc,show 3204#32+448#32=3652#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (by exact Nat.mod_one _) (Memory.block_access stack (off := 3652) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r1⟩ ⟨c4,r2⟩ := by
    refine Quiet.step_of (by change (0x80000aa6#32).getLsbD 0=false;decide) sn2147486374 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r1 0 [] [] = ⟨.ok c4 r2 [],[]⟩
    have v8 : c3.get 8=sp+3204#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h22]
    have v10 : c3.get 10=word := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h22]
    rw [exec_store,v8,v10,BitVec.add_assoc,show 3204#32+1028#32=4232#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1058 aligned) (Memory.block_access stack (off := 4232) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r2⟩ ⟨c5,r3⟩ := by
    refine Quiet.step_of (by change (0x80000aaa#32).getLsbD 0=false;decide) sn2147486378 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r2 0 [] [] = ⟨.ok c5 r3 [],[]⟩
    have v8 : c4.get 8=sp+3204#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h22]
    have v11 : c4.get 11=half := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h22]
    rw [exec_store,v8,v11,BitVec.add_assoc,show 3204#32+1032#32=4236#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned sp 2118 (by omega)) (Memory.block_access stack (off := 4236) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c5,.step t0 (.step t1 (.step t2 (.step t3 (.single t4)))),rfl,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h22]
  · simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h22]
  · intro reg h10 h11;simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h22,h10,h11]
end E5R.Thermostat.RejectNextFront
