import Projects.thermostat.MainRequestBuildCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainRequestPaddingStores
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp b0 b1 b2 b3 b4 b5 b6 : Word) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (sp+3609#32) (b0) .b) (sp+3610#32) (b1) .b) (sp+3611#32) (b2) .b) (sp+3612#32) (b3) .b) (sp+3613#32) (b4) .b) (sp+3614#32) (b5) .b) (sp+3615#32) (b6) .b

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp b0 b1 b2 b3 b4 b5 b6 : Word) (h8 : c.get 8=sp+3204#32) (stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0) (h2 : c.get 2=sp)
(h10 : c.get 10=b0) (h11 : c.get 11=b1) (h12 : c.get 12=b2) (h13 : c.get 13=b3) (h14 : c.get 14=b4) (h15 : c.get 15=b5) (h16 : c.get 16=b6)
    (hp : c.pc=0x800011fe#32) :
    ∃ d, Quiet.Steps B img 9 ⟨c,ram⟩ ⟨d,memory ram sp b0 b1 b2 b3 b4 b5 b6⟩ ∧ d.pc=0x80001222#32 ∧
      d.get 17=sp+3609#32 ∧ (∀ r : Reg, r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 17 (sp+2047#32) 0x80001202#32
  let c2 := c1.wr 17 (sp+3609#32) 0x80001206#32
  let r1 := ramWrite ram (sp+3609#32) (b0) .b
  let c3 := c2.goto 0x8000120a#32
  let r2 := ramWrite r1 (sp+3610#32) (b1) .b
  let c4 := c3.goto 0x8000120e#32
  let r3 := ramWrite r2 (sp+3611#32) (b2) .b
  let c5 := c4.goto 0x80001212#32
  let r4 := ramWrite r3 (sp+3612#32) (b3) .b
  let c6 := c5.goto 0x80001216#32
  let r5 := ramWrite r4 (sp+3613#32) (b4) .b
  let c7 := c6.goto 0x8000121a#32
  let r6 := ramWrite r5 (sp+3614#32) (b5) .b
  let c8 := c7.goto 0x8000121e#32
  let r7 := ramWrite r6 (sp+3615#32) (b6) .b
  let c9 := c8.goto 0x80001222#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147488254) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v2 : c.get 2=sp := by simp [Core.wr_get_ne,Core.wr_get,h8,h2,h10,h11,h12,h13,h14,h15,h16]
    rw [exec_opimm,v2];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80001202#32).getLsbD 0=false;decide) re2147488258 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v17 : c1.get 17=sp+2047#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h11,h12,h13,h14,h15,h16]
    rw [exec_opimm,v17]
    change Observed.interp B img o (Eff.done (c1.wr 17 ((sp+2047#32)+1562#32) 0x80001206#32)) ram 0 [] []=_
    rw [BitVec.add_assoc,show 2047#32+1562#32=3609#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,r1⟩ := by
    refine Quiet.step_of (by change (0x80001206#32).getLsbD 0=false;decide) re2147488262 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 r1 [],[]⟩
    have v17 : c2.get 17=sp+3609#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h11,h12,h13,h14,h15,h16]
    have v10 : c2.get 10=b0 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h11,h12,h13,h14,h15,h16]
    rw [exec_store,v17,v10,BitVec.add_assoc,show 3609#32+0#32=3609#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3609) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r1⟩ ⟨c4,r2⟩ := by
    refine Quiet.step_of (by change (0x8000120a#32).getLsbD 0=false;decide) re2147488266 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r1 0 [] [] = ⟨.ok c4 r2 [],[]⟩
    have v17 : c3.get 17=sp+3609#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h11,h12,h13,h14,h15,h16]
    have v11 : c3.get 11=b1 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h11,h12,h13,h14,h15,h16]
    rw [exec_store,v17,v11,BitVec.add_assoc,show 3609#32+1#32=3610#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3610) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r2⟩ ⟨c5,r3⟩ := by
    refine Quiet.step_of (by change (0x8000120e#32).getLsbD 0=false;decide) re2147488270 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r2 0 [] [] = ⟨.ok c5 r3 [],[]⟩
    have v17 : c4.get 17=sp+3609#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h11,h12,h13,h14,h15,h16]
    have v12 : c4.get 12=b2 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h11,h12,h13,h14,h15,h16]
    rw [exec_store,v17,v12,BitVec.add_assoc,show 3609#32+2#32=3611#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3611) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r3⟩ ⟨c6,r4⟩ := by
    refine Quiet.step_of (by change (0x80001212#32).getLsbD 0=false;decide) re2147488274 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r3 0 [] [] = ⟨.ok c6 r4 [],[]⟩
    have v17 : c5.get 17=sp+3609#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h11,h12,h13,h14,h15,h16]
    have v13 : c5.get 13=b3 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h11,h12,h13,h14,h15,h16]
    rw [exec_store,v17,v13,BitVec.add_assoc,show 3609#32+3#32=3612#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3612) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r4⟩ ⟨c7,r5⟩ := by
    refine Quiet.step_of (by change (0x80001216#32).getLsbD 0=false;decide) re2147488278 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r4 0 [] [] = ⟨.ok c7 r5 [],[]⟩
    have v17 : c6.get 17=sp+3609#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h11,h12,h13,h14,h15,h16]
    have v14 : c6.get 14=b4 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h11,h12,h13,h14,h15,h16]
    rw [exec_store,v17,v14,BitVec.add_assoc,show 3609#32+4#32=3613#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3613) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,r5⟩ ⟨c8,r6⟩ := by
    refine Quiet.step_of (by change (0x8000121a#32).getLsbD 0=false;decide) re2147488282 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r5 0 [] [] = ⟨.ok c8 r6 [],[]⟩
    have v17 : c7.get 17=sp+3609#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h11,h12,h13,h14,h15,h16]
    have v15 : c7.get 15=b5 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h11,h12,h13,h14,h15,h16]
    rw [exec_store,v17,v15,BitVec.add_assoc,show 3609#32+5#32=3614#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3614) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,r6⟩ ⟨c9,r7⟩ := by
    refine Quiet.step_of (by change (0x8000121e#32).getLsbD 0=false;decide) re2147488286 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r6 0 [] [] = ⟨.ok c9 r7 [],[]⟩
    have v17 : c8.get 17=sp+3609#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h11,h12,h13,h14,h15,h16]
    have v16 : c8.get 16=b6 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h11,h12,h13,h14,h15,h16]
    rw [exec_store,v17,v16,BitVec.add_assoc,show 3609#32+6#32=3615#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .b) o (Nat.mod_one _) (Memory.block_access stack (off := 3615) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c9,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.single t8)))))))),rfl,?_ ,?_ ,by rfl⟩
  · simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h11,h12,h13,h14,h15,h16]
  · intro reg h17;simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h11,h12,h13,h14,h15,h16,h17]
end E5R.Thermostat.MainRequestPaddingStores
