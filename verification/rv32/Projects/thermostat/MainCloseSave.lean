import Projects.thermostat.MainCloseCode
import Projects.thermostat.QuietRam

import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainCloseSave
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp : Word) (origin : Core) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (sp+44#32) (origin.get 8) .w) (sp+40#32) (origin.get 9) .w) (sp+36#32) (origin.get 18) .w) (sp+32#32) (origin.get 19) .w) (sp+28#32) (origin.get 20) .w) (sp+24#32) (origin.get 21) .w) (sp+20#32) (origin.get 22) .w) (sp+16#32) (origin.get 23) .w) (sp+12#32) (origin.get 24) .w) (sp+8#32) (origin.get 25) .w) (sp+4#32) (origin.get 26) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (origin : Core) (same : c=origin) (h2 : c.get 2=sp+48#32) (stack : Memory.Block B sp 48) (aligned : sp.toNat%4=0)
    (hp : c.pc=0x800023f2#32) :
    ∃ d, Quiet.Steps B img 12 ⟨c,ram⟩ ⟨d,memory ram sp origin⟩ ∧ d.pc=0x8000240a#32 ∧
      d.get 2=sp ∧ (∀ r : Reg, r≠2 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 2 (sp) 0x800023f4#32
  let r1 := ramWrite ram (sp+44#32) (origin.get 8) .w
  let c2 := c1.goto 0x800023f6#32
  let r2 := ramWrite r1 (sp+40#32) (origin.get 9) .w
  let c3 := c2.goto 0x800023f8#32
  let r3 := ramWrite r2 (sp+36#32) (origin.get 18) .w
  let c4 := c3.goto 0x800023fa#32
  let r4 := ramWrite r3 (sp+32#32) (origin.get 19) .w
  let c5 := c4.goto 0x800023fc#32
  let r5 := ramWrite r4 (sp+28#32) (origin.get 20) .w
  let c6 := c5.goto 0x800023fe#32
  let r6 := ramWrite r5 (sp+24#32) (origin.get 21) .w
  let c7 := c6.goto 0x80002400#32
  let r7 := ramWrite r6 (sp+20#32) (origin.get 22) .w
  let c8 := c7.goto 0x80002402#32
  let r8 := ramWrite r7 (sp+16#32) (origin.get 23) .w
  let c9 := c8.goto 0x80002404#32
  let r9 := ramWrite r8 (sp+12#32) (origin.get 24) .w
  let c10 := c9.goto 0x80002406#32
  let r10 := ramWrite r9 (sp+8#32) (origin.get 25) .w
  let c11 := c10.goto 0x80002408#32
  let r11 := ramWrite r10 (sp+4#32) (origin.get 26) .w
  let c12 := c11.goto 0x8000240a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147492850) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v2 : c.get 2=sp+48#32 := by simp [Core.wr_get_ne,Core.wr_get,h2,←same]
    rw [exec_opimm,v2,hp]
    change Observed.interp B img o (.done (c.wr 2 ((sp+48#32)+0xffffffd0#32) 0x800023f4#32)) ram 0 [] []=_
    rw [BitVec.add_assoc,show 48#32+0xffffffd0#32=0#32 by decide +kernel,BitVec.add_zero];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,r1⟩ := by
    refine Quiet.step_of (by change (0x800023f4#32).getLsbD 0=false;decide) re2147492852 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 r1 [],[]⟩
    have v2 : c1.get 2=sp := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    have v8 : c1.get 8=origin.get 8 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    rw [exec_store,v2,v8,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 11 aligned) (Memory.block_access stack (off := 44) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,r1⟩ ⟨c3,r2⟩ := by
    refine Quiet.step_of (by change (0x800023f6#32).getLsbD 0=false;decide) re2147492854 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) r1 0 [] [] = ⟨.ok c3 r2 [],[]⟩
    have v2 : c2.get 2=sp := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    have v9 : c2.get 9=origin.get 9 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    rw [exec_store,v2,v9,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 10 aligned) (Memory.block_access stack (off := 40) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r2⟩ ⟨c4,r3⟩ := by
    refine Quiet.step_of (by change (0x800023f8#32).getLsbD 0=false;decide) re2147492856 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r2 0 [] [] = ⟨.ok c4 r3 [],[]⟩
    have v2 : c3.get 2=sp := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    have v18 : c3.get 18=origin.get 18 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    rw [exec_store,v2,v18,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 9 aligned) (Memory.block_access stack (off := 36) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r3⟩ ⟨c5,r4⟩ := by
    refine Quiet.step_of (by change (0x800023fa#32).getLsbD 0=false;decide) re2147492858 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r3 0 [] [] = ⟨.ok c5 r4 [],[]⟩
    have v2 : c4.get 2=sp := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    have v19 : c4.get 19=origin.get 19 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    rw [exec_store,v2,v19,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 8 aligned) (Memory.block_access stack (off := 32) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r4⟩ ⟨c6,r5⟩ := by
    refine Quiet.step_of (by change (0x800023fc#32).getLsbD 0=false;decide) re2147492860 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r4 0 [] [] = ⟨.ok c6 r5 [],[]⟩
    have v2 : c5.get 2=sp := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    have v20 : c5.get 20=origin.get 20 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    rw [exec_store,v2,v20,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 7 aligned) (Memory.block_access stack (off := 28) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r5⟩ ⟨c7,r6⟩ := by
    refine Quiet.step_of (by change (0x800023fe#32).getLsbD 0=false;decide) re2147492862 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r5 0 [] [] = ⟨.ok c7 r6 [],[]⟩
    have v2 : c6.get 2=sp := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    have v21 : c6.get 21=origin.get 21 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    rw [exec_store,v2,v21,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 6 aligned) (Memory.block_access stack (off := 24) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,r6⟩ ⟨c8,r7⟩ := by
    refine Quiet.step_of (by change (0x80002400#32).getLsbD 0=false;decide) re2147492864 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r6 0 [] [] = ⟨.ok c8 r7 [],[]⟩
    have v2 : c7.get 2=sp := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    have v22 : c7.get 22=origin.get 22 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    rw [exec_store,v2,v22,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 5 aligned) (Memory.block_access stack (off := 20) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,r7⟩ ⟨c9,r8⟩ := by
    refine Quiet.step_of (by change (0x80002402#32).getLsbD 0=false;decide) re2147492866 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r7 0 [] [] = ⟨.ok c9 r8 [],[]⟩
    have v2 : c8.get 2=sp := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    have v23 : c8.get 23=origin.get 23 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    rw [exec_store,v2,v23,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 4 aligned) (Memory.block_access stack (off := 16) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,r8⟩ ⟨c10,r9⟩ := by
    refine Quiet.step_of (by change (0x80002404#32).getLsbD 0=false;decide) re2147492868 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) r8 0 [] [] = ⟨.ok c10 r9 [],[]⟩
    have v2 : c9.get 2=sp := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    have v24 : c9.get 24=origin.get 24 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    rw [exec_store,v2,v24,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 3 aligned) (Memory.block_access stack (off := 12) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,r9⟩ ⟨c11,r10⟩ := by
    refine Quiet.step_of (by change (0x80002406#32).getLsbD 0=false;decide) re2147492870 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) r9 0 [] [] = ⟨.ok c11 r10 [],[]⟩
    have v2 : c10.get 2=sp := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    have v25 : c10.get 25=origin.get 25 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    rw [exec_store,v2,v25,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 2 aligned) (Memory.block_access stack (off := 8) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,r10⟩ ⟨c12,r11⟩ := by
    refine Quiet.step_of (by change (0x80002408#32).getLsbD 0=false;decide) re2147492872 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) r10 0 [] [] = ⟨.ok c12 r11 [],[]⟩
    have v2 : c11.get 2=sp := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    have v26 : c11.get 26=origin.get 26 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
    rw [exec_store,v2,v26,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1 aligned) (Memory.block_access stack (off := 4) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c12,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.single t11))))))))))),rfl,?_ ,?_ ,by rfl⟩
  · simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same]
  · intro reg h2;simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,←same,h2]

theorem frame (ram : Word → BitVec 8) (sp : Word) (c : Core) (x : Word)
    (outside : ∀ i : Fin 48, x≠sp+BitVec.ofNat 32 i.val) : memory ram sp c x=ram x := by
  unfold memory
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact outside ⟨4+i,by omega⟩)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact outside ⟨8+i,by omega⟩)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact outside ⟨12+i,by omega⟩)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact outside ⟨16+i,by omega⟩)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact outside ⟨20+i,by omega⟩)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact outside ⟨24+i,by omega⟩)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact outside ⟨28+i,by omega⟩)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact outside ⟨32+i,by omega⟩)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact outside ⟨36+i,by omega⟩)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact outside ⟨40+i,by omega⟩)]
  rw [ramWrite_w_other _ _ _ _ (by intro i hi;rw [BitVec.add_assoc,←BitVec.ofNat_add];exact outside ⟨44+i,by omega⟩)]

theorem saved8 (ram : Word → BitVec 8) (sp : Word) (c : Core) : ramRead (memory ram sp c) (sp+44#32) .w=c.get 8 := by
  unfold memory
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 44 4 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 44 8 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 44 12 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 44 16 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 44 20 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 44 24 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 44 28 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 44 32 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 44 36 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 44 40 (by decide) (by decide) (by decide) (by decide) (by decide))]
  exact ramRead_ramWrite_w _ _ _

theorem saved9 (ram : Word → BitVec 8) (sp : Word) (c : Core) : ramRead (memory ram sp c) (sp+40#32) .w=c.get 9 := by
  unfold memory
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 40 4 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 40 8 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 40 12 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 40 16 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 40 20 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 40 24 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 40 28 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 40 32 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 40 36 (by decide) (by decide) (by decide) (by decide) (by decide))]
  exact ramRead_ramWrite_w _ _ _

theorem saved18 (ram : Word → BitVec 8) (sp : Word) (c : Core) : ramRead (memory ram sp c) (sp+36#32) .w=c.get 18 := by
  unfold memory
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 36 4 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 36 8 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 36 12 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 36 16 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 36 20 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 36 24 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 36 28 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 36 32 (by decide) (by decide) (by decide) (by decide) (by decide))]
  exact ramRead_ramWrite_w _ _ _

theorem saved19 (ram : Word → BitVec 8) (sp : Word) (c : Core) : ramRead (memory ram sp c) (sp+32#32) .w=c.get 19 := by
  unfold memory
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 32 4 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 32 8 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 32 12 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 32 16 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 32 20 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 32 24 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 32 28 (by decide) (by decide) (by decide) (by decide) (by decide))]
  exact ramRead_ramWrite_w _ _ _

theorem saved20 (ram : Word → BitVec 8) (sp : Word) (c : Core) : ramRead (memory ram sp c) (sp+28#32) .w=c.get 20 := by
  unfold memory
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 28 4 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 28 8 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 28 12 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 28 16 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 28 20 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 28 24 (by decide) (by decide) (by decide) (by decide) (by decide))]
  exact ramRead_ramWrite_w _ _ _

theorem saved21 (ram : Word → BitVec 8) (sp : Word) (c : Core) : ramRead (memory ram sp c) (sp+24#32) .w=c.get 21 := by
  unfold memory
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 24 4 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 24 8 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 24 12 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 24 16 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 24 20 (by decide) (by decide) (by decide) (by decide) (by decide))]
  exact ramRead_ramWrite_w _ _ _

theorem saved22 (ram : Word → BitVec 8) (sp : Word) (c : Core) : ramRead (memory ram sp c) (sp+20#32) .w=c.get 22 := by
  unfold memory
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 20 4 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 20 8 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 20 12 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 20 16 (by decide) (by decide) (by decide) (by decide) (by decide))]
  exact ramRead_ramWrite_w _ _ _

theorem saved23 (ram : Word → BitVec 8) (sp : Word) (c : Core) : ramRead (memory ram sp c) (sp+16#32) .w=c.get 23 := by
  unfold memory
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 16 4 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 16 8 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 16 12 (by decide) (by decide) (by decide) (by decide) (by decide))]
  exact ramRead_ramWrite_w _ _ _

theorem saved24 (ram : Word → BitVec 8) (sp : Word) (c : Core) : ramRead (memory ram sp c) (sp+12#32) .w=c.get 24 := by
  unfold memory
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 12 4 (by decide) (by decide) (by decide) (by decide) (by decide))]
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 12 8 (by decide) (by decide) (by decide) (by decide) (by decide))]
  exact ramRead_ramWrite_w _ _ _

theorem saved25 (ram : Word → BitVec 8) (sp : Word) (c : Core) : ramRead (memory ram sp c) (sp+8#32) .w=c.get 25 := by
  unfold memory
  rw [Memory.read_word_write_other _ _ _ _ (Memory.word_disjoint sp 8 4 (by decide) (by decide) (by decide) (by decide) (by decide))]
  exact ramRead_ramWrite_w _ _ _

theorem saved26 (ram : Word → BitVec 8) (sp : Word) (c : Core) : ramRead (memory ram sp c) (sp+4#32) .w=c.get 26 := by
  unfold memory
  exact ramRead_ramWrite_w _ _ _
end E5R.Thermostat.MainCloseSave
