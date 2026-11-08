import Projects.thermostat.MainRequestBuildCode
import Projects.thermostat.QuietRam
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainRequestMetadataStores
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd : Word) :=
  ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ramWrite (ram) (sp+3616#32) (path) .w) (sp+3620#32) (pathLen) .w) (sp+3624#32) (query) .w) (sp+3628#32) (queryLen) .w) (sp+3322#32) (0#32) .h) (sp+3324#32) (0#32) .h) (sp+3326#32) (0#32) .h) (sp+3312#32) (tag) .w) (sp+3316#32) (pad) .w) (sp+3320#32) (low) .h) (sp+3328#32) (methodStart) .w) (sp+3332#32) (methodEnd) .w) (sp+3336#32) (targetStart) .w) (sp+3340#32) (targetEnd) .w

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd : Word) (h8 : c.get 8=sp+3204#32) (stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0)
(h2 : c.get 2=sp) (h10 : c.get 10=path) (h28 : c.get 28=pathLen) (h12 : c.get 12=query) (h13 : c.get 13=queryLen) (h16 : c.get 16=0#32) (h17 : c.get 17=0#32) (h14 : c.get 14=0#32) (h9 : c.get 9=tag) (h31 : c.get 31=pad) (h27 : c.get 27=low) (h7 : c.get 7=methodStart) (h11 : c.get 11=methodEnd) (h29 : c.get 29=targetStart) (h30 : c.get 30=targetEnd)
    (hp : c.pc=0x80001186#32) :
    ∃ d, Quiet.Steps B img 16 ⟨c,ram⟩ ⟨d,memory ram sp path pathLen query queryLen tag pad low methodStart methodEnd targetStart targetEnd⟩ ∧ d.pc=0x800011c4#32 ∧
      d.get 10=sp+3322#32 ∧ (∀ r : Reg, r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  let r1 := ramWrite ram (sp+3616#32) (path) .w
  let c1 := c.goto 0x8000118a#32
  let r2 := ramWrite r1 (sp+3620#32) (pathLen) .w
  let c2 := c1.goto 0x8000118e#32
  let r3 := ramWrite r2 (sp+3624#32) (query) .w
  let c3 := c2.goto 0x80001192#32
  let r4 := ramWrite r3 (sp+3628#32) (queryLen) .w
  let c4 := c3.goto 0x80001196#32
  let c5 := c4.wr 10 (sp+2047#32) 0x8000119a#32
  let c6 := c5.wr 10 (sp+3322#32) 0x8000119e#32
  let r5 := ramWrite r4 (sp+3322#32) (0#32) .h
  let c7 := c6.goto 0x800011a2#32
  let r6 := ramWrite r5 (sp+3324#32) (0#32) .h
  let c8 := c7.goto 0x800011a6#32
  let r7 := ramWrite r6 (sp+3326#32) (0#32) .h
  let c9 := c8.goto 0x800011aa#32
  let r8 := ramWrite r7 (sp+3312#32) (tag) .w
  let c10 := c9.goto 0x800011ac#32
  let r9 := ramWrite r8 (sp+3316#32) (pad) .w
  let c11 := c10.goto 0x800011b0#32
  let r10 := ramWrite r9 (sp+3320#32) (low) .h
  let c12 := c11.goto 0x800011b4#32
  let r11 := ramWrite r10 (sp+3328#32) (methodStart) .w
  let c13 := c12.goto 0x800011b8#32
  let r12 := ramWrite r11 (sp+3332#32) (methodEnd) .w
  let c14 := c13.goto 0x800011bc#32
  let r13 := ramWrite r12 (sp+3336#32) (targetStart) .w
  let c15 := c14.goto 0x800011c0#32
  let r14 := ramWrite r13 (sp+3340#32) (targetEnd) .w
  let c16 := c15.goto 0x800011c4#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,r1⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147488134) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 r1 [],[]⟩
    have v8 : c.get 8=sp+3204#32 := by simp [Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
    have v10 : c.get 10=path := by simp [Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
    rw [exec_store,v8,v10,BitVec.add_assoc,show 3204#32+412#32=3616#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 904 aligned) (Memory.block_access stack (off := 3616) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t1 : Quiet.Step B img ⟨c1,r1⟩ ⟨c2,r2⟩ := by
    refine Quiet.step_of (by change (0x8000118a#32).getLsbD 0=false;decide) re2147488138 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) r1 0 [] [] = ⟨.ok c2 r2 [],[]⟩
    have v8 : c1.get 8=sp+3204#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
    have v28 : c1.get 28=pathLen := by simp [c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
    rw [exec_store,v8,v28,BitVec.add_assoc,show 3204#32+416#32=3620#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 905 aligned) (Memory.block_access stack (off := 3620) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,r2⟩ ⟨c3,r3⟩ := by
    refine Quiet.step_of (by change (0x8000118e#32).getLsbD 0=false;decide) re2147488142 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) r2 0 [] [] = ⟨.ok c3 r3 [],[]⟩
    have v8 : c2.get 8=sp+3204#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
    have v12 : c2.get 12=query := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
    rw [exec_store,v8,v12,BitVec.add_assoc,show 3204#32+420#32=3624#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 906 aligned) (Memory.block_access stack (off := 3624) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t3 : Quiet.Step B img ⟨c3,r3⟩ ⟨c4,r4⟩ := by
    refine Quiet.step_of (by change (0x80001192#32).getLsbD 0=false;decide) re2147488146 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) r3 0 [] [] = ⟨.ok c4 r4 [],[]⟩
    have v8 : c3.get 8=sp+3204#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
    have v13 : c3.get 13=queryLen := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
    rw [exec_store,v8,v13,BitVec.add_assoc,show 3204#32+424#32=3628#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 907 aligned) (Memory.block_access stack (off := 3628) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r4⟩ ⟨c5,r4⟩ := by
    refine Quiet.step_of (by change (0x80001196#32).getLsbD 0=false;decide) re2147488150 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r4 0 [] [] = ⟨.ok c5 r4 [],[]⟩
    have v2 : c4.get 2=sp := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
    rw [exec_opimm,v2];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r4⟩ ⟨c6,r4⟩ := by
    refine Quiet.step_of (by change (0x8000119a#32).getLsbD 0=false;decide) re2147488154 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r4 0 [] [] = ⟨.ok c6 r4 [],[]⟩
    have v10 : c5.get 10=sp+2047#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
    rw [exec_opimm,v10]
    change Observed.interp B img o (Eff.done (c5.wr 10 ((sp+2047#32)+1275#32) 0x8000119e#32)) r4 0 [] []=_
    rw [BitVec.add_assoc,show 2047#32+1275#32=3322#32 by decide +kernel];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r4⟩ ⟨c7,r5⟩ := by
    refine Quiet.step_of (by change (0x8000119e#32).getLsbD 0=false;decide) re2147488158 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r4 0 [] [] = ⟨.ok c7 r5 [],[]⟩
    have v10 : c6.get 10=sp+3322#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
    have v16 : c6.get 16=0#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
    rw [exec_store,v10,v16,BitVec.add_assoc,show 3322#32+0#32=3322#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned sp 1661 (by omega)) (Memory.block_access stack (off := 3322) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,r5⟩ ⟨c8,r6⟩ := by
    refine Quiet.step_of (by change (0x800011a2#32).getLsbD 0=false;decide) re2147488162 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r5 0 [] [] = ⟨.ok c8 r6 [],[]⟩
    have v10 : c7.get 10=sp+3322#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
    have v17 : c7.get 17=0#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
    rw [exec_store,v10,v17,BitVec.add_assoc,show 3322#32+2#32=3324#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned sp 1662 (by omega)) (Memory.block_access stack (off := 3324) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,r6⟩ ⟨c9,r7⟩ := by
    refine Quiet.step_of (by change (0x800011a6#32).getLsbD 0=false;decide) re2147488166 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r6 0 [] [] = ⟨.ok c9 r7 [],[]⟩
    have v10 : c8.get 10=sp+3322#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
    have v14 : c8.get 14=0#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
    rw [exec_store,v10,v14,BitVec.add_assoc,show 3322#32+4#32=3326#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned sp 1663 (by omega)) (Memory.block_access stack (off := 3326) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,r7⟩ ⟨c10,r8⟩ := by
    refine Quiet.step_of (by change (0x800011aa#32).getLsbD 0=false;decide) re2147488170 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) r7 0 [] [] = ⟨.ok c10 r8 [],[]⟩
    have v8 : c9.get 8=sp+3204#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
    have v9 : c9.get 9=tag := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
    rw [exec_store,v8,v9,BitVec.add_assoc,show 3204#32+108#32=3312#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 828 aligned) (Memory.block_access stack (off := 3312) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,r8⟩ ⟨c11,r9⟩ := by
    refine Quiet.step_of (by change (0x800011ac#32).getLsbD 0=false;decide) re2147488172 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) r8 0 [] [] = ⟨.ok c11 r9 [],[]⟩
    have v8 : c10.get 8=sp+3204#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
    have v31 : c10.get 31=pad := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
    rw [exec_store,v8,v31,BitVec.add_assoc,show 3204#32+112#32=3316#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 829 aligned) (Memory.block_access stack (off := 3316) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,r9⟩ ⟨c12,r10⟩ := by
    refine Quiet.step_of (by change (0x800011b0#32).getLsbD 0=false;decide) re2147488176 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) r9 0 [] [] = ⟨.ok c12 r10 [],[]⟩
    have v8 : c11.get 8=sp+3204#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
    have v27 : c11.get 27=low := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
    rw [exec_store,v8,v27,BitVec.add_assoc,show 3204#32+116#32=3320#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned sp 1660 (by omega)) (Memory.block_access stack (off := 3320) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t12 : Quiet.Step B img ⟨c12,r10⟩ ⟨c13,r11⟩ := by
    refine Quiet.step_of (by change (0x800011b4#32).getLsbD 0=false;decide) re2147488180 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) r10 0 [] [] = ⟨.ok c13 r11 [],[]⟩
    have v8 : c12.get 8=sp+3204#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
    have v7 : c12.get 7=methodStart := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
    rw [exec_store,v8,v7,BitVec.add_assoc,show 3204#32+124#32=3328#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 832 aligned) (Memory.block_access stack (off := 3328) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,r11⟩ ⟨c14,r12⟩ := by
    refine Quiet.step_of (by change (0x800011b8#32).getLsbD 0=false;decide) re2147488184 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) r11 0 [] [] = ⟨.ok c14 r12 [],[]⟩
    have v8 : c13.get 8=sp+3204#32 := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
    have v11 : c13.get 11=methodEnd := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
    rw [exec_store,v8,v11,BitVec.add_assoc,show 3204#32+128#32=3332#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 833 aligned) (Memory.block_access stack (off := 3332) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,r12⟩ ⟨c15,r13⟩ := by
    refine Quiet.step_of (by change (0x800011bc#32).getLsbD 0=false;decide) re2147488188 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) r12 0 [] [] = ⟨.ok c15 r13 [],[]⟩
    have v8 : c14.get 8=sp+3204#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
    have v29 : c14.get 29=targetStart := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
    rw [exec_store,v8,v29,BitVec.add_assoc,show 3204#32+132#32=3336#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 834 aligned) (Memory.block_access stack (off := 3336) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t15 : Quiet.Step B img ⟨c15,r13⟩ ⟨c16,r14⟩ := by
    refine Quiet.step_of (by change (0x800011c0#32).getLsbD 0=false;decide) re2147488192 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) r13 0 [] [] = ⟨.ok c16 r14 [],[]⟩
    have v8 : c15.get 8=sp+3204#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
    have v30 : c15.get 30=targetEnd := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
    rw [exec_store,v8,v30,BitVec.add_assoc,show 3204#32+136#32=3340#32 by decide +kernel,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 835 aligned) (Memory.block_access stack (off := 3340) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  refine ⟨c16,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.single t15))))))))))))))),rfl,?_ ,?_ ,by rfl⟩
  · simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30]
  · intro reg h10;simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h8,h2,h10,h28,h12,h13,h16,h17,h14,h9,h31,h27,h7,h11,h29,h30,h10]
end E5R.Thermostat.MainRequestMetadataStores
