import Projects.thermostat.HttpDecCode
import Projects.thermostat.QuietRam
import Projects.thermostat.HttpDecMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HttpDecLeading0
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp : Word) :=
  ramWrite (ramWrite (ramWrite (ram) (sp+4#32) (0#32) .w) (sp+8#32) (0#32) .w) (sp+12#32) (0#32) .h

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (n : Nat) (hn : n≤832) (h2 : c.get 2=(sp+16#32)) (h13 : c.get 13=(BitVec.ofNat 32 n)) (hm : Memory.Block B sp 16) (ha : sp.toNat%4=0)
    (hp : c.pc=0x80004180#32) :
    ∃ d, Quiet.Steps B img 30 ⟨c,ram⟩ ⟨d,memory ram sp⟩ ∧ d.pc=0x8000447a#32 ∧
      d.get 2=sp ∧ d.get 14=3518435328#32 ∧ d.get 15=429496730#32 ∧ d.get 16=0#32 ∧ d.get 17=0#32 ∧ (∀ r : Reg, r≠2 → r≠14 → r≠15 → r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 2 (sp) 0x80004182#32
  let c2 := c1.wr 14 (1000001536#32) 0x80004186#32
  let c3 := c2.wr 14 (999999999#32) 0x8000418a#32
  let r1 := ramWrite ram (sp+4#32) (0#32) .w
  let c4 := c3.goto 0x8000418c#32
  let r2 := ramWrite r1 (sp+8#32) (0#32) .w
  let c5 := c4.goto 0x8000418e#32
  let r3 := ramWrite r2 (sp+12#32) (0#32) .h
  let c6 := c5.goto 0x80004192#32
  let c7 := c6.goto 0x800041e0#32
  let c8 := c7.wr 14 (99999744#32) 0x800041e4#32
  let c9 := c8.wr 14 (100000000#32) 0x800041e8#32
  let c10 := c9.goto 0x80004404#32
  let c11 := c10.wr 14 (9998336#32) 0x80004408#32
  let c12 := c11.wr 14 (10000000#32) 0x8000440c#32
  let c13 := c12.goto 0x80004410#32
  let c14 := c13.wr 14 (999424#32) 0x80004414#32
  let c15 := c14.wr 14 (1000000#32) 0x80004418#32
  let c16 := c15.goto 0x8000441c#32
  let c17 := c16.wr 14 (175923200#32) 0x80004420#32
  let c18 := c17.wr 15 (((BitVec.ofNat 32 n) >>> 5)) 0x80004424#32
  let c19 := c18.wr 14 (175921861#32) 0x80004428#32
  let c20 := c19.wr 14 ((muldiv .mulhu (((BitVec.ofNat 32 n) >>> 5)) (175921861#32))) 0x8000442c#32
  let c21 := c20.wr 15 (429498368#32) 0x80004430#32
  let c22 := c21.wr 14 (0#32) 0x80004432#32
  let c23 := c22.wr 15 (429496730#32) 0x80004436#32
  let c24 := c23.wr 16 (0#32) 0x8000443a#32
  let c25 := c24.wr 17 (0#32) 0x8000443e#32
  let c26 := c25.wr 16 (0#32) 0x80004440#32
  let c27 := c26.wr 16 (0#32) 0x80004442#32
  let c28 := c27.wr 14 (0#32) 0x80004446#32
  let c29 := c28.goto 0x80004476#32
  let c30 := c29.wr 14 (3518435328#32) 0x8000447a#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact de2147500416) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v2 : c.get 2=(sp+16#32) := by simp [Core.wr_get_ne,Core.wr_get,h2,h13]
    rw [exec_opimm,v2]
    change Observed.interp B img o (.done (c.wr 2 (alu .add ((sp+16#32)) (4294967280#32)) (c.pc+2#32))) ram 0 [] [] = _
    rw [(by simp [alu,BitVec.add_assoc,show 16#32+4294967280#32=0#32 by decide +kernel] : alu .add ((sp+16#32)) (4294967280#32)=sp)]
    first | rfl | (rw [hp]; rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x80004182#32).getLsbD 0=false;decide) de2147500418 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80004186#32).getLsbD 0=false;decide) de2147500422 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v14 : c2.get 14=1000001536#32 := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
    rw [exec_opimm,v14]
    change Observed.interp B img o (.done (c2.wr 14 (alu .add (1000001536#32) (4294965759#32)) (c2.pc+4#32))) ram 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,r1⟩ := by
    refine Quiet.step_of (by change (0x8000418a#32).getLsbD 0=false;decide) de2147500426 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 r1 [],[]⟩
    have v2 : c3.get 2=sp := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
    rw [exec_store,v2,Core.get_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 1 ha) (Memory.block_access hm (off := 4) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t4 : Quiet.Step B img ⟨c4,r1⟩ ⟨c5,r2⟩ := by
    refine Quiet.step_of (by change (0x8000418c#32).getLsbD 0=false;decide) de2147500428 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) r1 0 [] [] = ⟨.ok c5 r2 [],[]⟩
    have v2 : c4.get 2=sp := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
    rw [exec_store,v2,Core.get_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .w) o (Memory.word_aligned sp 2 ha) (Memory.block_access hm (off := 8) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t5 : Quiet.Step B img ⟨c5,r2⟩ ⟨c6,r3⟩ := by
    refine Quiet.step_of (by change (0x8000418e#32).getLsbD 0=false;decide) de2147500430 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) r2 0 [] [] = ⟨.ok c6 r3 [],[]⟩
    have v2 : c5.get 2=sp := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
    rw [exec_store,v2,Core.get_zero,Quiet.interp_store_ram (B := B) (img := img) (w := .h) o (Memory.half_aligned sp 6 (by omega)) (Memory.block_access hm (off := 12) (by decide) (by decide))];first | rfl | (rw [hp];rfl)
  have t6 : Quiet.Step B img ⟨c6,r3⟩ ⟨c7,r3⟩ := by
    refine Quiet.step_of (by change (0x80004192#32).getLsbD 0=false;decide) de2147500434 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) r3 0 [] [] = ⟨.ok c7 r3 [],[]⟩
    have v14 : c6.get 14=999999999#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
    have v13 : c6.get 13=(BitVec.ofNat 32 n) := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
    rw [exec_branch,v14,v13,(by rw [HttpDecMath.branch_geu 999999999 n (by omega) (by omega)];exact decide_eq_true (by omega) : taken .geu (999999999#32) ((BitVec.ofNat 32 n))=true)]
    simp only [ite_true]
    rw [show c6.pc=2147500434#32 by rfl,show 2147500434#32+78#32=2147500512#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t7 : Quiet.Step B img ⟨c7,r3⟩ ⟨c8,r3⟩ := by
    refine Quiet.step_of (by change (0x800041e0#32).getLsbD 0=false;decide) de2147500512 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) r3 0 [] [] = ⟨.ok c8 r3 [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t8 : Quiet.Step B img ⟨c8,r3⟩ ⟨c9,r3⟩ := by
    refine Quiet.step_of (by change (0x800041e4#32).getLsbD 0=false;decide) de2147500516 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) r3 0 [] [] = ⟨.ok c9 r3 [],[]⟩
    have v14 : c8.get 14=99999744#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
    rw [exec_opimm,v14]
    change Observed.interp B img o (.done (c8.wr 14 (alu .add (99999744#32) (256#32)) (c8.pc+4#32))) r3 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t9 : Quiet.Step B img ⟨c9,r3⟩ ⟨c10,r3⟩ := by
    refine Quiet.step_of (by change (0x800041e8#32).getLsbD 0=false;decide) de2147500520 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) r3 0 [] [] = ⟨.ok c10 r3 [],[]⟩
    have v13 : c9.get 13=(BitVec.ofNat 32 n) := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
    have v14 : c9.get 14=100000000#32 := by simp [c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
    rw [exec_branch,v13,v14,(by rw [HttpDecMath.branch_ltu n 100000000 (by omega) (by omega)];exact decide_eq_true (by omega) : taken .ltu ((BitVec.ofNat 32 n)) (100000000#32)=true)]
    simp only [ite_true]
    rw [show c9.pc=2147500520#32 by rfl,show 2147500520#32+540#32=2147501060#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,r3⟩ ⟨c11,r3⟩ := by
    refine Quiet.step_of (by change (0x80004404#32).getLsbD 0=false;decide) de2147501060 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) r3 0 [] [] = ⟨.ok c11 r3 [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t11 : Quiet.Step B img ⟨c11,r3⟩ ⟨c12,r3⟩ := by
    refine Quiet.step_of (by change (0x80004408#32).getLsbD 0=false;decide) de2147501064 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) r3 0 [] [] = ⟨.ok c12 r3 [],[]⟩
    have v14 : c11.get 14=9998336#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
    rw [exec_opimm,v14]
    change Observed.interp B img o (.done (c11.wr 14 (alu .add (9998336#32) (1664#32)) (c11.pc+4#32))) r3 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t12 : Quiet.Step B img ⟨c12,r3⟩ ⟨c13,r3⟩ := by
    refine Quiet.step_of (by change (0x8000440c#32).getLsbD 0=false;decide) de2147501068 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) r3 0 [] [] = ⟨.ok c13 r3 [],[]⟩
    have v13 : c12.get 13=(BitVec.ofNat 32 n) := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
    have v14 : c12.get 14=10000000#32 := by simp [c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
    rw [exec_branch,v13,v14,(by rw [HttpDecMath.branch_geu n 10000000 (by omega) (by omega)];exact decide_eq_false (by omega) : taken .geu ((BitVec.ofNat 32 n)) (10000000#32)=false)]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,r3⟩ ⟨c14,r3⟩ := by
    refine Quiet.step_of (by change (0x80004410#32).getLsbD 0=false;decide) de2147501072 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) r3 0 [] [] = ⟨.ok c14 r3 [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t14 : Quiet.Step B img ⟨c14,r3⟩ ⟨c15,r3⟩ := by
    refine Quiet.step_of (by change (0x80004414#32).getLsbD 0=false;decide) de2147501076 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) r3 0 [] [] = ⟨.ok c15 r3 [],[]⟩
    have v14 : c14.get 14=999424#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
    rw [exec_opimm,v14]
    change Observed.interp B img o (.done (c14.wr 14 (alu .add (999424#32) (576#32)) (c14.pc+4#32))) r3 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t15 : Quiet.Step B img ⟨c15,r3⟩ ⟨c16,r3⟩ := by
    refine Quiet.step_of (by change (0x80004418#32).getLsbD 0=false;decide) de2147501080 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) r3 0 [] [] = ⟨.ok c16 r3 [],[]⟩
    have v13 : c15.get 13=(BitVec.ofNat 32 n) := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
    have v14 : c15.get 14=1000000#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
    rw [exec_branch,v13,v14,(by rw [HttpDecMath.branch_geu n 1000000 (by omega) (by omega)];exact decide_eq_false (by omega) : taken .geu ((BitVec.ofNat 32 n)) (1000000#32)=false)]
    simp only [Bool.false_eq_true,ite_false];first | rfl | (rw [hp];rfl)
  have t16 : Quiet.Step B img ⟨c16,r3⟩ ⟨c17,r3⟩ := by
    refine Quiet.step_of (by change (0x8000441c#32).getLsbD 0=false;decide) de2147501084 fun o => ?_
    change Observed.interp B img o (exec c16 _ _) r3 0 [] [] = ⟨.ok c17 r3 [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t17 : Quiet.Step B img ⟨c17,r3⟩ ⟨c18,r3⟩ := by
    refine Quiet.step_of (by change (0x80004420#32).getLsbD 0=false;decide) de2147501088 fun o => ?_
    change Observed.interp B img o (exec c17 _ _) r3 0 [] [] = ⟨.ok c18 r3 [],[]⟩
    have v13 : c17.get 13=(BitVec.ofNat 32 n) := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
    rw [exec_opimm,v13]
    change Observed.interp B img o (.done (c17.wr 15 (alu .srl ((BitVec.ofNat 32 n)) (5#32)) (c17.pc+4#32))) r3 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t18 : Quiet.Step B img ⟨c18,r3⟩ ⟨c19,r3⟩ := by
    refine Quiet.step_of (by change (0x80004424#32).getLsbD 0=false;decide) de2147501092 fun o => ?_
    change Observed.interp B img o (exec c18 _ _) r3 0 [] [] = ⟨.ok c19 r3 [],[]⟩
    have v14 : c18.get 14=175923200#32 := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
    rw [exec_opimm,v14]
    change Observed.interp B img o (.done (c18.wr 14 (alu .add (175923200#32) (4294965957#32)) (c18.pc+4#32))) r3 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t19 : Quiet.Step B img ⟨c19,r3⟩ ⟨c20,r3⟩ := by
    refine Quiet.step_of (by change (0x80004428#32).getLsbD 0=false;decide) de2147501096 fun o => ?_
    change Observed.interp B img o (exec c19 _ _) r3 0 [] [] = ⟨.ok c20 r3 [],[]⟩
    have v15 : c19.get 15=((BitVec.ofNat 32 n) >>> 5) := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
    have v14 : c19.get 14=175921861#32 := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
    rw [HttpDecMath.exec_muldiv,v15,v14]
    change Observed.interp B img o (.done (c19.wr 14 (muldiv .mulhu (((BitVec.ofNat 32 n) >>> 5)) (175921861#32)) (c19.pc+4#32))) r3 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t20 : Quiet.Step B img ⟨c20,r3⟩ ⟨c21,r3⟩ := by
    refine Quiet.step_of (by change (0x8000442c#32).getLsbD 0=false;decide) de2147501100 fun o => ?_
    change Observed.interp B img o (exec c20 _ _) r3 0 [] [] = ⟨.ok c21 r3 [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t21 : Quiet.Step B img ⟨c21,r3⟩ ⟨c22,r3⟩ := by
    refine Quiet.step_of (by change (0x80004430#32).getLsbD 0=false;decide) de2147501104 fun o => ?_
    change Observed.interp B img o (exec c21 _ _) r3 0 [] [] = ⟨.ok c22 r3 [],[]⟩
    have v14 : c21.get 14=(muldiv .mulhu (((BitVec.ofNat 32 n) >>> 5)) (175921861#32)) := by simp [c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
    rw [exec_opimm,v14]
    change Observed.interp B img o (.done (c21.wr 14 (alu .srl ((muldiv .mulhu (((BitVec.ofNat 32 n) >>> 5)) (175921861#32))) (7#32)) (c21.pc+2#32))) r3 0 [] [] = _
    rw [(show alu .srl ((muldiv .mulhu (((BitVec.ofNat 32 n) >>> 5)) (175921861#32))) (7#32)=0#32 from HttpDecMath.million_zero n hn)]
    first | rfl | (rw [hp]; rfl)
  have t22 : Quiet.Step B img ⟨c22,r3⟩ ⟨c23,r3⟩ := by
    refine Quiet.step_of (by change (0x80004432#32).getLsbD 0=false;decide) de2147501106 fun o => ?_
    change Observed.interp B img o (exec c22 _ _) r3 0 [] [] = ⟨.ok c23 r3 [],[]⟩
    have v15 : c22.get 15=429498368#32 := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
    rw [exec_opimm,v15]
    change Observed.interp B img o (.done (c22.wr 15 (alu .add (429498368#32) (4294965658#32)) (c22.pc+4#32))) r3 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t23 : Quiet.Step B img ⟨c23,r3⟩ ⟨c24,r3⟩ := by
    refine Quiet.step_of (by change (0x80004436#32).getLsbD 0=false;decide) de2147501110 fun o => ?_
    change Observed.interp B img o (exec c23 _ _) r3 0 [] [] = ⟨.ok c24 r3 [],[]⟩
    have v14 : c23.get 14=0#32 := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
    have v15 : c23.get 15=429496730#32 := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
    rw [HttpDecMath.exec_muldiv,v14,v15]
    change Observed.interp B img o (.done (c23.wr 16 (muldiv .mulhu (0#32) (429496730#32)) (c23.pc+4#32))) r3 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t24 : Quiet.Step B img ⟨c24,r3⟩ ⟨c25,r3⟩ := by
    refine Quiet.step_of (by change (0x8000443a#32).getLsbD 0=false;decide) de2147501114 fun o => ?_
    change Observed.interp B img o (exec c24 _ _) r3 0 [] [] = ⟨.ok c25 r3 [],[]⟩
    have v16 : c24.get 16=0#32 := by simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
    rw [exec_opimm,v16]
    change Observed.interp B img o (.done (c24.wr 17 (alu .sll (0#32) (1#32)) (c24.pc+4#32))) r3 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t25 : Quiet.Step B img ⟨c25,r3⟩ ⟨c26,r3⟩ := by
    refine Quiet.step_of (by change (0x8000443e#32).getLsbD 0=false;decide) de2147501118 fun o => ?_
    change Observed.interp B img o (exec c25 _ _) r3 0 [] [] = ⟨.ok c26 r3 [],[]⟩
    have v16 : c25.get 16=0#32 := by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
    rw [exec_opimm,v16]
    change Observed.interp B img o (.done (c25.wr 16 (alu .sll (0#32) (3#32)) (c25.pc+2#32))) r3 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t26 : Quiet.Step B img ⟨c26,r3⟩ ⟨c27,r3⟩ := by
    refine Quiet.step_of (by change (0x80004440#32).getLsbD 0=false;decide) de2147501120 fun o => ?_
    change Observed.interp B img o (exec c26 _ _) r3 0 [] [] = ⟨.ok c27 r3 [],[]⟩
    have v16 : c26.get 16=0#32 := by simp [c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
    have v17 : c26.get 17=0#32 := by simp [c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
    rw [exec_op,v16,v17]
    change Observed.interp B img o (.done (c26.wr 16 (alu .add (0#32) (0#32)) (c26.pc+2#32))) r3 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t27 : Quiet.Step B img ⟨c27,r3⟩ ⟨c28,r3⟩ := by
    refine Quiet.step_of (by change (0x80004442#32).getLsbD 0=false;decide) de2147501122 fun o => ?_
    change Observed.interp B img o (exec c27 _ _) r3 0 [] [] = ⟨.ok c28 r3 [],[]⟩
    have v14 : c27.get 14=0#32 := by simp [c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
    have v16 : c27.get 16=0#32 := by simp [c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
    rw [exec_op,v14,v16]
    change Observed.interp B img o (.done (c27.wr 14 (alu .sub (0#32) (0#32)) (c27.pc+4#32))) r3 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t28 : Quiet.Step B img ⟨c28,r3⟩ ⟨c29,r3⟩ := by
    refine Quiet.step_of (by change (0x80004446#32).getLsbD 0=false;decide) de2147501126 fun o => ?_
    change Observed.interp B img o (exec c28 _ _) r3 0 [] [] = ⟨.ok c29 r3 [],[]⟩
    have v14 : c28.get 14=0#32 := by simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
    rw [exec_branch,v14,Core.get_zero,(by decide +kernel : taken .eq (0#32) ((0 : Word))=true)]
    simp only [ite_true]
    rw [show c28.pc=2147501126#32 by rfl,show 2147501126#32+48#32=2147501174#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t29 : Quiet.Step B img ⟨c29,r3⟩ ⟨c30,r3⟩ := by
    refine Quiet.step_of (by change (0x80004476#32).getLsbD 0=false;decide) de2147501174 fun o => ?_
    change Observed.interp B img o (exec c29 _ _) r3 0 [] [] = ⟨.ok c30 r3 [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  refine ⟨c30,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.step t16 (.step t17 (.step t18 (.step t19 (.step t20 (.step t21 (.step t22 (.step t23 (.step t24 (.step t25 (.step t26 (.step t27 (.step t28 (.single t29))))))))))))))))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
  · simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
  · simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
  · simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
  · simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13]
  · intro reg h2 h14 h15 h16 h17;simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h2,h14,h15,h16,h17]
end E5R.Thermostat.HttpDecLeading0
