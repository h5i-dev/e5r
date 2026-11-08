import Projects.thermostat.HttpDecCode
import Projects.thermostat.QuietRam
import Projects.thermostat.HttpDecMath
import Projects.thermostat.Memory
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.HttpDecLeading1
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (n : Nat) (hn : n≤832) (h2 : c.get 2=sp) (h13 : c.get 13=(BitVec.ofNat 32 n)) (h14 : c.get 14=3518435328#32) (h15 : c.get 15=429496730#32) (h16 : c.get 16=0#32) (h17 : c.get 17=0#32) (hm : Memory.Block B sp 16) (ha : sp.toNat%4=0)
    (hp : c.pc=0x8000447a#32) :
    ∃ d, Quiet.Steps B img 30 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800044e0#32 ∧
      d.get 14=(BitVec.ofNat 32 (n/100)) ∧ d.get 15=0#32 ∧ d.get 16=0#32 ∧ d.get 17=0#32 ∧ (∀ r : Reg, r≠14 → r≠15 → r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 14 (3518437209#32) 0x8000447e#32
  let c2 := c1.wr 14 ((muldiv .mulhu ((BitVec.ofNat 32 n)) (3518437209#32))) 0x80004482#32
  let c3 := c2.wr 14 (0#32) 0x80004484#32
  let c4 := c3.wr 15 (0#32) 0x80004488#32
  let c5 := c4.wr 16 (0#32) 0x8000448c#32
  let c6 := c5.wr 15 (0#32) 0x8000448e#32
  let c7 := c6.wr 15 (0#32) 0x80004490#32
  let c8 := c7.wr 14 (0#32) 0x80004492#32
  let c9 := c8.goto 0x80004498#32
  let c10 := c9.wr 14 (274878464#32) 0x8000449c#32
  let c11 := c10.wr 14 (274877907#32) 0x800044a0#32
  let c12 := c11.wr 14 ((muldiv .mulhu ((BitVec.ofNat 32 n)) (274877907#32))) 0x800044a4#32
  let c13 := c12.wr 15 (429498368#32) 0x800044a8#32
  let c14 := c13.wr 14 (0#32) 0x800044aa#32
  let c15 := c14.wr 15 (429496730#32) 0x800044ae#32
  let c16 := c15.wr 16 (0#32) 0x800044b2#32
  let c17 := c16.wr 17 (0#32) 0x800044b6#32
  let c18 := c17.wr 16 (0#32) 0x800044b8#32
  let c19 := c18.wr 16 (0#32) 0x800044ba#32
  let c20 := c19.wr 14 (0#32) 0x800044be#32
  let c21 := c20.goto 0x800044c4#32
  let c22 := c21.wr 14 (1374388224#32) 0x800044c8#32
  let c23 := c22.wr 14 (1374389535#32) 0x800044cc#32
  let c24 := c23.wr 14 ((muldiv .mulhu ((BitVec.ofNat 32 n)) (1374389535#32))) 0x800044d0#32
  let c25 := c24.wr 14 ((BitVec.ofNat 32 (n/100))) 0x800044d2#32
  let c26 := c25.wr 15 (0#32) 0x800044d6#32
  let c27 := c26.wr 16 (0#32) 0x800044da#32
  let c28 := c27.wr 15 (0#32) 0x800044dc#32
  let c29 := c28.wr 15 (0#32) 0x800044de#32
  let c30 := c29.wr 14 ((BitVec.ofNat 32 (n/100))) 0x800044e0#32
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact de2147501178) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok c1 ram [],[]⟩
    have v14 : c.get 14=3518435328#32 := by simp [Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    rw [exec_opimm,v14]
    change Observed.interp B img o (.done (c.wr 14 (alu .add (3518435328#32) (1881#32)) (c.pc+4#32))) ram 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t1 : Quiet.Step B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
    refine Quiet.step_of (by change (0x8000447e#32).getLsbD 0=false;decide) de2147501182 fun o => ?_
    change Observed.interp B img o (exec c1 _ _) ram 0 [] [] = ⟨.ok c2 ram [],[]⟩
    have v13 : c1.get 13=(BitVec.ofNat 32 n) := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    have v14 : c1.get 14=3518437209#32 := by simp [c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    rw [HttpDecMath.exec_muldiv,v13,v14]
    change Observed.interp B img o (.done (c1.wr 14 (muldiv .mulhu ((BitVec.ofNat 32 n)) (3518437209#32)) (c1.pc+4#32))) ram 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t2 : Quiet.Step B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
    refine Quiet.step_of (by change (0x80004482#32).getLsbD 0=false;decide) de2147501186 fun o => ?_
    change Observed.interp B img o (exec c2 _ _) ram 0 [] [] = ⟨.ok c3 ram [],[]⟩
    have v14 : c2.get 14=(muldiv .mulhu ((BitVec.ofNat 32 n)) (3518437209#32)) := by simp [c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    rw [exec_opimm,v14]
    change Observed.interp B img o (.done (c2.wr 14 (alu .srl ((muldiv .mulhu ((BitVec.ofNat 32 n)) (3518437209#32))) (13#32)) (c2.pc+2#32))) ram 0 [] [] = _
    rw [(show alu .srl ((muldiv .mulhu ((BitVec.ofNat 32 n)) (3518437209#32))) (13#32)=0#32 from HttpDecMath.ten_thousand_zero n hn)]
    first | rfl | (rw [hp]; rfl)
  have t3 : Quiet.Step B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
    refine Quiet.step_of (by change (0x80004484#32).getLsbD 0=false;decide) de2147501188 fun o => ?_
    change Observed.interp B img o (exec c3 _ _) ram 0 [] [] = ⟨.ok c4 ram [],[]⟩
    have v14 : c3.get 14=0#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    have v15 : c3.get 15=429496730#32 := by simp [c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    rw [HttpDecMath.exec_muldiv,v14,v15]
    change Observed.interp B img o (.done (c3.wr 15 (muldiv .mulhu (0#32) (429496730#32)) (c3.pc+4#32))) ram 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t4 : Quiet.Step B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
    refine Quiet.step_of (by change (0x80004488#32).getLsbD 0=false;decide) de2147501192 fun o => ?_
    change Observed.interp B img o (exec c4 _ _) ram 0 [] [] = ⟨.ok c5 ram [],[]⟩
    have v15 : c4.get 15=0#32 := by simp [c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    rw [exec_opimm,v15]
    change Observed.interp B img o (.done (c4.wr 16 (alu .sll (0#32) (1#32)) (c4.pc+4#32))) ram 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t5 : Quiet.Step B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
    refine Quiet.step_of (by change (0x8000448c#32).getLsbD 0=false;decide) de2147501196 fun o => ?_
    change Observed.interp B img o (exec c5 _ _) ram 0 [] [] = ⟨.ok c6 ram [],[]⟩
    have v15 : c5.get 15=0#32 := by simp [c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    rw [exec_opimm,v15]
    change Observed.interp B img o (.done (c5.wr 15 (alu .sll (0#32) (3#32)) (c5.pc+2#32))) ram 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t6 : Quiet.Step B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
    refine Quiet.step_of (by change (0x8000448e#32).getLsbD 0=false;decide) de2147501198 fun o => ?_
    change Observed.interp B img o (exec c6 _ _) ram 0 [] [] = ⟨.ok c7 ram [],[]⟩
    have v15 : c6.get 15=0#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    have v16 : c6.get 16=0#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    rw [exec_op,v15,v16]
    change Observed.interp B img o (.done (c6.wr 15 (alu .add (0#32) (0#32)) (c6.pc+2#32))) ram 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t7 : Quiet.Step B img ⟨c7,ram⟩ ⟨c8,ram⟩ := by
    refine Quiet.step_of (by change (0x80004490#32).getLsbD 0=false;decide) de2147501200 fun o => ?_
    change Observed.interp B img o (exec c7 _ _) ram 0 [] [] = ⟨.ok c8 ram [],[]⟩
    have v14 : c7.get 14=0#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    have v15 : c7.get 15=0#32 := by simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    rw [exec_op,v14,v15]
    change Observed.interp B img o (.done (c7.wr 14 (alu .sub (0#32) (0#32)) (c7.pc+2#32))) ram 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t8 : Quiet.Step B img ⟨c8,ram⟩ ⟨c9,ram⟩ := by
    refine Quiet.step_of (by change (0x80004492#32).getLsbD 0=false;decide) de2147501202 fun o => ?_
    change Observed.interp B img o (exec c8 _ _) ram 0 [] [] = ⟨.ok c9 ram [],[]⟩
    have v14 : c8.get 14=0#32 := by simp [c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    rw [exec_branch,v14,Core.get_zero,(by decide +kernel : taken .eq (0#32) ((0 : Word))=true)]
    simp only [ite_true]
    rw [show c8.pc=2147501202#32 by rfl,show 2147501202#32+6#32=2147501208#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t9 : Quiet.Step B img ⟨c9,ram⟩ ⟨c10,ram⟩ := by
    refine Quiet.step_of (by change (0x80004498#32).getLsbD 0=false;decide) de2147501208 fun o => ?_
    change Observed.interp B img o (exec c9 _ _) ram 0 [] [] = ⟨.ok c10 ram [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t10 : Quiet.Step B img ⟨c10,ram⟩ ⟨c11,ram⟩ := by
    refine Quiet.step_of (by change (0x8000449c#32).getLsbD 0=false;decide) de2147501212 fun o => ?_
    change Observed.interp B img o (exec c10 _ _) ram 0 [] [] = ⟨.ok c11 ram [],[]⟩
    have v14 : c10.get 14=274878464#32 := by simp [c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    rw [exec_opimm,v14]
    change Observed.interp B img o (.done (c10.wr 14 (alu .add (274878464#32) (4294966739#32)) (c10.pc+4#32))) ram 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t11 : Quiet.Step B img ⟨c11,ram⟩ ⟨c12,ram⟩ := by
    refine Quiet.step_of (by change (0x800044a0#32).getLsbD 0=false;decide) de2147501216 fun o => ?_
    change Observed.interp B img o (exec c11 _ _) ram 0 [] [] = ⟨.ok c12 ram [],[]⟩
    have v13 : c11.get 13=(BitVec.ofNat 32 n) := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    have v14 : c11.get 14=274877907#32 := by simp [c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    rw [HttpDecMath.exec_muldiv,v13,v14]
    change Observed.interp B img o (.done (c11.wr 14 (muldiv .mulhu ((BitVec.ofNat 32 n)) (274877907#32)) (c11.pc+4#32))) ram 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t12 : Quiet.Step B img ⟨c12,ram⟩ ⟨c13,ram⟩ := by
    refine Quiet.step_of (by change (0x800044a4#32).getLsbD 0=false;decide) de2147501220 fun o => ?_
    change Observed.interp B img o (exec c12 _ _) ram 0 [] [] = ⟨.ok c13 ram [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t13 : Quiet.Step B img ⟨c13,ram⟩ ⟨c14,ram⟩ := by
    refine Quiet.step_of (by change (0x800044a8#32).getLsbD 0=false;decide) de2147501224 fun o => ?_
    change Observed.interp B img o (exec c13 _ _) ram 0 [] [] = ⟨.ok c14 ram [],[]⟩
    have v14 : c13.get 14=(muldiv .mulhu ((BitVec.ofNat 32 n)) (274877907#32)) := by simp [c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    rw [exec_opimm,v14]
    change Observed.interp B img o (.done (c13.wr 14 (alu .srl ((muldiv .mulhu ((BitVec.ofNat 32 n)) (274877907#32))) (6#32)) (c13.pc+2#32))) ram 0 [] [] = _
    rw [(show alu .srl ((muldiv .mulhu ((BitVec.ofNat 32 n)) (274877907#32))) (6#32)=0#32 from HttpDecMath.thousand_zero n hn)]
    first | rfl | (rw [hp]; rfl)
  have t14 : Quiet.Step B img ⟨c14,ram⟩ ⟨c15,ram⟩ := by
    refine Quiet.step_of (by change (0x800044aa#32).getLsbD 0=false;decide) de2147501226 fun o => ?_
    change Observed.interp B img o (exec c14 _ _) ram 0 [] [] = ⟨.ok c15 ram [],[]⟩
    have v15 : c14.get 15=429498368#32 := by simp [c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    rw [exec_opimm,v15]
    change Observed.interp B img o (.done (c14.wr 15 (alu .add (429498368#32) (4294965658#32)) (c14.pc+4#32))) ram 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t15 : Quiet.Step B img ⟨c15,ram⟩ ⟨c16,ram⟩ := by
    refine Quiet.step_of (by change (0x800044ae#32).getLsbD 0=false;decide) de2147501230 fun o => ?_
    change Observed.interp B img o (exec c15 _ _) ram 0 [] [] = ⟨.ok c16 ram [],[]⟩
    have v14 : c15.get 14=0#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    have v15 : c15.get 15=429496730#32 := by simp [c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    rw [HttpDecMath.exec_muldiv,v14,v15]
    change Observed.interp B img o (.done (c15.wr 16 (muldiv .mulhu (0#32) (429496730#32)) (c15.pc+4#32))) ram 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t16 : Quiet.Step B img ⟨c16,ram⟩ ⟨c17,ram⟩ := by
    refine Quiet.step_of (by change (0x800044b2#32).getLsbD 0=false;decide) de2147501234 fun o => ?_
    change Observed.interp B img o (exec c16 _ _) ram 0 [] [] = ⟨.ok c17 ram [],[]⟩
    have v16 : c16.get 16=0#32 := by simp [c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    rw [exec_opimm,v16]
    change Observed.interp B img o (.done (c16.wr 17 (alu .sll (0#32) (1#32)) (c16.pc+4#32))) ram 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t17 : Quiet.Step B img ⟨c17,ram⟩ ⟨c18,ram⟩ := by
    refine Quiet.step_of (by change (0x800044b6#32).getLsbD 0=false;decide) de2147501238 fun o => ?_
    change Observed.interp B img o (exec c17 _ _) ram 0 [] [] = ⟨.ok c18 ram [],[]⟩
    have v16 : c17.get 16=0#32 := by simp [c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    rw [exec_opimm,v16]
    change Observed.interp B img o (.done (c17.wr 16 (alu .sll (0#32) (3#32)) (c17.pc+2#32))) ram 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t18 : Quiet.Step B img ⟨c18,ram⟩ ⟨c19,ram⟩ := by
    refine Quiet.step_of (by change (0x800044b8#32).getLsbD 0=false;decide) de2147501240 fun o => ?_
    change Observed.interp B img o (exec c18 _ _) ram 0 [] [] = ⟨.ok c19 ram [],[]⟩
    have v16 : c18.get 16=0#32 := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    have v17 : c18.get 17=0#32 := by simp [c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    rw [exec_op,v16,v17]
    change Observed.interp B img o (.done (c18.wr 16 (alu .add (0#32) (0#32)) (c18.pc+2#32))) ram 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t19 : Quiet.Step B img ⟨c19,ram⟩ ⟨c20,ram⟩ := by
    refine Quiet.step_of (by change (0x800044ba#32).getLsbD 0=false;decide) de2147501242 fun o => ?_
    change Observed.interp B img o (exec c19 _ _) ram 0 [] [] = ⟨.ok c20 ram [],[]⟩
    have v14 : c19.get 14=0#32 := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    have v16 : c19.get 16=0#32 := by simp [c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    rw [exec_op,v14,v16]
    change Observed.interp B img o (.done (c19.wr 14 (alu .sub (0#32) (0#32)) (c19.pc+4#32))) ram 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t20 : Quiet.Step B img ⟨c20,ram⟩ ⟨c21,ram⟩ := by
    refine Quiet.step_of (by change (0x800044be#32).getLsbD 0=false;decide) de2147501246 fun o => ?_
    change Observed.interp B img o (exec c20 _ _) ram 0 [] [] = ⟨.ok c21 ram [],[]⟩
    have v14 : c20.get 14=0#32 := by simp [c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    rw [exec_branch,v14,Core.get_zero,(by decide +kernel : taken .eq (0#32) ((0 : Word))=true)]
    simp only [ite_true]
    rw [show c20.pc=2147501246#32 by rfl,show 2147501246#32+6#32=2147501252#32 by decide +kernel,jump_ok _ _ (by decide)];first | rfl | (rw [hp];rfl)
  have t21 : Quiet.Step B img ⟨c21,ram⟩ ⟨c22,ram⟩ := by
    refine Quiet.step_of (by change (0x800044c4#32).getLsbD 0=false;decide) de2147501252 fun o => ?_
    change Observed.interp B img o (exec c21 _ _) ram 0 [] [] = ⟨.ok c22 ram [],[]⟩
    rw [exec_lui];first | rfl | (rw [hp];rfl)
  have t22 : Quiet.Step B img ⟨c22,ram⟩ ⟨c23,ram⟩ := by
    refine Quiet.step_of (by change (0x800044c8#32).getLsbD 0=false;decide) de2147501256 fun o => ?_
    change Observed.interp B img o (exec c22 _ _) ram 0 [] [] = ⟨.ok c23 ram [],[]⟩
    have v14 : c22.get 14=1374388224#32 := by simp [c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    rw [exec_opimm,v14]
    change Observed.interp B img o (.done (c22.wr 14 (alu .add (1374388224#32) (1311#32)) (c22.pc+4#32))) ram 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t23 : Quiet.Step B img ⟨c23,ram⟩ ⟨c24,ram⟩ := by
    refine Quiet.step_of (by change (0x800044cc#32).getLsbD 0=false;decide) de2147501260 fun o => ?_
    change Observed.interp B img o (exec c23 _ _) ram 0 [] [] = ⟨.ok c24 ram [],[]⟩
    have v13 : c23.get 13=(BitVec.ofNat 32 n) := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    have v14 : c23.get 14=1374389535#32 := by simp [c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    rw [HttpDecMath.exec_muldiv,v13,v14]
    change Observed.interp B img o (.done (c23.wr 14 (muldiv .mulhu ((BitVec.ofNat 32 n)) (1374389535#32)) (c23.pc+4#32))) ram 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t24 : Quiet.Step B img ⟨c24,ram⟩ ⟨c25,ram⟩ := by
    refine Quiet.step_of (by change (0x800044d0#32).getLsbD 0=false;decide) de2147501264 fun o => ?_
    change Observed.interp B img o (exec c24 _ _) ram 0 [] [] = ⟨.ok c25 ram [],[]⟩
    have v14 : c24.get 14=(muldiv .mulhu ((BitVec.ofNat 32 n)) (1374389535#32)) := by simp [c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    rw [exec_opimm,v14]
    change Observed.interp B img o (.done (c24.wr 14 (alu .srl ((muldiv .mulhu ((BitVec.ofNat 32 n)) (1374389535#32))) (5#32)) (c24.pc+2#32))) ram 0 [] [] = _
    rw [(show alu .srl ((muldiv .mulhu ((BitVec.ofNat 32 n)) (1374389535#32))) (5#32)=(BitVec.ofNat 32 (n/100)) from HttpDecMath.quotient100 n hn)]
    first | rfl | (rw [hp]; rfl)
  have t25 : Quiet.Step B img ⟨c25,ram⟩ ⟨c26,ram⟩ := by
    refine Quiet.step_of (by change (0x800044d2#32).getLsbD 0=false;decide) de2147501266 fun o => ?_
    change Observed.interp B img o (exec c25 _ _) ram 0 [] [] = ⟨.ok c26 ram [],[]⟩
    have v14 : c25.get 14=(BitVec.ofNat 32 (n/100)) := by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    have v15 : c25.get 15=429496730#32 := by simp [c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    rw [HttpDecMath.exec_muldiv,v14,v15]
    change Observed.interp B img o (.done (c25.wr 15 (muldiv .mulhu ((BitVec.ofNat 32 (n/100))) (429496730#32)) (c25.pc+4#32))) ram 0 [] [] = _
    rw [(show muldiv .mulhu ((BitVec.ofNat 32 (n/100))) (429496730#32)=0#32 from HttpDecMath.low_tens n hn)]
    first | rfl | (rw [hp]; rfl)
  have t26 : Quiet.Step B img ⟨c26,ram⟩ ⟨c27,ram⟩ := by
    refine Quiet.step_of (by change (0x800044d6#32).getLsbD 0=false;decide) de2147501270 fun o => ?_
    change Observed.interp B img o (exec c26 _ _) ram 0 [] [] = ⟨.ok c27 ram [],[]⟩
    have v15 : c26.get 15=0#32 := by simp [c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    rw [exec_opimm,v15]
    change Observed.interp B img o (.done (c26.wr 16 (alu .sll (0#32) (1#32)) (c26.pc+4#32))) ram 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t27 : Quiet.Step B img ⟨c27,ram⟩ ⟨c28,ram⟩ := by
    refine Quiet.step_of (by change (0x800044da#32).getLsbD 0=false;decide) de2147501274 fun o => ?_
    change Observed.interp B img o (exec c27 _ _) ram 0 [] [] = ⟨.ok c28 ram [],[]⟩
    have v15 : c27.get 15=0#32 := by simp [c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    rw [exec_opimm,v15]
    change Observed.interp B img o (.done (c27.wr 15 (alu .sll (0#32) (3#32)) (c27.pc+2#32))) ram 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t28 : Quiet.Step B img ⟨c28,ram⟩ ⟨c29,ram⟩ := by
    refine Quiet.step_of (by change (0x800044dc#32).getLsbD 0=false;decide) de2147501276 fun o => ?_
    change Observed.interp B img o (exec c28 _ _) ram 0 [] [] = ⟨.ok c29 ram [],[]⟩
    have v15 : c28.get 15=0#32 := by simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    have v16 : c28.get 16=0#32 := by simp [c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    rw [exec_op,v15,v16]
    change Observed.interp B img o (.done (c28.wr 15 (alu .add (0#32) (0#32)) (c28.pc+2#32))) ram 0 [] [] = _
    first | rfl | (rw [hp]; rfl)
  have t29 : Quiet.Step B img ⟨c29,ram⟩ ⟨c30,ram⟩ := by
    refine Quiet.step_of (by change (0x800044de#32).getLsbD 0=false;decide) de2147501278 fun o => ?_
    change Observed.interp B img o (exec c29 _ _) ram 0 [] [] = ⟨.ok c30 ram [],[]⟩
    have v14 : c29.get 14=(BitVec.ofNat 32 (n/100)) := by simp [c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    have v15 : c29.get 15=0#32 := by simp [c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
    rw [exec_op,v14,v15]
    change Observed.interp B img o (.done (c29.wr 14 (alu .sub ((BitVec.ofNat 32 (n/100))) (0#32)) (c29.pc+2#32))) ram 0 [] [] = _
    rw [(by exact BitVec.sub_zero _ : alu .sub ((BitVec.ofNat 32 (n/100))) (0#32)=(BitVec.ofNat 32 (n/100)))]
    first | rfl | (rw [hp]; rfl)
  refine ⟨c30,.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t11 (.step t12 (.step t13 (.step t14 (.step t15 (.step t16 (.step t17 (.step t18 (.step t19 (.step t20 (.step t21 (.step t22 (.step t23 (.step t24 (.step t25 (.step t26 (.step t27 (.step t28 (.single t29))))))))))))))))))))))))))))),rfl,?_ ,?_ ,?_ ,?_ ,?_ ,by rfl⟩
  · simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
  · simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
  · simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
  · simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17]
  · intro reg h14 h15 h16 h17;simp [c30,c29,c28,c27,c26,c25,c24,c23,c22,c21,c20,c19,c18,c17,c16,c15,c14,c13,c12,c11,c10,c9,c8,c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,Core.wr_get,h2,h13,h14,h15,h16,h17,h14,h15,h16,h17]
end E5R.Thermostat.HttpDecLeading1
