import Projects.thermostat.TrimMath
import Projects.thermostat.QuietRam
set_option autoImplicit false
namespace E5R.Thermostat.AsciiWhitespaceProgram
open E5R E5R.Thermostat

/-- A checked subtraction/range/bitmask whitespace classifier. Instruction
    lengths are explicit because the backwards scan uses compressed ADDI. -/
structure Certificate (img : List Segment) (pc len off1 off2 : Word) (src tmp rangeReg maskReg : Reg) : Prop where
  aligned0 : pc.getLsbD 0=false
  aligned1 : (pc+len).getLsbD 0=false
  aligned2 : (pc+len+4#32).getLsbD 0=false
  aligned3 : (pc+len+8#32).getLsbD 0=false
  aligned4 : (pc+len+12#32).getLsbD 0=false
  alignedTarget : (pc+len+off1).getLsbD 0=false
  sameTarget : pc+len+12#32+off2=pc+len+off1
  sub : fetchDecode img pc=some (.opimm .add tmp src 0xfffffff7#32,len)
  range : fetchDecode img (pc+len)=some (.branch .ltu rangeReg tmp off1,4#32)
  shift : fetchDecode img (pc+len+4#32)=some (.op .srl tmp maskReg tmp,4#32)
  mask : fetchDecode img (pc+len+8#32)=some (.opimm .and tmp tmp 1#32,4#32)
  zero : fetchDecode img (pc+len+12#32)=some (.branch .eq tmp 0 off2,4#32)

theorem contract (B : Board) (img : List Segment) (c : Core) (ram : Word → BitVec 8)
    (pc len off1 off2 : Word) (src tmp rangeReg maskReg : Reg) (byte : BitVec 8)
    (cert : Certificate img pc len off1 off2 src tmp rangeReg maskReg)
    (tmpZero : tmp.val≠0) (rangeApart : rangeReg≠tmp) (maskApart : maskReg≠tmp)
    (hp : c.pc=pc) (value : c.get src=BitVec.ofNat 32 byte.toNat)
    (rangeValue : c.get rangeReg=23#32) (maskValue : c.get maskReg=0x80001b#32) :
    ∃ n d, n≤5 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if TrimMath.white byte then pc+len+16#32 else pc+len+off1) ∧
      (∀ r : Reg, r≠tmp → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr tmp (BitVec.ofNat 32 byte.toNat+0xfffffff7#32) (pc+len)
  have sa : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];exact cert.aligned0) (by rw [hp];exact cert.sub) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok a ram [],[]⟩
    rw [exec_opimm,value,hp];rfl
  have av : a.get tmp=BitVec.ofNat 32 byte.toNat+0xfffffff7#32 := Core.wr_get_self _ _ _ _ tmpZero
  have ar : a.get rangeReg=23#32 := (Core.wr_get_ne _ _ _ _ _ rangeApart).trans rangeValue
  by_cases inside : 9≤byte.toNat ∧ byte.toNat≤32
  · let b := a.goto (pc+len+4#32)
    let e := b.wr tmp (TrimMath.shifted byte) (pc+len+8#32)
    let f := e.wr tmp (if TrimMath.white byte then 1#32 else 0#32) (pc+len+12#32)
    let d := f.goto (if TrimMath.white byte then pc+len+16#32 else pc+len+off1)
    have sb : Quiet.Step B img ⟨a,ram⟩ ⟨b,ram⟩ := by
      refine Quiet.step_of cert.aligned1 cert.range fun o => ?_
      rw [exec_branch,ar,av,TrimMath.range]
      have outside : ¬(byte.toNat<9 ∨ 32<byte.toNat) := by omega
      simp only [outside,decide_false,Bool.false_eq_true,ite_false]
      rfl
    have se : Quiet.Step B img ⟨b,ram⟩ ⟨e,ram⟩ := by
      refine Quiet.step_of cert.aligned2 cert.shift fun o => ?_
      change Observed.interp B img o (exec b _ _) ram 0 [] [] = ⟨.ok e ram [],[]⟩
      have bm : b.get maskReg=0x80001b#32 := (Core.wr_get_ne _ _ _ _ _ maskApart).trans maskValue
      have bv : b.get tmp=BitVec.ofNat 32 byte.toNat+0xfffffff7#32 := av
      rw [exec_op,bm,bv]
      have shiftedValue : alu .srl 0x80001b#32 (BitVec.ofNat 32 byte.toNat+0xfffffff7#32)=TrimMath.shifted byte := by
        unfold TrimMath.shifted
        rfl
      rw [shiftedValue]
      change Observed.interp B img o (Eff.done (b.wr tmp (TrimMath.shifted byte) ((pc+len+4#32)+4#32))) ram 0 [] [] = _
      rw [BitVec.add_assoc,show 4#32+4#32=8#32 by decide +kernel];rfl
    have sf : Quiet.Step B img ⟨e,ram⟩ ⟨f,ram⟩ := by
      refine Quiet.step_of cert.aligned3 cert.mask fun o => ?_
      change Observed.interp B img o (exec e _ _) ram 0 [] [] = ⟨.ok f ram [],[]⟩
      have ev : e.get tmp=TrimMath.shifted byte := Core.wr_get_self _ _ _ _ tmpZero
      rw [exec_opimm,ev]
      change Observed.interp B img o (Eff.done (e.wr tmp (TrimMath.shifted byte &&& 1#32) ((pc+len+8#32)+4#32))) ram 0 [] [] = _
      rw [TrimMath.mask byte inside,BitVec.add_assoc,show 8#32+4#32=12#32 by decide +kernel];rfl
    have sd : Quiet.Step B img ⟨f,ram⟩ ⟨d,ram⟩ := by
      refine Quiet.step_of cert.aligned4 cert.zero fun o => ?_
      have fv : f.get tmp=(if TrimMath.white byte then 1#32 else 0#32) := Core.wr_get_self _ _ _ _ tmpZero
      rw [exec_branch,fv,Core.get_zero]
      cases white : TrimMath.white byte with
      | false =>
        simp only [Bool.false_eq_true,ite_false]
        rw [show taken .eq 0#32 (0 : Word)=true by decide +kernel]
        simp only [ite_true]
        change Observed.interp B img o (jump f (pc+len+12#32+off2)) ram 0 [] [] = _
        rw [cert.sameTarget,jump_ok _ _ cert.alignedTarget]
        simp only [d,white,Bool.false_eq_true,ite_false]
        rfl
      | true =>
        simp only [ite_true]
        rw [show taken .eq 1#32 (0 : Word)=false by decide +kernel]
        simp only [Bool.false_eq_true,ite_false]
        change Observed.interp B img o (Eff.done (f.goto ((pc+len+12#32)+4#32))) ram 0 [] [] = _
        rw [BitVec.add_assoc,show 12#32+4#32=16#32 by decide +kernel]
        simp only [d,white,ite_true]
        rfl
    refine ⟨5,d,by omega,.step sa (.step sb (.step se (.step sf (.single sd)))),rfl,?_,?_⟩
    · intro r ne
      simp only [d,f,e,b,a,Core.goto_get,Core.wr_get_ne _ _ _ _ _ ne]
    · exact (Core.sameCsr_goto f _).trans ((Core.sameCsr_wr e _ _ _).trans ((Core.sameCsr_wr b _ _ _).trans ((Core.sameCsr_goto a _).trans (Core.sameCsr_wr c _ _ _))))
  · let d := a.goto (pc+len+off1)
    have sd : Quiet.Step B img ⟨a,ram⟩ ⟨d,ram⟩ := by
      refine Quiet.step_of cert.aligned1 cert.range fun o => ?_
      rw [exec_branch,ar,av,TrimMath.range]
      have outside : byte.toNat<9 ∨ 32<byte.toNat := by omega
      simp only [outside,decide_true,ite_true]
      change Observed.interp B img o (jump a (pc+len+off1)) ram 0 [] [] = _
      rw [jump_ok _ _ cert.alignedTarget];rfl
    have notWhite : TrimMath.white byte=false := by
      simp only [TrimMath.white,decide_eq_false_iff_not]
      omega
    refine ⟨2,d,by omega,.step sa (.single sd),?_,?_,(Core.sameCsr_goto a _).trans (Core.sameCsr_wr c _ _ _)⟩
    · simp only [d,Core.goto_pc,notWhite,Bool.false_eq_true,ite_false]
    · intro r ne
      exact Core.wr_get_ne _ _ _ _ _ ne
end E5R.Thermostat.AsciiWhitespaceProgram
