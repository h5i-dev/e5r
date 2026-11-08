import Projects.thermostat.HeaderMath
import Projects.thermostat.QuietRam
set_option autoImplicit false
namespace E5R.Thermostat.AsciiFoldProgram
open E5R E5R.Thermostat

/-- Four actual instructions computing ASCII case folding. The explicit image
    parameter prevents accidental generalization of an unbound image name. -/
structure Certificate (img : List Segment) (pc : Word) (src tmp dst : Reg) (swap : Bool) (length : Word) : Prop where
  aligned0 : pc.getLsbD 0=false
  aligned1 : (pc+4#32).getLsbD 0=false
  aligned2 : (pc+8#32).getLsbD 0=false
  aligned3 : (pc+10#32).getLsbD 0=false
  add : fetchDecode img pc=some (.opimm .add tmp src 0xffffffbf#32,4#32)
  flag : fetchDecode img (pc+4#32)=some (.opimm .sltu tmp tmp 26#32,4#32)
  shift : fetchDecode img (pc+8#32)=some (.opimm .sll tmp tmp 5#32,2#32)
  fold : fetchDecode img (pc+10#32)=some ((if swap then .op .or dst src tmp else .op .or dst tmp src),length)

theorem contract (B : Board) (img : List Segment) (c : Core) (ram : Word → BitVec 8)
    (pc : Word) (src tmp dst : Reg) (swap : Bool) (length : Word) (byte : BitVec 8)
    (cert : Certificate img pc src tmp dst swap length) (tmpZero : tmp.val≠0) (dstZero : dst.val≠0) (apart : src≠tmp)
    (hp : c.pc=pc) (value : c.get src=BitVec.ofNat 32 byte.toNat) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=pc+10#32+length ∧
      d.get dst=BitVec.ofNat 32 (HeaderSpec.lower byte).toNat ∧
      (∀ r : Reg, r≠tmp → r≠dst → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr tmp (BitVec.ofNat 32 byte.toNat+0xffffffbf#32) (pc+4#32)
  let b := a.wr tmp (HeaderMath.upperFlag byte) (pc+8#32)
  let e := b.wr tmp (HeaderMath.upperFlag byte <<< 5) (pc+10#32)
  let d := e.wr dst (BitVec.ofNat 32 (HeaderSpec.lower byte).toNat) (pc+10#32+length)
  have t0 : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];exact cert.aligned0) (by rw [hp];exact cert.add) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok a ram [],[]⟩
    rw [exec_opimm,value,hp];rfl
  have t1 : Quiet.Step B img ⟨a,ram⟩ ⟨b,ram⟩ := by
    refine Quiet.step_of cert.aligned1 cert.flag fun o => ?_
    change Observed.interp B img o (exec a _ _) ram 0 [] [] = ⟨.ok b ram [],[]⟩
    have av : a.get tmp=BitVec.ofNat 32 byte.toNat+0xffffffbf#32 := Core.wr_get_self _ _ _ _ tmpZero
    rw [exec_opimm,av]
    change Observed.interp B img o (Eff.done (a.wr tmp (HeaderMath.upperFlag byte) (pc+4#32+4#32))) ram 0 [] [] = _
    rw [BitVec.add_assoc,show 4#32+4#32=8#32 by decide +kernel];rfl
  have t2 : Quiet.Step B img ⟨b,ram⟩ ⟨e,ram⟩ := by
    refine Quiet.step_of cert.aligned2 cert.shift fun o => ?_
    change Observed.interp B img o (exec b _ _) ram 0 [] [] = ⟨.ok e ram [],[]⟩
    have bv : b.get tmp=HeaderMath.upperFlag byte := Core.wr_get_self _ _ _ _ tmpZero
    rw [exec_opimm,bv]
    change Observed.interp B img o (Eff.done (b.wr tmp (HeaderMath.upperFlag byte <<< 5) (pc+8#32+2#32))) ram 0 [] [] = _
    rw [BitVec.add_assoc,show 8#32+2#32=10#32 by decide +kernel];rfl
  have t3 : Quiet.Step B img ⟨e,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of cert.aligned3 cert.fold fun o => ?_
    change Observed.interp B img o (exec e _ _) ram 0 [] [] = ⟨.ok d ram [],[]⟩
    have ev : e.get tmp=HeaderMath.upperFlag byte <<< 5 := Core.wr_get_self _ _ _ _ tmpZero
    have es : e.get src=BitVec.ofNat 32 byte.toNat := by
      simp only [e,b,a,Core.wr_get_ne _ _ _ _ _ apart,value]
    cases swap with
    | false =>
      simp only [Bool.false_eq_true,ite_false]
      rw [exec_op,ev,es]
      change Observed.interp B img o (Eff.done (e.wr dst ((HeaderMath.upperFlag byte <<< 5) ||| BitVec.ofNat 32 byte.toNat) (pc+10#32+length))) ram 0 [] [] = _
      rw [HeaderMath.folded];rfl
    | true =>
      simp only [ite_true]
      rw [exec_op,es,ev]
      change Observed.interp B img o (Eff.done (e.wr dst (BitVec.ofNat 32 byte.toNat ||| (HeaderMath.upperFlag byte <<< 5)) (pc+10#32+length))) ram 0 [] [] = _
      rw [BitVec.or_comm,HeaderMath.folded];rfl
  refine ⟨d,.step t0 (.step t1 (.step t2 (.single t3))),rfl,Core.wr_get_self _ _ _ _ dstZero,?_,
    (Core.sameCsr_wr e dst _ _).trans ((Core.sameCsr_wr b tmp _ _).trans ((Core.sameCsr_wr a tmp _ _).trans (Core.sameCsr_wr c tmp _ _)))⟩
  intro r nt nd
  simp only [d,e,b,a,Core.wr_get_ne _ _ _ _ _ nd,Core.wr_get_ne _ _ _ _ _ nt]
end E5R.Thermostat.AsciiFoldProgram
