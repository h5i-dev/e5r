import Projects.thermostat.QuietRam
set_option autoImplicit false
namespace E5R.Thermostat.TrimAdvanceProgram
open E5R E5R.Thermostat

structure Certificate (img : List Segment) (pc step off : Word) (counter ptr : Reg) : Prop where
  aligned0 : pc.getLsbD 0=false
  aligned1 : (pc+2#32).getLsbD 0=false
  aligned2 : (pc+4#32).getLsbD 0=false
  alignedTarget : (pc+4#32+off).getLsbD 0=false
  decrement : fetchDecode img pc=some (.opimm .add counter counter 0xffffffff#32,2#32)
  advance : fetchDecode img (pc+2#32)=some (.opimm .add ptr ptr step,2#32)
  branch : fetchDecode img (pc+4#32)=some (.branch .ne counter 0 off,4#32)

theorem decrement (n : Nat) (positive : 0<n) : BitVec.ofNat 32 n+0xffffffff#32=BitVec.ofNat 32 (n-1) := by
  have he : n=(n-1)+1 := by omega
  calc
    BitVec.ofNat 32 n+0xffffffff#32=(BitVec.ofNat 32 (n-1)+1#32)+0xffffffff#32 := by
      exact congrArg (fun x : Word => x+0xffffffff#32) (by rw [←BitVec.ofNat_add];exact congrArg (BitVec.ofNat 32) he)
    _ = _ := by rw [BitVec.add_assoc,show 1#32+0xffffffff#32=0#32 by decide +kernel,BitVec.add_zero]

theorem tested (n : Nat) (positive : 0<n) (bound : n<2^32) :
    taken .ne (BitVec.ofNat 32 (n-1)) (0 : Word)=decide (n≠1) := by
  change decide (BitVec.ofNat 32 (n-1)≠(0 : Word))=_
  have he : BitVec.ofNat 32 (n-1)=(0 : Word) ↔ n=1 := by
    constructor
    · intro h
      have hh := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show n-1<2^32 by omega)] at hh
      change n-1=0 at hh
      omega
    · intro h
      subst n
      rfl
  simp only [ne_eq,he]

/-- Three real instructions; the pointer can advance in either direction. -/
theorem contract (B : Board) (img : List Segment) (c : Core) (ram : Word → BitVec 8)
    (pc step off p : Word) (counter ptr : Reg) (n : Nat)
    (cert : Certificate img pc step off counter ptr)
    (counterZero : counter.val≠0) (ptrZero : ptr.val≠0) (apart : counter≠ptr)
    (positive : 0<n) (bound : n<2^32) (hp : c.pc=pc)
    (count : c.get counter=BitVec.ofNat 32 n) (pointer : c.get ptr=p) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if n=1 then pc+8#32 else pc+4#32+off) ∧ d.get counter=BitVec.ofNat 32 (n-1) ∧ d.get ptr=p+step ∧
      (∀ r : Reg, r≠counter → r≠ptr → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr counter (BitVec.ofNat 32 (n-1)) (pc+2#32)
  let b := a.wr ptr (p+step) (pc+4#32)
  let d := b.goto (if n=1 then pc+8#32 else pc+4#32+off)
  have sa : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];exact cert.aligned0) (by rw [hp];exact cert.decrement) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] [] = ⟨.ok a ram [],[]⟩
    rw [exec_opimm,count]
    change Observed.interp B img o (Eff.done (c.wr counter (BitVec.ofNat 32 n+0xffffffff#32) (c.pc+2#32))) ram 0 [] [] = _
    rw [decrement n positive,hp];rfl
  have sb : Quiet.Step B img ⟨a,ram⟩ ⟨b,ram⟩ := by
    refine Quiet.step_of cert.aligned1 cert.advance fun o => ?_
    change Observed.interp B img o (exec a _ _) ram 0 [] [] = ⟨.ok b ram [],[]⟩
    have av : a.get ptr=p := (Core.wr_get_ne _ _ _ _ _ (Ne.symm apart)).trans pointer
    rw [exec_opimm,av]
    change Observed.interp B img o (Eff.done (a.wr ptr (p+step) (pc+2#32+2#32))) ram 0 [] [] = _
    rw [BitVec.add_assoc,show 2#32+2#32=4#32 by decide +kernel];rfl
  have sd : Quiet.Step B img ⟨b,ram⟩ ⟨d,ram⟩ := by
    refine Quiet.step_of cert.aligned2 cert.branch fun o => ?_
    have bv : b.get counter=BitVec.ofNat 32 (n-1) := (Core.wr_get_ne _ _ _ _ _ apart).trans (Core.wr_get_self _ _ _ _ counterZero)
    rw [exec_branch,bv,Core.get_zero,tested n positive bound]
    by_cases equal : n=1
    · simp only [equal,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,ite_false]
      change Observed.interp B img o (Eff.done (b.goto (pc+4#32+4#32))) ram 0 [] [] = _
      rw [BitVec.add_assoc,show 4#32+4#32=8#32 by decide +kernel]
      simp only [d,equal,ite_true]
      rfl
    · simp only [ne_eq,equal,not_false_eq_true,decide_true,ite_true]
      change Observed.interp B img o (jump b (pc+4#32+off)) ram 0 [] [] = _
      rw [jump_ok _ _ cert.alignedTarget]
      simp only [d,equal,ite_false]
      rfl
  refine ⟨d,.step sa (.step sb (.single sd)),rfl,?_,?_,?_,(Core.sameCsr_goto b _).trans ((Core.sameCsr_wr a _ _ _).trans (Core.sameCsr_wr c _ _ _))⟩
  · exact (Core.wr_get_ne _ _ _ _ _ apart).trans (Core.wr_get_self _ _ _ _ counterZero)
  · exact Core.wr_get_self _ _ _ _ ptrZero
  · intro r nc np
    simp only [d,b,a,Core.goto_get,Core.wr_get_ne _ _ _ _ _ np,Core.wr_get_ne _ _ _ _ _ nc]
end E5R.Thermostat.TrimAdvanceProgram
