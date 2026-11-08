import Projects.thermostat.DecodeCode
import Projects.thermostat.Usize
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.LenBranch
open E5R E5R.Thermostat

/-- Only decoder/ISA facts and PC arithmetic enter this two-instruction rule. -/
structure Site (k : Nat) where
  pc : Word
  target : Word
  fall : Word
  offset : Word
  equal : Bool
  aligned : pc.getLsbD 0 = false
  branch_aligned : (pc+2#32).getLsbD 0 = false
  target_aligned : target.getLsbD 0 = false
  constant : fetchDecode img pc = some (.opimm .add 12 0 (BitVec.ofNat 32 k),2#32)
  branch : fetchDecode img (pc+2#32) = some (.branch (if equal then .eq else .ne) 11 12 offset,4#32)
  to_target : (pc+2#32)+offset = target
  to_fall : (pc+2#32)+4#32 = fall

def yes {k} (s : Site k) : Word := if s.equal then s.target else s.fall
def no {k} (s : Site k) : Word := if s.equal then s.fall else s.target

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (n k : Nat)
    (hn : n < 2^32) (hk : k < 2^32) (site : Site k)
    (hp : c.pc = site.pc) (h11 : c.get 11 = BitVec.ofNat 32 n) :
    ∃ d, DetSteps B img 2 ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = (if n = k then yes site else no site) ∧
      (∀ r : Reg, r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  let c1 := c.wr 12 (BitVec.ofNat 32 k) (site.pc+2#32)
  let d := c1.goto (if n = k then yes site else no site)
  have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
    refine detStep_of (by rw [hp];exact site.aligned) (by rw [hp];exact site.constant) fun o => ?_
    rw [exec_opimm,Core.get_zero]
    simp only [alu]
    rw [show (0 : Word) = 0#32 from rfl,BitVec.zero_add,hp];rfl
  have s1 : DetStep B img ⟨c1,ram⟩ ⟨d,ram⟩ := by
    refine detStep_of site.branch_aligned site.branch fun o => ?_
    have hv11 : c1.get 11 = BitVec.ofNat 32 n := by simp [c1,Core.wr_get_ne,h11]
    have hv12 : c1.get 12 = BitVec.ofNat 32 k := by simp [c1,Core.wr_get]
    rw [exec_branch,hv11,hv12]
    cases heq : site.equal with
    | true =>
      simp only [heq,ite_true]
      rw [Usize.eq n k hn hk]
      by_cases he : n = k
      · simp only [d,yes,no,heq,ite_true,decide_eq_true he,ite_eq_left he]
        change interp B img o (jump c1 ((site.pc+2#32)+site.offset)) ram 0 [] = _
        rw [site.to_target,jump_ok _ _ site.target_aligned];rfl
      · simp only [d,yes,no,heq,ite_true,decide_eq_false he,Bool.false_eq_true,ite_false,ite_eq_right he]
        change interp B img o (.done (c1.goto ((site.pc+2#32)+4#32))) ram 0 [] = _
        rw [site.to_fall];rfl
    | false =>
      simp only [heq,Bool.false_eq_true,ite_false]
      rw [Usize.ne n k hn hk]
      by_cases he : n = k
      · simp only [d,yes,no,heq,Bool.false_eq_true,ite_false,ite_eq_left he,he,ne_eq,not_true_eq_false,decide_false]
        change interp B img o (.done (c1.goto ((site.pc+2#32)+4#32))) ram 0 [] = _
        rw [site.to_fall];rfl
      · simp only [d,yes,no,heq,Bool.false_eq_true,ite_false,ite_eq_right he,he,ne_eq,not_false_eq_true,decide_true,ite_true]
        change interp B img o (jump c1 ((site.pc+2#32)+site.offset)) ram 0 [] = _
        rw [site.to_target,jump_ok _ _ site.target_aligned];rfl
  refine ⟨d,.step s0 (.single s1),rfl,?_,by rfl⟩
  intro r hr;simp [d,c1,Core.wr_get_ne,hr]

def five : Site 5 where
  pc := 0x80001fb8#32
  target := 0x800020aa#32
  fall := 0x80001fbe#32
  offset := 0xf0#32
  equal := true
  aligned := by decide
  branch_aligned := by decide
  target_aligned := by decide
  constant := wd2147491768
  branch := wd2147491770
  to_target := by decide +kernel
  to_fall := by decide +kernel

def nine : Site 9 where
  pc := 0x80001fbe#32
  target := 0x8000201c#32
  fall := 0x80001fc4#32
  offset := 0x5c#32
  equal := true
  aligned := by decide
  branch_aligned := by decide
  target_aligned := by decide
  constant := wd2147491774
  branch := wd2147491776
  to_target := by decide +kernel
  to_fall := by decide +kernel

def six : Site 6 where
  pc := 0x80001fc4#32
  target := 0x80002194#32
  fall := 0x80001fca#32
  offset := 0x1ce#32
  equal := false
  aligned := by decide
  branch_aligned := by decide
  target_aligned := by decide
  constant := wd2147491780
  branch := wd2147491782
  to_target := by decide +kernel
  to_fall := by decide +kernel
end E5R.Thermostat.LenBranch
