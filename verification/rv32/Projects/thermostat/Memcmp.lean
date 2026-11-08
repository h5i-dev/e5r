import Projects.thermostat.MemcmpLoop
import Projects.thermostat.Interrupt
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.Memcmp
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p q : Word) (xs ys : List (BitVec 8))
    (hx : ReadBytes.Span B img ram p xs) (hy : ReadBytes.Span B img ram q ys) (hl : xs.length = ys.length)
    (hp : c.pc = 0x80005162#32) (h10 : c.get 10 = p) (h11 : c.get 11 = q)
    (h12 : c.get 12 = BitVec.ofNat 32 xs.length) :
    ∃ d n, n ≤ 7*xs.length+3 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = c.get 1 &&& ~~~1 ∧ d.get 10 = MemcmpSpec.value xs ys ∧ MemcmpLoop.Frame c d ∧ d.sameCsr c := by
  by_cases hz : xs = []
  · subst xs
    have hy0 : ys = [] := by apply List.eq_nil_of_length_eq_zero;simpa only [List.length_nil] using hl.symm
    subst ys
    let a := c.goto 0x80005178#32
    have s0 : DetStep B img ⟨c,ram⟩ ⟨a,ram⟩ := by
      refine detStep_of (by rw [hp];decide) (by rw [hp];exact mc2147504482) fun o => ?_
      rw [exec_branch,h12,Core.get_zero]
      change interp B img o (jump c (c.pc+22#32)) ram 0 [] = _
      rw [hp,show 0x80005162#32+22#32 = 0x80005178#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
    obtain ⟨d,td,dpc,d10,dframe,dcsr⟩ := MemcmpReturn.zero B a ram rfl
    refine ⟨d,3,by simp,(DetSteps.single s0).trans td,dpc,d10,?_,dcsr⟩
    intro r hr;exact dframe r (MemcmpLoop.outside r 10 hr (by decide))
  · let a := c.goto 0x80005164#32
    have hlen : BitVec.ofNat 32 xs.length ≠ (0 : Word) := by
      intro he
      have hh := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat] at hh
      change xs.length%4294967296 = 0 at hh
      have hi := hx.length
      have h0 : xs.length = 0 := by omega
      exact hz (List.eq_nil_of_length_eq_zero h0)
    have s0 : DetStep B img ⟨c,ram⟩ ⟨a,ram⟩ := by
      refine detStep_of (by rw [hp];decide) (by rw [hp];exact mc2147504482) fun o => ?_
      rw [exec_branch,h12,Core.get_zero]
      have ht : taken .eq (BitVec.ofNat 32 xs.length) (0 : Word) = false := by
        change decide (BitVec.ofNat 32 xs.length = (0 : Word)) = false
        exact decide_eq_false hlen
      rw [ht];change Result.ok (c.goto (c.pc+2#32)) ram [] = _;rw [hp];rfl
    obtain ⟨d,n,hn,td,dpc,d10,dframe,dcsr⟩ := MemcmpLoop.contract B ram xs ys hl hz p q hx hy a rfl h10 h11 h12
    exact ⟨d,1+n,by omega,(DetSteps.single s0).trans td,dpc,d10,dframe,dcsr⟩

theorem closed_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p q : Word) (xs ys : List (BitVec 8))
    (hx : ReadBytes.Span B img ram p xs) (hy : ReadBytes.Span B img ram q ys) (hl : xs.length = ys.length)
    (hp : c.pc = 0x80005162#32) (h10 : c.get 10 = p) (h11 : c.get 11 = q)
    (h12 : c.get 12 = BitVec.ofNat 32 xs.length) (hm : c.mie_ = false) :
    ∃ d n, n ≤ 7*xs.length+3 ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = c.get 1 &&& ~~~1 ∧ d.get 10 = MemcmpSpec.value xs ys ∧ MemcmpLoop.Frame c d ∧ d.sameCsr c := by
  obtain ⟨d,n,hn,ht,hpc,hval,hframe,hcsr⟩ := contract B c ram p q xs ys hx hy hl hp h10 h11 h12
  exact ⟨d,n,hn,Interrupt.close ht hm,hpc,hval,hframe,hcsr⟩
end E5R.Thermostat.Memcmp
