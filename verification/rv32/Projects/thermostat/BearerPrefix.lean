import Projects.thermostat.BearerCall
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.BearerPrefix
open E5R E5R.Thermostat

theorem decision (B : Board) (c : Core) (ram : Word → BitVec 8) (w : Word)
    (hp : c.pc = 0x80000566#32) (h10 : c.get 10 = w) :
    DetStep B img ⟨c,ram⟩ ⟨c.goto (if w = 0#32 then 0x80000568#32 else 0x800005a2#32),ram⟩ := by
  refine detStep_of (by rw [hp];decide) (by rw [hp];exact be2147485030) fun o => ?_
  rw [exec_branch,h10,Core.get_zero]
  by_cases he : w = 0#32
  · have ht : taken .ne w (0 : Word) = false := by rw [he];decide +kernel
    rw [ht];simp only [Bool.false_eq_true,ite_false,ite_eq_left he]
    change Result.ok (c.goto (c.pc+2#32)) ram [] = _;rw [hp];rfl
  · have ht : taken .ne w (0 : Word) = true := by
      change (!decide (w = 0#32)) = true
      simp only [decide_eq_false he,Bool.not_false]
    rw [ht];simp only [ite_true,ite_eq_right he]
    change interp B img o (jump c (c.pc+0x3c#32)) ram 0 [] = _
    rw [hp,show 0x80000566#32+0x3c#32 = 0x800005a2#32 by decide +kernel,jump_ok _ _ (by decide)];rfl

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p len : Word) (xs : List (BitVec 8))
    (hx : ReadBytes.Span B img ram p xs) (hl : xs.length = 7)
    (hy : ReadBytes.Span B img ram 0x80005b75#32 (WireSpec.ascii "Bearer "))
    (hp : c.pc = 0x80000550#32) (h10 : c.get 10 = p) (h11 : c.get 11 = len) :
    ∃ d n, n ≤ 60 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if xs = WireSpec.ascii "Bearer " then 0x80000568#32 else 0x800005a2#32) ∧
      d.get 24 = p ∧ d.get 25 = len ∧
      (∀ r : Reg, r ≠ 1 → r ≠ 24 → r ≠ 25 → r.val < 10 ∨ 14 < r.val → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,n,hn,ht,apc,a10,a24,a25,aframe,acsr⟩ := BearerCall.contract B c ram p len xs hx hl hy hp h10 h11
  let w := MemcmpSpec.value xs (WireSpec.ascii "Bearer ")
  let d := a.goto (if w = 0#32 then 0x80000568#32 else 0x800005a2#32)
  have td := decision B a ram w apc a10
  have he : w = 0#32 ↔ xs = WireSpec.ascii "Bearer " := MemcmpSpec.zero_iff xs _ hl
  refine ⟨d,n+1,by omega,ht.trans (.single td),?_,a24,a25,aframe,acsr⟩
  change (if w = 0#32 then _ else _) = _
  simp only [he]
end E5R.Thermostat.BearerPrefix
