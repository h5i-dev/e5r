import Projects.thermostat.RouteLiteralCall
import Projects.thermostat.MemcmpQuiet
import Projects.thermostat.QuietBranch
set_option autoImplicit false
namespace E5R.Thermostat.RouteLiteralCompare
open E5R E5R.Thermostat

/-- The actual matcher calls the real ROM/RAM memcmp, then branches on its
    result. Equality is derived from the byte specification, not assumed. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (path start pattern : Word) (xs ys : List (BitVec 8))
    (hx : ReadBytes.Span B img ram pattern xs) (hy : ReadBytes.Span B img ram (path+start) ys)
    (equalLength : xs.length=ys.length) (hp : c.pc=0x80002902#32)
    (h20 : c.get 20=path) (h10 : c.get 10=start) (h13 : c.get 13=pattern)
    (h12 : c.get 12=BitVec.ofNat 32 xs.length) :
    ∃ n d, n≤7*xs.length+8 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if xs=ys then 0x80002912#32 else 0x8000292a#32) ∧
      d.get 10=MemcmpSpec.value xs ys ∧
      (∀ r : Reg, r≠1 → (r.val<10 ∨ 14<r.val) → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,ta,pa,a11,a10,a1,ar,ac⟩ := RouteLiteralCall.contract B c ram path start pattern h20 h10 h13 hp
  have a12 : a.get 12=BitVec.ofNat 32 xs.length := (ar 12 (by decide) (by decide) (by decide)).trans h12
  obtain ⟨b,n,bound,tb,pb,b10,br,bc⟩ := Memcmp.contract_quiet B a ram pattern (path+start) xs ys hx hy equalLength pa a10 a11 a12
  have pcB : b.pc=0x80002910#32 := by rw [pb,a1];decide
  have tested : taken .ne (b.get 10) (b.get 0)=decide (xs≠ys) := by
    rw [b10,Core.get_zero]
    change decide (MemcmpSpec.value xs ys≠0#32)=_
    simp only [ne_eq,MemcmpSpec.zero_iff xs ys equalLength]
  obtain ⟨d,td,pd,dr,dc⟩ := QuietBranch.contract B img b ram 0x80002910#32 2#32 26#32 .ne 10 0 (decide (xs≠ys))
    pcB (by decide) (by decide) rt2147494160 tested
  refine ⟨4+n+1,d,by omega,(ta.trans tb).trans td,?_,(dr 10).trans b10,?_,dc.trans (bc.trans ac)⟩
  · by_cases same : xs=ys <;> simpa [same] using pd
  · intro r nr keep
    exact (dr r).trans ((br r keep).trans (ar r (by intro e;subst r;omega) (by intro e;subst r;omega) nr))
end E5R.Thermostat.RouteLiteralCompare
