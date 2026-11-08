import Projects.thermostat.PathSites
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.PathLiterals
open E5R E5R.Thermostat

theorem state (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8))
    (hs : Bytes.Span B ram (p+0#32) xs) (hlen : xs.length = 6)
    (hp : c.pc = 0x80001fce#32) (h11 : c.get 11 = p) :
    ∃ d n, n ≤ 18 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if xs = WireSpec.ascii "/state" then 0x80002016#32 else 0x80002194#32) ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨d,n,hn,ht,hpc,hregs,hcsr⟩ := Literal.check PathSites.state5 PathSites.state_prefix rfl rfl rfl
    (by decide) (by decide) B ram p xs c hs hlen hp h11
  have he : WireSpec.ascii "/stat"++[101#8] = WireSpec.ascii "/state" := rfl
  refine ⟨d,n,hn,ht,?_,?_,hcsr⟩
  · simpa only [he,PathSites.state5] using hpc
  · intro r h1 h2 h3;exact hregs r h2 h3 h1 h2

theorem point (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8))
    (hs : Bytes.Span B ram (p+0#32) xs) (hlen : xs.length = 9)
    (hp : c.pc = 0x80002020#32) (h11 : c.get 11 = p) :
    ∃ d n, n ≤ 27 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if xs = WireSpec.ascii "/setpoint" then 0x8000208c#32 else 0x80002194#32) ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨d,n,hn,ht,hpc,hregs,hcsr⟩ := Literal.check PathSites.point8 PathSites.point_prefix rfl rfl rfl
    (by decide) (by decide) B ram p xs c hs hlen hp h11
  have he : WireSpec.ascii "/setpoin"++[116#8] = WireSpec.ascii "/setpoint" := rfl
  refine ⟨d,n,hn,ht,?_,?_,hcsr⟩
  · simpa only [he,PathSites.point8] using hpc
  · intro r h1 h2 h3;exact hregs r h2 h3 h1 h2

theorem temp (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8))
    (hs : Bytes.Span B ram (p+2#32) xs) (hlen : xs.length = 3)
    (hp : c.pc = 0x800020ce#32) (h11 : c.get 11 = p) :
    ∃ d n, n ≤ 9 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if xs = WireSpec.ascii "emp" then 0x800020f2#32 else 0x80002194#32) ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨d,n,hn,ht,hpc,hregs,hcsr⟩ := Literal.check PathSites.temp2 PathSites.temp_prefix rfl rfl rfl
    (by decide) (by decide) B ram p xs c hs hlen hp h11
  have he : WireSpec.ascii "em"++[112#8] = WireSpec.ascii "emp" := rfl
  refine ⟨d,n,hn,ht,?_,?_,hcsr⟩
  · simpa only [he,PathSites.temp2] using hpc
  · intro r h1 h2 h3;exact hregs r h2 h3 h1 h2

theorem mode (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8))
    (hs : Bytes.Span B ram (p+2#32) xs) (hlen : xs.length = 3)
    (hp : c.pc = 0x80002136#32) (h11 : c.get 11 = p) :
    ∃ d n, n ≤ 9 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if xs = WireSpec.ascii "ode" then 0x8000215a#32 else 0x80002194#32) ∧
      (∀ r : Reg, r ≠ 11 → r ≠ 12 → r ≠ 13 → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨d,n,hn,ht,hpc,hregs,hcsr⟩ := Literal.check PathSites.mode2 PathSites.mode_prefix rfl rfl rfl
    (by decide) (by decide) B ram p xs c hs hlen hp h11
  have he : WireSpec.ascii "od"++[101#8] = WireSpec.ascii "ode" := rfl
  refine ⟨d,n,hn,ht,?_,?_,hcsr⟩
  · simpa only [he,PathSites.mode2] using hpc
  · intro r h1 h2 h3;exact hregs r h2 h3 h1 h2
end E5R.Thermostat.PathLiterals
