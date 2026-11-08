-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.BodySuffix
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.LiteralCheckQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.BodySuffix
theorem heat_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8))
    (hs : Bytes.Span B ram (p+1#32) xs) (hlen : xs.length = 3)
    (hp : c.pc = 0x80002230#32) (h8 : c.get 8 = p) :
    ∃ d n, n ≤ 9 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if xs = WireSpec.ascii "eat" then 0x80002254#32 else 0x8000220a#32) ∧
      (∀ r : Reg, r ≠ 12 → r ≠ 13 → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨d,n,hn,ht,hpc,hregs,hcsr⟩ := E5R.Thermostat.Literal.check_quiet BodySites.heat2 BodySites.heat_prefix rfl rfl rfl
    (by decide) (by decide) B ram p xs c hs hlen hp h8
  have he : WireSpec.ascii "ea"++[116#8] = WireSpec.ascii "eat" := rfl
  refine ⟨d,n,hn,ht,?_,?_,hcsr⟩
  · simpa only [he,BodySites.heat2] using hpc
  · intro r h1 h2;exact hregs r h1 h2 h1 h2

end E5R.Thermostat.BodySuffix
namespace E5R.Thermostat.BodySuffix
theorem auto_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8))
    (hs : Bytes.Span B ram (p+1#32) xs) (hlen : xs.length = 3)
    (hp : c.pc = 0x8000225c#32) (h8 : c.get 8 = p) :
    ∃ d n, n ≤ 9 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if xs = WireSpec.ascii "uto" then 0x80002280#32 else 0x8000220a#32) ∧
      (∀ r : Reg, r ≠ 12 → r ≠ 13 → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨d,n,hn,ht,hpc,hregs,hcsr⟩ := E5R.Thermostat.Literal.check_quiet BodySites.auto2 BodySites.auto_prefix rfl rfl rfl
    (by decide) (by decide) B ram p xs c hs hlen hp h8
  have he : WireSpec.ascii "ut"++[111#8] = WireSpec.ascii "uto" := rfl
  refine ⟨d,n,hn,ht,?_,?_,hcsr⟩
  · simpa only [he,BodySites.auto2] using hpc
  · intro r h1 h2;exact hregs r h1 h2 h1 h2

end E5R.Thermostat.BodySuffix
