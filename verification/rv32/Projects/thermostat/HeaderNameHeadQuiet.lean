-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.HeaderNameHead
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.HeaderDecisionQuiet
import Projects.thermostat.HeaderFoldQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.HeaderNameHead
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p q : Word) (a b : BitVec 8)
    (hp : c.pc = 0x80002706#32) (h10 : c.get 10 = p) (h14 : c.get 14 = q)
    (ha : ReadBytes.Byte B img ram p a) (hb : ReadBytes.Byte B img ram q b) :
    ∃ d, Quiet.Steps B img 11 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc = (if HeaderSpec.lower a = HeaderSpec.lower b then 0x8000272e#32 else 0x800026e2#32) ∧
      (∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 28 → r ≠ 29 → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨u,tu,upc,u6,u7,uregs,ucsr⟩ := E5R.Thermostat.HeaderFold.contract_quiet B c ram p q a b hp h10 h14 ha hb
  let d := u.goto (if HeaderSpec.lower a = HeaderSpec.lower b then 0x8000272e#32 else 0x800026e2#32)
  have td := E5R.Thermostat.HeaderDecision.contract_quiet B u ram (HeaderSpec.lower a) (HeaderSpec.lower b) upc u6 u7
  exact ⟨d,tu.trans (.single td),rfl,uregs,ucsr⟩

end E5R.Thermostat.HeaderNameHead
