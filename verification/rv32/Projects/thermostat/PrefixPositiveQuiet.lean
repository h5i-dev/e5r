-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.PrefixPositive
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.PrefixEmptyQuiet
import Projects.thermostat.PrefixExitQuiet
import Projects.thermostat.PrefixNoSignQuiet
import Projects.thermostat.PrefixSaveQuiet
import Projects.thermostat.PrefixSetupQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.PrefixPositive
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp writer : Word)
    (hp : c.pc = 0x80004e00#32) (hsp : c.get 2 = sp+32#32)
    (h10 : c.get 10 = writer) (h11 : c.get 11 = 0x80005c04#32)
    (h12 : c.get 12 = 0xffffffff#32) (h13 : c.get 13 = 0#32) (h14 : c.get 14 = 0#32)
    (hm : Memory.Block B sp 32) (ha : sp.toNat%4 = 0) :
    ∃ d, Quiet.Steps B img 24 ⟨c,ram⟩ ⟨d,PrefixSave.memory ram sp c⟩ ∧ CursorExit.Returned c d ∧
      d.get 20 = c.get 20 ∧ (∀ r : Reg, 21 ≤ r.val → d.get r = c.get r) ∧ d.get 10 = 0#32 := by
  let rr := PrefixSave.memory ram sp c
  obtain ⟨a,ta,apc,asp,ar,ac⟩ := E5R.Thermostat.PrefixSave.contract_quiet B c ram sp hp hsp hm ha
  obtain ⟨b,tb,bpc,b8,b9,b18,b19,b11,b20,br,bc⟩ := E5R.Thermostat.PrefixSetup.contract_quiet B a rr sp writer 0x80005c04#32 0#32 0#32
    asp ((ar 10 (by decide)).trans h10) ((ar 11 (by decide)).trans h11)
    ((ar 13 (by decide)).trans h13) ((ar 14 (by decide)).trans h14) apc
  have b12 : b.get 12 = 0xffffffff#32 := (br 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((ar 12 (by decide)).trans h12)
  have bsp : b.get 2 = sp := (br 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans asp
  obtain ⟨u,tu,upc,ur,uc⟩ := E5R.Thermostat.PrefixNoSign.contract_quiet B b rr b12 b11 bpc
  obtain ⟨v,tv,vpc,v10,vr,vc⟩ := E5R.Thermostat.PrefixEmpty.contract_quiet B u rr ((ur 18).trans b18) upc
  have vsp : v.get 2 = sp := (vr 2 (by decide)).trans ((ur 2).trans bsp)
  have vu : ∀ reg : Reg, 21 ≤ reg.val → v.get reg = c.get reg := by
    intro reg hr
    have hn (k : Reg) (hk : k.val < 21) : reg ≠ k := by intro he;have hv := congrArg Fin.val he;omega
    exact (vr reg (hn 10 (by decide))).trans ((ur reg).trans
      ((br reg (hn 8 (by decide)) (hn 9 (by decide)) (hn 18 (by decide)) (hn 19 (by decide))
        (hn 11 (by decide)) (hn 20 (by decide))).trans (ar reg (hn 2 (by decide)))))
  obtain ⟨d,td,hd,d20,du,d10⟩ := E5R.Thermostat.PrefixExit.contract_quiet B c v ram rr sp vpc vsp hsp hm ha
    (((vc.trans uc).trans bc).trans ac) (fun _ => rfl) vu
  exact ⟨d,(((ta.trans tb).trans tu).trans tv).trans td,hd,d20,du,d10.trans v10⟩

end E5R.Thermostat.PrefixPositive
