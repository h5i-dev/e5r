import Theories.Logic
set_option autoImplicit false
namespace E5R.Thermostat.EffectCoreProperty
open E5R
/-- A property of every successful effect continuation. Used to close the
    actual nonreturning panic regions without assuming RAM-store success. -/
def Holds (P : Core → Prop) : Eff → Prop
  | .done c => P c
  | .trap _ | .unsupported _ => True
  | .load _ _ _ k | .pick k => ∀ v, Holds P (k v)
  | .store _ _ _ _ k => Holds P k
  | .choose k => ∀ b, Holds P (k b)

theorem interp_holds {P : Core → Prop} {B img e} (h : Holds P e) :
    ∀ o ram i evs c r out, interp B img o e ram i evs = .ok c r out → P c := by
  induction e with
  | done c => intro o ram i evs c' r out he; cases he; exact h
  | trap | unsupported => intros; contradiction
  | choose k ih => intro o ram i evs c r out he; exact ih _ (h _) o ram (i+1) evs c r out he
  | pick k ih => intro o ram i evs c r out he; exact ih _ (h _) o ram (i+1) evs c r out he
  | load w a atomic k ih =>
    intro o ram i evs c r out he
    simp only [interp] at he
    split at he
    · contradiction
    · split at he
      · exact ih _ (h _) o ram i evs c r out he
      · split at he
        · contradiction
        · split at he
          · exact ih _ (h _) o ram i evs c r out he
          · split at he
            · split at he
              · exact ih _ (h _) o ram (i+1) evs c r out he
              · contradiction
            · contradiction
  | store w a v atomic k ih =>
    intro o ram i evs c r out he
    simp only [interp] at he
    split at he
    · contradiction
    · split at he
      · exact ih h o _ i evs c r out he
      · split at he
        · contradiction
        · split at he
          · split at he
            · exact ih h o ram i _ c r out he
            · contradiction
          · contradiction

end E5R.Thermostat.EffectCoreProperty
