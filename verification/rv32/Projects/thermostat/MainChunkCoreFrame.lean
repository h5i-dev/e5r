import Theories.Logic
namespace E5R.Thermostat.MainChunkCoreFrame
open E5R

/-- Persistent main registers, excluding the cached byte, input cursor and
    conditional status that this loop intentionally updates. -/
def Kept (r : Reg) : Prop := r=2 ∨ r=8 ∨ r=9 ∨ (18≤r.val ∧ r≠20 ∧ r≠24 ∧ r≠27)
instance (r : Reg) : Decidable (Kept r) := by unfold Kept;infer_instance

def At (before after : Core) : Prop := ∀ r, Kept r → after.get r=before.get r

theorem callee_saved {r : Reg} (h : Kept r) : r=1 ∨ r=2 ∨ r=8 ∨ r=9 ∨ 18≤r.val := by
  rcases h with h|h|h|h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h.1)))

theorem trans {a b c} (h : At a b) (g : At b c) : At a c := fun r hr => (g r hr).trans (h r hr)

theorem masked {before after : Core} (h : after.sameCsr before) (hm : before.mie_=false) :
    after.mie_=false := (congrArg Prod.fst h).trans hm

end E5R.Thermostat.MainChunkCoreFrame
