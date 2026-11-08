import Projects.thermostat.ChunkSpecInvariant
namespace E5R.Thermostat.ChunkDecodedInvariant
open E5R.Thermostat HttpRequestSpec

def advance (decoded : Nat) (out : COut) : Nat := if out=.data then decoded+1 else decoded

/-- Announced bytes are counted in total at the size CR, while data bytes
    increase decoded individually. Data phase always has a positive remainder. -/
def Accounting (s : CState) (decoded : Nat) : Prop :=
  (if s.phase=1 ∨ s.phase=2 then s.total=decoded+s.size else s.total=decoded) ∧
  (s.phase=2 → 0<s.size) ∧ (3≤s.phase → s.size=0)

structure Inv (maxBody : Nat) (s : CState) (decoded : Nat) : Prop where
  bounded : ChunkSpecInvariant.Inv maxBody s
  accounting : Accounting s decoded

theorem initial (maxBody : Nat) : Inv maxBody cStart 0 := by
  exact ⟨ChunkSpecInvariant.initial maxBody,by simp [Accounting,cStart]⟩

theorem decoded_bound {maxBody s decoded} (h : Inv maxBody s decoded) : decoded≤maxBody := by
  have ht := h.bounded.total
  have ha := h.accounting.1
  split at ha <;> omega

theorem preserved (s : CState) (b maxBody decoded : Nat) (h : Inv maxBody s decoded)
    (hm : maxBody<4294967296) :
    Inv maxBody (chunkStep s b maxBody).1 (advance decoded (chunkStep s b maxBody).2) := by
  refine ⟨ChunkSpecInvariant.preserved s b maxBody h.bounded hm,?_⟩
  have ha := h.accounting.1
  have hp := h.accounting.2.1
  have hz := h.accounting.2.2
  unfold chunkStep
  split
  · rename_i phase
    have total : s.total=decoded := by simpa [phase] using ha
    unfold sizeStep
    split
    · split
      · simpa [advance] using h.accounting
      · simp [Accounting,advance,phase,total]
    · split
      · split
        · simpa [advance] using h.accounting
        · simp [Accounting,advance,total]
      · simpa [advance] using h.accounting
  · split
    · rename_i phase
      have total : s.total=decoded+s.size := by simpa [phase] using ha
      split
      · simpa [advance] using h.accounting
      · split
        · rename_i zero
          simp [Accounting,advance,zero,total]
        · rename_i nonzero
          simp [Accounting,advance,total]
          omega
    · split
      · rename_i phase
        have total : s.total=decoded+s.size := by simpa [phase] using ha
        have positive : 0<s.size := hp phase
        split
        · simp [Accounting,advance,total]
          omega
        · simp [Accounting,advance,phase,total]
          omega
      · split
        · rename_i phase
          have total : s.total=decoded := by simpa [phase] using ha
          have zero : s.size=0 := hz (by omega)
          unfold expectStep
          split
          · simpa [advance] using h.accounting
          · simp [Accounting,advance,total,zero]
        · split
          · rename_i phase
            have total : s.total=decoded := by simpa [phase] using ha
            unfold expectStep
            split
            · simp [Accounting,advance,phase,total]
            · simp [Accounting,advance,total]
          · split
            · rename_i phase
              have total : s.total=decoded := by simpa [phase] using ha
              have zero : s.size=0 := hz (by omega)
              unfold expectStep
              split
              · simpa [advance] using h.accounting
              · simp [Accounting,advance,total,zero]
            · split
              · rename_i phase
                have total : s.total=decoded := by simpa [phase] using ha
                have zero : s.size=0 := hz (by omega)
                unfold expectStep
                split
                · simpa [advance] using h.accounting
                · simp [Accounting,advance,total,zero]
              · simpa [advance] using h.accounting

end E5R.Thermostat.ChunkDecodedInvariant
