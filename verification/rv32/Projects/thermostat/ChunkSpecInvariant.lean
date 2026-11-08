import Projects.thermostat.HttpRequestSpec
namespace E5R.Thermostat.ChunkSpecInvariant
open HttpRequestSpec

/-- Bounds maintained by complete or partial chunked input. A partial size
    may exceed the body limit, and is rejected only at the following CR. -/
structure Inv (maxBody : Nat) (s : CState) : Prop where
  phase : s.phase ≤ 7
  size : s.size < 4294967296
  digits : s.digits ≤ 8
  total : s.total ≤ maxBody

theorem initial (maxBody : Nat) : Inv maxBody cStart := by
  constructor <;> simp [cStart]

theorem hex_bound (b : Nat) : hexv b ≤ 16 := by
  unfold hexv
  split <;> (try split) <;> (try split) <;> omega

/-- The pure streaming transition preserves the representation bounds even
    when it rejects malformed input. No input arrival or eventual completion
    is assumed. -/
theorem preserved (s : CState) (b maxBody : Nat) (h : Inv maxBody s)
    (hm : maxBody < 4294967296) : Inv maxBody (chunkStep s b maxBody).1 := by
  rcases h with ⟨hp,hs,hd,ht⟩
  unfold chunkStep
  split
  · unfold sizeStep
    split
    · rename_i hv
      split
      · exact ⟨hp,hs,hd,ht⟩
      · rename_i hb
        constructor <;> simp only <;> omega
    · split
      · split
        · exact ⟨hp,hs,hd,ht⟩
        · rename_i hb
          constructor <;> simp only <;> omega
      · exact ⟨hp,hs,hd,ht⟩
  · split
    · split
      · exact ⟨hp,hs,hd,ht⟩
      · constructor
        · simp only;split <;> omega
        · exact hs
        · simp
        · exact ht
    · split
      · split
        · constructor <;> simp only <;> omega
        · constructor <;> simp only <;> omega
      · split
        · unfold expectStep
          split
          · exact ⟨hp,hs,hd,ht⟩
          · exact ⟨by simp,hs,hd,ht⟩
        · split
          · unfold expectStep
            split <;> (constructor <;> simp only <;> omega)
          · split
            · unfold expectStep
              split
              · exact ⟨hp,hs,hd,ht⟩
              · exact ⟨by simp,hs,hd,ht⟩
            · split
              · unfold expectStep
                split
                · exact ⟨hp,hs,hd,ht⟩
                · exact ⟨by simp,hs,hd,ht⟩
              · exact ⟨hp,hs,hd,ht⟩

end E5R.Thermostat.ChunkSpecInvariant
