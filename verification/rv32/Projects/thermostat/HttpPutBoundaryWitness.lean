import Projects.thermostat.HttpPutWitness
namespace E5R.Thermostat.HttpPutBoundaryWitness
open E5R E5R.Thermostat
abbrev B := UartPlatform.board
abbrev ram := HttpPutWitness.ram

def emptyCore : Core := HttpPutWitness.core.set 14 0#32

def rejectedCore : Core := HttpPutWitness.core.set 12 193#32

/-- Empty append does not read a source or require a destination allocation. -/
theorem empty_execution : ∃ d, Quiet.Steps B img 9 ⟨emptyCore,ram⟩ ⟨d,ram⟩ ∧
    FormatCursor.Returned emptyCore d ∧ d.get 10=1#32 ∧ d.get 11=13#32 := by
  obtain ⟨d,td,hr,d10,d11,_⟩ := HttpPutCopy.empty B emptyCore ram 192#32 13 (by decide)
    rfl (by rfl)
    (by rfl)
    (by rfl)
  exact ⟨d,td,hr,d10,d11⟩

/-- Position beyond capacity rejects before touching RAM, even without valid
    source/destination allocations. All saved registers and SP still return. -/
theorem rejected_execution : ∃ d, Quiet.Steps B img 7 ⟨rejectedCore,ram⟩ ⟨d,ram⟩ ∧
    FormatCursor.Returned rejectedCore d ∧ d.get 10=0#32 := by
  obtain ⟨d,td,hr,d10,_,_⟩ := HttpPut.contract B rejectedCore ram 0x80010000#32 0x80020000#32 192#32 193 [79#8,75#8]
    (by decide) (by decide) rfl
    (by rfl)
    (by rfl)
    (by rfl)
    (by rfl)
    (by rfl)
    (by intro h;exact False.elim ((by decide : ¬193+[79#8,75#8].length≤(192#32).toNat) h))
    (by intro h;exact False.elim ((by decide : ¬193+[79#8,75#8].length≤(192#32).toNat) h))
    (by intro h;exact False.elim ((by decide : ¬193+[79#8,75#8].length≤(192#32).toNat) h))
  have ht : HttpPut.duration (192#32).toNat 193 [79#8,75#8].length=7 := by decide
  have hm : HttpPut.memory ram 0x80020000#32 192#32 193 [79#8,75#8]=ram := by rfl
  rw [ht,hm] at td
  refine ⟨d,td,hr,?_⟩
  exact d10
end E5R.Thermostat.HttpPutBoundaryWitness
