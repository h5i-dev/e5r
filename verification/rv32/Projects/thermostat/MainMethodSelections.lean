import Projects.thermostat.MainMethodSelectHead
import Projects.thermostat.MainMethodSelectPost
import Projects.thermostat.MainMethodSelectPatch
import Projects.thermostat.MainMethodSelectDelete
import Projects.thermostat.MainMethodSelectGet
import Projects.thermostat.MainMethodSelectPut
import Projects.thermostat.MainMethodLastSetup
import Projects.thermostat.MainMethodSuffix
set_option autoImplicit false
namespace E5R.Thermostat.MainMethodSelections
open E5R E5R.Thermostat

theorem head (B : Board) (ram : Word → BitVec 8) (c : Core) (hp : c.pc=0x80000d9e#32) :
    ∃ n d, n≤4 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001154#32 ∧
      d.get 14=1#32 ∧ d.get 16=68#32 ∧ d.get 17=3#32 ∧ MainMethodSuffix.SelectFrame c d ∧ d.sameCsr c := by
  obtain ⟨d,trace,pc,d14,d16,d17,d0,dr,dc⟩ := MainMethodSelectHead.contract B c ram hp
  refine ⟨4,d,by decide,trace,pc,d14,d16,d17,?_,dc⟩
  intro r h14 h16 h17
  by_cases zero : r=0
  · subst r;rw [Core.get_zero,Core.get_zero]
  · exact dr r h14 h16 h17 zero

theorem post (B : Board) (ram : Word → BitVec 8) (c : Core) (hp : c.pc=0x80001136#32) :
    ∃ n d, n≤4 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001154#32 ∧
      d.get 14=2#32 ∧ d.get 16=84#32 ∧ d.get 17=3#32 ∧ MainMethodSuffix.SelectFrame c d ∧ d.sameCsr c := by
  obtain ⟨d,trace,pc,d14,d16,d17,d0,dr,dc⟩ := MainMethodSelectPost.contract B c ram hp
  refine ⟨4,d,by decide,trace,pc,d14,d16,d17,?_,dc⟩
  intro r h14 h16 h17
  by_cases zero : r=0
  · subst r;rw [Core.get_zero,Core.get_zero]
  · exact dr r h14 h16 h17 zero

theorem patch (B : Board) (ram : Word → BitVec 8) (c : Core) (hp : c.pc=0x80000e4a#32) :
    ∃ n d, n≤4 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001154#32 ∧
      d.get 14=4#32 ∧ d.get 16=72#32 ∧ d.get 17=4#32 ∧ MainMethodSuffix.SelectFrame c d ∧ d.sameCsr c := by
  obtain ⟨d,trace,pc,d17,d16,d14,d0,dr,dc⟩ := MainMethodSelectPatch.contract B c ram hp
  refine ⟨4,d,by decide,trace,pc,d14,d16,d17,?_,dc⟩
  intro r h14 h16 h17
  by_cases zero : r=0
  · subst r;rw [Core.get_zero,Core.get_zero]
  · exact dr r h17 h16 h14 zero

theorem delete (B : Board) (ram : Word → BitVec 8) (c : Core) (hp : c.pc=0x80000dec#32) :
    ∃ n d, n≤4 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001154#32 ∧
      d.get 14=5#32 ∧ d.get 16=69#32 ∧ d.get 17=5#32 ∧ MainMethodSuffix.SelectFrame c d ∧ d.sameCsr c := by
  obtain ⟨d,trace,pc,d17,d16,d14,d0,dr,dc⟩ := MainMethodSelectDelete.contract B c ram hp
  refine ⟨4,d,by decide,trace,pc,d14,d16,d17,?_,dc⟩
  intro r h14 h16 h17
  by_cases zero : r=0
  · subst r;rw [Core.get_zero,Core.get_zero]
  · exact dr r h17 h16 h14 zero

theorem put (B : Board) (ram : Word → BitVec 8) (c : Core) (hp : c.pc=0x8000114c#32) :
    ∃ n d, n≤4 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001154#32 ∧
      d.get 14=3#32 ∧ d.get 16=84#32 ∧ d.get 17=2#32 ∧ MainMethodSuffix.SelectFrame c d ∧ d.sameCsr c := by
  obtain ⟨d,trace,pc,d14,d16,d17,dr,dc⟩ := MainMethodSelectPut.contract B c ram hp
  refine ⟨3,d,by decide,trace,pc,d14,d16,d17,?_,dc⟩
  intro r h14 h16 h17
  exact dr r h14 h16 h17

theorem get (B : Board) (ram : Word → BitVec 8) (c : Core) (hp : c.pc=0x80000e16#32) :
    ∃ n d, n≤4 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001154#32 ∧
      d.get 14=0#32 ∧ d.get 16=84#32 ∧ d.get 17=2#32 ∧ MainMethodSuffix.SelectFrame c d ∧ d.sameCsr c := by
  obtain ⟨a,first,pa,a14,a0,ar,ac⟩ := MainMethodSelectGet.contract B c ram hp
  obtain ⟨d,last,pc,d16,d17,dr,dc⟩ := MainMethodLastSetup.contract B a ram pa
  refine ⟨4,d,by decide,first.trans last,pc,(dr 14 (by decide) (by decide)).trans a14,d16,d17,?_,dc.trans ac⟩
  intro r h14 h16 h17
  by_cases zero : r=0
  · subst r;rw [Core.get_zero,Core.get_zero]
  · exact (dr r h16 h17).trans (ar r h14 zero)
end E5R.Thermostat.MainMethodSelections
