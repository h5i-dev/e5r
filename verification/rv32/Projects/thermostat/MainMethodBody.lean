import Projects.thermostat.MainMethodLength
import Projects.thermostat.MainMethodThree
import Projects.thermostat.MainMethodFour
set_option autoImplicit false
namespace E5R.Thermostat.MainMethodBody
open E5R E5R.Thermostat

/-- All method lengths, including every nonmatching byte string. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (bytes : Nat → BitVec 8) (len : Nat)
    (hp : c.pc=MainMethodLength.destination len) (h15 : c.get 15=base) (h14 : c.get 14=6#32)
    (memory : ∀ k, k<len → B.inRam (base+BitVec.ofNat 32 k) 1=true)
    (data : ∀ k, k<len → ram (base+BitVec.ofNat 32 k)=bytes k) :
    ∃ n d, n≤24 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001160#32 ∧
      d.get 14=BitVec.ofNat 32 (MainMethodSpec.tag (MainMethodSpec.classify len (fun i => (bytes i).toNat))) ∧
      MainMethodSuffix.Frame c d ∧ d.sameCsr c := by
  by_cases three : len=3
  · subst len
    exact MainMethodThree.contract B c ram base bytes (by simpa [MainMethodLength.destination] using hp) h15 h14 memory data
  · by_cases four : len=4
    · subst len
      exact MainMethodFour.contract B c ram base bytes (by simpa [MainMethodLength.destination] using hp) h15 h14 memory data
    · by_cases five : len=5
      · subst len
        obtain ⟨n,d,nb,trace,pc,d14,dr,dc⟩ := MainMethodSuffixes.patch B c ram base bytes (by simpa [MainMethodLength.destination] using hp) h15 h14 memory data
        refine ⟨n,d,by omega,trace,pc,?_,dr,dc⟩
        by_cases good : (bytes 0).toNat=80 ∧ (bytes 1).toNat=65 ∧ (bytes 2).toNat=84 ∧ (bytes 3).toNat=67 ∧ (bytes 4).toNat=72
        · simpa [MainMethodSpec.classify,MainMethodSpec.tag,good] using d14
        · simpa [MainMethodSpec.classify,MainMethodSpec.tag,good] using d14
      · by_cases six : len=6
        · subst len
          obtain ⟨n,d,nb,trace,pc,d14,dr,dc⟩ := MainMethodSuffixes.delete B c ram base bytes (by simpa [MainMethodLength.destination] using hp) h15 h14 memory data
          refine ⟨n,d,by omega,trace,pc,?_,dr,dc⟩
          by_cases good : (bytes 0).toNat=68 ∧ (bytes 1).toNat=69 ∧ (bytes 2).toNat=76 ∧ (bytes 3).toNat=69 ∧ (bytes 4).toNat=84 ∧ (bytes 5).toNat=69
          · simpa [MainMethodSpec.classify,MainMethodSpec.tag,good] using d14
          · simpa [MainMethodSpec.classify,MainMethodSpec.tag,good] using d14
        · refine ⟨0,c,by decide,.refl _,?_,?_,fun _ _ _ _ _ => rfl,rfl⟩
          · simpa [MainMethodLength.destination,three,four,five,six] using hp
          · simpa [MainMethodSpec.classify,MainMethodSpec.tag,three,four,five,six] using h14
end E5R.Thermostat.MainMethodBody
