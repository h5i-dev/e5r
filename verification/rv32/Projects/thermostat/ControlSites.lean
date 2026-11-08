-- Each candidate is checked separately to bound kernel replay memory.
import Projects.thermostat.ControlSiteList
import Projects.thermostat.PackedFetch
namespace E5R.Thermostat.Control
open E5R

def safeAt (a : Nat) : Bool := match fetchDecode img (BitVec.ofNat 32 a) with
  | none => true
  | some (i,_) => decide (Safe i)

def classifyFetch (f : Option (Word × Word)) : Bool :=
  match f with
  | none => true
  | some (bits,len) => match decode bits len with
    | none => true
    | some i => decide (Safe i)

theorem safeAt_fetch (a : Nat) : safeAt a = classifyFetch (fetch img (BitVec.ofNat 32 a)) := by
  unfold safeAt fetchDecode classifyFetch
  cases fetch img (BitVec.ofNat 32 a) with
  | none => rfl
  | some v =>
    rcases v with ⟨bits,len⟩
    simp only
    cases h : decode bits len <;> simp [h]

theorem safeAt_fast (a : Nat) (h1 : 0x80000000 ≤ (BitVec.ofNat 32 a).toNat)
    (h2 : (BitVec.ofNat 32 a).toNat+4 ≤ 0x800056a8) :
    safeAt a = classifyFetch (PackedFetch.fetchT PackedFetch.textByte (BitVec.ofNat 32 a)) :=
  (safeAt_fetch a).trans (congrArg classifyFetch (PackedFetch.fetch_text _ h1 h2))

theorem safe2147483648 : safeAt 2147483648 = true := (safeAt_fast _ (by decide) (by decide)).trans (by decide +kernel)
theorem safe2147483652 : safeAt 2147483652 = true := (safeAt_fast _ (by decide) (by decide)).trans (by decide +kernel)
theorem safe2147490458 : safeAt 2147490458 = true := (safeAt_fast _ (by decide) (by decide)).trans (by decide +kernel)
theorem safe2147490528 : safeAt 2147490528 = true := (safeAt_fast _ (by decide) (by decide)).trans (by decide +kernel)
theorem safe2147493648 : safeAt 2147493648 = true := (safeAt_fast _ (by decide) (by decide)).trans (by decide +kernel)
theorem safe2147493652 : safeAt 2147493652 = true := (safeAt_fast _ (by decide) (by decide)).trans (by decide +kernel)
theorem safe2147493676 : safeAt 2147493676 = true := (safeAt_fast _ (by decide) (by decide)).trans (by decide +kernel)
theorem safe2147495066 : safeAt 2147495066 = true := (safeAt_fast _ (by decide) (by decide)).trans (by decide +kernel)
theorem safe2147495346 : safeAt 2147495346 = true := (safeAt_fast _ (by decide) (by decide)).trans (by decide +kernel)
theorem safe2147495354 : safeAt 2147495354 = true := (safeAt_fast _ (by decide) (by decide)).trans (by decide +kernel)
theorem safe2147495566 : safeAt 2147495566 = true := (safeAt_fast _ (by decide) (by decide)).trans (by decide +kernel)
theorem safe2147503270 : safeAt 2147503270 = true := (safeAt_fast _ (by decide) (by decide)).trans (by decide +kernel)
theorem safe2147504968 : safeAt 2147504968 = true := (safeAt_fast _ (by decide) (by decide)).trans (by decide +kernel)
theorem safe2147504972 : safeAt 2147504972 = true := (safeAt_fast _ (by decide) (by decide)).trans (by decide +kernel)

theorem candidates_checked : expectedSites.all safeAt = true := by
  simp [expectedSites,safe2147483648,safe2147483652,safe2147490458,safe2147490528,safe2147493648,safe2147493652,safe2147493676,safe2147495066,safe2147495346,safe2147495354,safe2147495566,safe2147503270,safe2147504968,safe2147504972]
end E5R.Thermostat.Control
