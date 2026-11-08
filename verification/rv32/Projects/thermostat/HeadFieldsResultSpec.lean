import Projects.thermostat.HeadFieldsStepSpec
namespace E5R.Thermostat.HeadFieldsResultSpec
open E5R E5R.Thermostat HttpRequestSpec

def NumBound : Num → Prop
  | .bad status => status<65536
  | .ok _ => True

def AddedBound : Added → Prop
  | .bad status => status<65536
  | .ok _ => True

def HeaderBound : HdrLine → Prop
  | .bad status => status<65536
  | .ok _ _ _ => True

def Bound (cap : Nat) : Fielded → Prop
  | .more => True
  | .bad status => status<65536
  | .done _ len => 2≤len ∧ len≤cap

theorem number (g : Nat → Nat) (e max acc p : Nat) : NumBound (clLoop g e max acc p) := by
  rw [clLoop]
  split
  next inside =>
    split
    next invalid => simp [NumBound,AddedBound,HeaderBound,Bound]
    next digit =>
      split
      next overflow => simp [NumBound,AddedBound,HeaderBound,Bound]
      next fits => exact number g e max (acc*10+(g p-48)) (p+1)
  next outside => trivial
termination_by e-p
 decreasing_by omega

theorem content (g : Nat → Nat) (s e max : Nat) : NumBound (contentLength g s e max) := by
  unfold contentLength
  split
  · simp [NumBound,AddedBound,HeaderBound,Bound]
  · exact number g e max 0 s

theorem added (g : Nat → Nat) (f : Fields) (ns ne vs ve le minor max : Nat) :
    AddedBound (addHeader g f ns ne vs ve le minor max) := by
  unfold addHeader
  dsimp only
  split
  next full => simp [NumBound,AddedBound,HeaderBound,Bound]
  next room =>
    split
    next host => split <;> simp [NumBound,AddedBound,HeaderBound,Bound]
    next notHost =>
      split
      next cl =>
        split
        next bad => simp [NumBound,AddedBound,HeaderBound,Bound]
        next good =>
          have bound := content g vs ve max
          cases parsed : contentLength g vs ve max with
          | bad status => simpa only [parsed,NumBound,AddedBound] using bound
          | ok value => trivial
      next notCl =>
        split
        next te =>
          split
          next bad => simp [NumBound,AddedBound,HeaderBound,Bound]
          next good => split <;> simp [NumBound,AddedBound,HeaderBound,Bound]
        next other => trivial

theorem header (g : Nat → Nat) (i j : Nat) : HeaderBound (headerLine g i j) := by
  unfold headerLine
  dsimp only
  split
  · simp [NumBound,AddedBound,HeaderBound,Bound]
  · split
    · simp [NumBound,AddedBound,HeaderBound,Bound]
    · split
      · simp [NumBound,AddedBound,HeaderBound,Bound]
      · trivial

theorem term (g : Nat → Nat) (j cap : Nat) (notMore : lineTerm g j cap≠1) (notBad : lineTerm g j cap≠2) : j+2≤cap := by
  unfold lineTerm at notMore notBad
  repeat' split at notMore <;> simp_all <;> omega

theorem fields (g : Nat → Nat) (cap minor max i : Nat) (f : Fields) :
    Bound cap (HttpRequestSpec.fields g cap minor max i f) := by
  rw [HttpRequestSpec.fields]
  split
  next inside =>
    dsimp only
    split
    next more => trivial
    next notMore =>
      split
      next bad => simp [NumBound,AddedBound,HeaderBound,Bound]
      next notBad =>
        split
        next empty => exact ⟨by omega,term g _ cap notMore notBad⟩
        next nonempty =>
          have headerBound := header g i (lineEnd g i cap)
          cases line : headerLine g i (lineEnd g i cap) with
          | bad status => simpa only [line,HeaderBound,Bound] using headerBound
          | ok ne vs ve =>
            dsimp only
            have addBound := added g f i ne vs ve (lineEnd g i cap) minor max
            cases add : addHeader g f i ne vs ve (lineEnd g i cap) minor max with
            | bad status => simpa only [add,AddedBound,Bound] using addBound
            | ok nextFields => exact fields g cap minor max ((lineEnd g i cap)+2) nextFields
  next outside => trivial
termination_by cap-i
 decreasing_by have := HttpRequestSpec.scan_ge notEol g i cap;unfold lineEnd at *;omega
end E5R.Thermostat.HeadFieldsResultSpec
