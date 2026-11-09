import Projects.thermostat.HttpRequestBytes
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.RejectStatus
open E5R E5R.Thermostat HttpRequestSpec

def Allowed (s : Nat) : Prop := s=400 ∨ s=413 ∨ s=414 ∨ s=431 ∨ s=501 ∨ s=505

theorem requestLine (g : Nat → Nat) (i j status : Nat)
    (bad : HttpRequestSpec.requestLine g i j=.bad status) : Allowed status := by
  unfold HttpRequestSpec.requestLine at bad
  dsimp only at bad
  repeat' first | split at bad | (cases bad;first | exact Or.inl rfl | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

  all_goals cases bad

theorem headerLine (g : Nat → Nat) (i j status : Nat)
    (bad : HttpRequestSpec.headerLine g i j=.bad status) : Allowed status := by
  unfold HttpRequestSpec.headerLine at bad
  dsimp only at bad
  repeat' first | split at bad | (cases bad;exact Or.inl rfl)

  all_goals cases bad

theorem clLoop (g : Nat → Nat) (e max acc p status : Nat)
    (bad : HttpRequestSpec.clLoop g e max acc p=.bad status) : Allowed status := by
  rw [HttpRequestSpec.clLoop] at bad
  split at bad
  · split at bad
    · cases bad;exact Or.inl rfl
    · split at bad
      · cases bad;exact Or.inr (Or.inl rfl)
      · exact clLoop g e max (acc*10+(g p-48)) (p+1) status bad
  · cases bad
termination_by e-p

theorem contentLength (g : Nat → Nat) (s e max status : Nat)
    (bad : HttpRequestSpec.contentLength g s e max=.bad status) : Allowed status := by
  unfold HttpRequestSpec.contentLength at bad
  split at bad
  · cases bad;exact Or.inl rfl
  · exact clLoop g e max 0 s status bad

theorem addHeader (g : Nat → Nat) (f : Fields) (ns ne vs ve le minor maxBody status : Nat)
    (bad : HttpRequestSpec.addHeader g f ns ne vs ve le minor maxBody=.bad status) : Allowed status := by
  unfold HttpRequestSpec.addHeader at bad
  dsimp only at bad
  split at bad
  · cases bad;exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · split at bad
    · split at bad
      · cases bad;exact Or.inl rfl
      · cases bad
    · split at bad
      · split at bad
        · cases bad;exact Or.inl rfl
        · cases h : HttpRequestSpec.contentLength g vs ve maxBody with
          | bad s => simp only [h] at bad;cases bad;exact contentLength g vs ve maxBody status h
          | ok v => simp only [h] at bad;cases bad
      · split at bad
        · split at bad
          · cases bad;exact Or.inl rfl
          · split at bad
            · cases bad;exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
            · cases bad
        · cases bad

theorem fields (g : Nat → Nat) (n minor maxBody i status : Nat) (f : Fields)
    (bad : HttpRequestSpec.fields g n minor maxBody i f=.bad status) : Allowed status := by
  rw [HttpRequestSpec.fields] at bad
  split at bad
  · dsimp only at bad
    split at bad
    · cases bad
    · split at bad
      · cases bad;exact Or.inl rfl
      · split at bad
        · cases bad
        · cases hh : HttpRequestSpec.headerLine g i (lineEnd g i n) with
          | bad s => simp only [hh] at bad;cases bad;exact headerLine g i (lineEnd g i n) status hh
          | ok k vs ve =>
            simp only [hh] at bad
            cases ha : HttpRequestSpec.addHeader g f i k vs ve (lineEnd g i n) minor maxBody with
            | bad s => simp only [ha] at bad;cases bad;exact addHeader g f i k vs ve (lineEnd g i n) minor maxBody status ha
            | ok f' =>
              simp only [ha] at bad
              exact fields g n minor maxBody (lineEnd g i n+2) status f' bad
  · cases bad
termination_by n-i
decreasing_by have := scan_ge notEol g i n; unfold lineEnd at *;omega

theorem parse (input : List (BitVec 8)) (maxHead maxBody status : Nat)
    (reject : HttpRequestBytes.parse input maxHead maxBody=.reject status) : Allowed status := by
  unfold HttpRequestBytes.parse HttpRequestSpec.parseHead at reject
  dsimp only at reject
  split at reject
  · split at reject <;> cases reject
    exact Or.inr (Or.inr (Or.inl rfl))
  · split at reject
    · cases reject;exact Or.inl rfl
    · let n := readLimit (HttpRequestBytes.bytes input).length maxHead
      let g := window (HttpRequestBytes.bytes input) n
      let j := lineEnd g 0 n
      change (match HttpRequestSpec.requestLine g 0 j with
        | .bad st => HeadR.reject st
        | .ok ms me ts te minor =>
          match HttpRequestSpec.fields g n minor maxBody (j+2) Fields.empty with
          | .more => if decide (maxHead≤(HttpRequestBytes.bytes input).length) then HeadR.reject 431 else .incomplete
          | .bad st => .reject st
          | .done f len => if minor=1 ∧ !f.host then .reject 400 else
              .done ⟨(ms,me),(ts,te),minor,f.headers,len,if f.te then .chunked else if f.hasCl then .length f.cl else .empty⟩)=HeadR.reject status at reject
      cases hr : HttpRequestSpec.requestLine g 0 j with
      | bad s => simp only [hr] at reject;cases reject;exact requestLine g 0 j status hr
      | ok ms me ts te minor =>
        simp only [hr] at reject
        cases hf : HttpRequestSpec.fields g n minor maxBody (j+2) Fields.empty with
        | more => simp only [hf] at reject;split at reject <;> cases reject;exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        | bad s => simp only [hf] at reject;cases reject;exact fields g n minor maxBody (j+2) status Fields.empty hf
        | done f len => simp only [hf] at reject;split at reject <;> cases reject;exact Or.inl rfl

theorem bounds {status : Nat} (h : Allowed status) : 200≤status ∧ status≤599 := by
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
end E5R.Thermostat.RejectStatus
