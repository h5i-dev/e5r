import Projects.thermostat.RuntimeHeaderPrefix
import Projects.thermostat.HeaderSpec
import Projects.thermostat.MainCloseSpec
import Projects.thermostat.ApiWriteHttpSpec
set_option autoImplicit false
namespace E5R.Thermostat.RuntimeHeaderLookup
open E5R E5R.Thermostat

/-- Header slices are unchanged by compaction beyond the original head. -/
theorem slice {raw original : List (BitVec 8)} {cut first last : Nat}
    (same : raw.take cut=original) (inside : first≤last ∧ last≤cut) :
    (raw.drop first).take (last-first)=(original.drop first).take (last-first) := by
  rw [←same,List.drop_take,List.take_take,Nat.min_eq_left (by omega : last-first≤cut-first)]

theorem fields {raw original : List (BitVec 8)} {cut : Nat} (same : raw.take cut=original)
    (e : HeaderSpec.Entry) (inside : HeaderSpec.Bounds cut e) :
    HeaderSpec.name raw e=HeaderSpec.name original e ∧ HeaderSpec.value raw e=HeaderSpec.value original e := by
  exact ⟨slice same ⟨inside.1,inside.2.1⟩,slice same ⟨inside.2.2.1,inside.2.2.2⟩⟩

/-- The first-match rule and duplicates remain unchanged, for arbitrary query. -/
theorem lookup {raw original : List (BitVec 8)} {cut : Nat} (same : raw.take cut=original)
    (query : List (BitVec 8)) (entries : List HeaderSpec.Entry) (inside : ∀ e∈entries,HeaderSpec.Bounds cut e) :
    HeaderSpec.lookup raw query entries=HeaderSpec.lookup original query entries := by
  induction entries with
  | nil => rfl
  | cons e es ih =>
    have head := fields same e (inside e (by simp))
    simp only [HeaderSpec.lookup,head.1,head.2,ih (fun e he => inside e (by simp [he]))]

/-- All Connection fields and comma tokens survive; no first-field shortcut. -/
theorem close {raw original : List (BitVec 8)} {cut : Nat} (same : raw.take cut=original)
    (minor served : Nat) (entries : List HeaderSpec.Entry) (inside : ∀ e∈entries,HeaderSpec.Bounds cut e) :
    MainCloseSpec.mustClose minor served raw entries=MainCloseSpec.mustClose minor served original entries := by
  have all : MainCloseSpec.wantsClose raw entries=MainCloseSpec.wantsClose original entries := by
    induction entries with
    | nil => rfl
    | cons e es ih =>
      have head := fields same e (inside e (by simp))
      change (MainCloseSpec.field (HeaderSpec.name raw e) (HeaderSpec.value raw e) || MainCloseSpec.wantsClose raw es) =
        (MainCloseSpec.field (HeaderSpec.name original e) (HeaderSpec.value original e) || MainCloseSpec.wantsClose original es)
      rw [head.1,head.2,ih (fun e he => inside e (by simp [he]))]
  unfold MainCloseSpec.mustClose;rw [all]

theorem write {raw original : List (BitVec 8)} {cut : Nat} (same : raw.take cut=original)
    (s : Spec.Snapshot) (path body : List (BitVec 8)) (first : Option (List (BitVec 8)))
    (entries : List HeaderSpec.Entry) (inside : ∀ e∈entries,HeaderSpec.Bounds cut e) :
    ApiWriteHttpSpec.run s path first raw body entries=ApiWriteHttpSpec.run s path first original body entries := by
  unfold ApiWriteHttpSpec.run
  rw [lookup same (WireSpec.ascii "authorization") entries inside]
end E5R.Thermostat.RuntimeHeaderLookup
