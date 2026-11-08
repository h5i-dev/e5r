import Projects.thermostat.Bytes
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.WordRegions
open E5R E5R.Thermostat

def Disjoint (a : Word) (n : Nat) (b : Word) (m : Nat) : Prop :=
  ∀ i : Fin n, ∀ j : Fin m, a+BitVec.ofNat 32 i.val ≠ b+BitVec.ofNat 32 j.val

theorem before (a b : Word) (n m : Nat) (ha : a.toNat+n ≤ b.toNat) (hb : b.toNat+m ≤ 2^32) : Disjoint a n b m := by
  intro i j he
  have hi := i.isLt
  have hj := j.isLt
  have hbn := b.isLt
  have hi32 : i.val < 2^32 := by omega
  have hj32 : j.val < 2^32 := by omega
  have hai : a.toNat+i.val < 2^32 := by omega
  have hbj : b.toNat+j.val < 2^32 := by omega
  have hh := congrArg BitVec.toNat he
  simp only [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hi32,Nat.mod_eq_of_lt hj32,
    Nat.mod_eq_of_lt hai,Nat.mod_eq_of_lt hbj] at hh
  omega

theorem symm {a n b m} (h : Disjoint a n b m) : Disjoint b m a n := fun i j => Ne.symm (h j i)

theorem shrink {a n b m n' m'} (h : Disjoint a n b m) (hn : n' ≤ n) (hm : m' ≤ m) : Disjoint a n' b m' :=
  fun i j => h ⟨i.val,by have := i.isLt;omega⟩ ⟨j.val,by have := j.isLt;omega⟩
theorem outside {a n b m} (h : Disjoint a n b m) (hb : b.toNat+m ≤ 2^32) (i : Fin n) :
    ¬(b.toNat ≤ (a+BitVec.ofNat 32 i.val).toNat ∧ (a+BitVec.ofNat 32 i.val).toNat < b.toNat+m) := by
  intro hx
  let k := (a+BitVec.ofNat 32 i.val).toNat-b.toNat
  have hk : k < m := by dsimp only [k];omega
  have hk32 : k < 2^32 := by omega
  have hsum : b.toNat+k < 2^32 := by dsimp only [k];omega
  have he : a+BitVec.ofNat 32 i.val = b+BitVec.ofNat 32 k := by
    apply Eq.symm
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hk32,Nat.mod_eq_of_lt hsum]
    dsimp only [k];omega
  exact h i ⟨k,hk⟩ he
end E5R.Thermostat.WordRegions
