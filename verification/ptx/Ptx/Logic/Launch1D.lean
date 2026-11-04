/-
One-dimensional launches: `grid = (G, 1, 1)`, `block = (B, 1, 1)`.

`gid B t = ctaid.x * B + tid.x` as a natural number. It is injective on the
threads of the launch and hits every index below `G * B`, which is what turns
"thread `gid` owns element `gid`" into disjoint footprints and full coverage.
-/
import Ptx.Logic.RaceFreedom
import Ptx.Logic.Regions

namespace Ptx

def Launch.OneD (L : Launch) (G B : BitVec 32) : Prop :=
  L.grid = ⟨G, 1, 1⟩ ∧ L.block = ⟨B, 1, 1⟩

def gid (B : BitVec 32) (t : Tid) : Nat := t.ctaid.x.toNat * B.toNat + t.tid.x.toNat

section
variable {L : Launch} {G B : BitVec 32}

theorem Launch.OneD.thread (h : L.OneD G B) {t : Tid} (ht : t ∈ L.threads) :
    t.ctaid.x.toNat < G.toNat ∧ t.tid.x.toNat < B.toNat ∧ t.ctaid.y = 0 ∧ t.ctaid.z = 0 ∧
      t.tid.y = 0 ∧ t.tid.z = 0 := by
  rw [mem_threads] at ht
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
  rw [h.1] at h1 h2 h3; rw [h.2] at h4 h5 h6
  have one : (1 : BitVec 32).toNat = 1 := rfl
  dsimp only at h1 h2 h3 h4 h5 h6
  rw [one] at h2 h3 h5 h6
  refine ⟨h1, h4, ?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;> simp <;> omega

theorem gid_lt_of (hc : c < G.toNat) (ht : d < B.toNat) : c * B.toNat + d < G.toNat * B.toNat := by
  have : (c + 1) * B.toNat ≤ G.toNat * B.toNat := Nat.mul_le_mul_right _ hc
  rw [Nat.add_mul, Nat.one_mul] at this; omega

theorem Launch.OneD.gid_lt (h : L.OneD G B) {t : Tid} (ht : t ∈ L.threads) : gid B t < G.toNat * B.toNat := by
  obtain ⟨h1, h2, -⟩ := h.thread ht
  exact gid_lt_of h1 h2

/-- The 32-bit `ctaid.x * ntid.x + tid.x` does not wrap when the launch has at
most `2^31` threads. -/
theorem Launch.OneD.gid_bv (h : L.OneD G B) {t : Tid} (ht : t ∈ L.threads) (hGB : G.toNat * B.toNat ≤ 2 ^ 31) :
    (t.ctaid.x * B + t.tid.x).toNat = gid B t := by
  have hl := h.gid_lt ht
  obtain ⟨h1, h2, -⟩ := h.thread ht
  unfold gid at *
  rw [BitVec.toNat_add, BitVec.toNat_mul,
    Nat.mod_eq_of_lt (a := t.ctaid.x.toNat * B.toNat) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem Launch.OneD.gid_inj (h : L.OneD G B) {t u : Tid} (ht : t ∈ L.threads) (hu : u ∈ L.threads)
    (heq : gid B t = gid B u) : t = u := by
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := h.thread ht
  obtain ⟨u1, u2, u3, u4, u5, u6⟩ := h.thread hu
  unfold gid at heq
  have hB : 0 < B.toNat := by omega
  have hd : (t.ctaid.x.toNat * B.toNat + t.tid.x.toNat) % B.toNat = t.tid.x.toNat := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt t2]
  have hd' : (u.ctaid.x.toNat * B.toNat + u.tid.x.toNat) % B.toNat = u.tid.x.toNat := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt u2]
  have hq : (t.ctaid.x.toNat * B.toNat + t.tid.x.toNat) / B.toNat = t.ctaid.x.toNat := by
    rw [Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt t2, Nat.add_zero]
  have hq' : (u.ctaid.x.toNat * B.toNat + u.tid.x.toNat) / B.toNat = u.ctaid.x.toNat := by
    rw [Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt u2, Nat.add_zero]
  have ex : t.tid.x = u.tid.x := BitVec.eq_of_toNat_eq (by rw [← hd, ← hd', heq])
  have cx : t.ctaid.x = u.ctaid.x := BitVec.eq_of_toNat_eq (by rw [← hq, ← hq', heq])
  rcases t with ⟨⟨_, _, _⟩, ⟨_, _, _⟩⟩
  rcases u with ⟨⟨_, _, _⟩, ⟨_, _, _⟩⟩
  simp_all

/-- The thread whose `gid` is `i`. -/
def owner (B : BitVec 32) (i : Nat) : Tid :=
  { ctaid := ⟨BitVec.ofNat 32 (i / B.toNat), 0, 0⟩, tid := ⟨BitVec.ofNat 32 (i % B.toNat), 0, 0⟩ }

theorem Launch.OneD.owner_mem (h : L.OneD G B) {i : Nat} (hi : i < G.toNat * B.toNat) :
    owner B i ∈ L.threads ∧ gid B (owner B i) = i := by
  have hB : 0 < B.toNat := by
    rcases Nat.eq_zero_or_pos B.toNat with h0 | h0
    · rw [h0, Nat.mul_zero] at hi; omega
    · exact h0
  have hq : i / B.toNat < G.toNat := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi)
  have hr : i % B.toNat < B.toNat := Nat.mod_lt _ hB
  have hG := G.isLt; have hB' := B.isLt
  refine ⟨?_, ?_⟩
  · have e1 : (i / B.toNat) % 2 ^ 32 = i / B.toNat := Nat.mod_eq_of_lt (by omega)
    have e2 : (i % B.toNat) % 2 ^ 32 = i % B.toNat := Nat.mod_eq_of_lt (by omega)
    have one : (1 : BitVec 32).toNat = 1 := rfl
    rw [mem_threads, Launch.Thread, h.1, h.2]
    simp only [owner, BitVec.toNat_ofNat, e1, e2, one]
    refine ⟨hq, ?_, ?_, hr, ?_, ?_⟩ <;> decide
  · simp only [gid, owner, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : i / B.toNat < 2 ^ 32), Nat.mod_eq_of_lt (by omega : i % B.toNat < 2 ^ 32)]
    rw [Nat.mul_comm]; exact Nat.div_add_mod i B.toNat

end

theorem rd32_congr {m₁ m₂ : Mem} {a : Addr} (h : ∀ x, covers a 4 x → m₁ x = m₂ x) :
    rd32 m₁ a = rd32 m₂ a := by
  have := rd_congr (sz := .b4) h
  rw [rd_b4, rd_b4] at this
  simpa using congrArg lo32 this

/-- A grid that never faults, always progresses and has bounded executions
has a finished execution. -/
theorem GridOk.exists_done {K L c₀ W P bound} (g : GridOk K L c₀ W P bound) :
    ∃ c, Reach K L c₀ c ∧ Done K L c := by
  have key : ∀ d j c, bound - j = d → Steps K L j c₀ c → ∃ c', Reach K L c₀ c' ∧ Done K L c' := by
    intro d
    induction d using Nat.strongRecOn with
    | _ d ih =>
      intro j c hd hs
      rcases g.progress c (Reach.of_steps hs) with hdone | ⟨c', hc'⟩
      · exact ⟨c, Reach.of_steps hs, hdone⟩
      · have hs' := Steps.tail hs hc'
        have := g.bounded _ _ hs'
        have := g.bounded _ _ hs
        exact ih (bound - (j + 1)) (by omega) (j + 1) c' rfl hs'
  exact key _ 0 c₀ rfl (.refl _)

end Ptx
