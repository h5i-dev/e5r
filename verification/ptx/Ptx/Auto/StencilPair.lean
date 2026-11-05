/- Domain and direct concrete-execution relation for the concrete two-output stencil17 edits.
No mathematical stencil-output function occurs in this contract. -/
import Ptx.Auto.Stencil

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

namespace Ptx.Auto.StencilPair
open Ptx Ptx.Auto.Stencil

abbrev Args := Stencil.Args

structure Spec where
  input : String
  output : String
  length : String

namespace Spec
variable (S : Spec) (A : Args)

def launch (edited : Bool) : Launch :=
  { grid := ⟨if edited then A.G₁ else A.G,1,1⟩,
    block := ⟨if edited then A.B₁ else A.B,1,1⟩,
    params := fun p => if p = S.input then A.base S.input else
      if p = S.output then A.base S.output else if p = S.length then ext32 A.n else 0,
    alloc := [⟨A.base S.input,4*(A.n.toNat+16)⟩,⟨A.base S.output,4*A.n.toNat⟩] }

def Pre : Prop :=
  Fits (A.base S.input) (A.n.toNat+16) ∧ Fits (A.base S.output) A.n.toNat ∧
  (A.base S.input).toNat % 4 = 0 ∧ (A.base S.output).toNat % 4 = 0 ∧
  ((A.base S.input).toNat+4*(A.n.toNat+16) ≤ (A.base S.output).toNat ∨
    (A.base S.output).toNat+4*A.n.toNat ≤ (A.base S.input).toNat) ∧
  A.n.toNat ≤ A.G.toNat*A.B.toNat ∧ A.G.toNat*A.B.toNat ≤ 2^31 ∧
  (A.n.toNat+1)/2 ≤ A.G₁.toNat*A.B₁.toNat ∧ A.G₁.toNat*A.B₁.toNat ≤ 2^31

def R (x : Addr) : Prop := ∃ i < A.n.toNat+16, covers (elem (A.base S.input) i) 4 x

def W₀ (i : Nat) (x : Addr) : Prop := i < A.n.toNat ∧ covers (elem (A.base S.output) i) 4 x

def W₁ (g : Nat) (x : Addr) : Prop := ∃ j < 2, S.W₀ A (2*g+j) x

def External (x : Addr) : Prop := ∀ i < A.n.toNat, ¬ covers (elem (A.base S.output) i) 4 x

/-- Outputs are uint32 words; every other global byte must be preserved.
Both launches vary independently over the declared complete coverage domain. -/
def Equivalent (original edited : Kernel) : Prop :=
  original.shared = [] ∧ edited.shared = [] ∧
  ∀ (A : Args) (m : Mem) (sh : Dim3 → Mem)
    (r : Tid → String → Val) (p : Tid → String → Bool), S.Pre A →
    let L₀ := S.launch A false
    let L₁ := S.launch A true
    let c₀ := Cfg.init r p m sh
    Relational.Total original L₀ c₀ ∧ Relational.Total edited L₁ c₀ ∧
    (∀ c d, Reach original L₀ c₀ c → Done original L₀ c →
      Reach edited L₁ c₀ d → Done edited L₁ d →
      ∀ i < A.n.toNat, rd32 c.mem (elem (A.base S.output) i) = rd32 d.mem (elem (A.base S.output) i)) ∧
    (∀ c, Reach original L₀ c₀ c → Done original L₀ c → ∀ x, S.External A x → c.mem x = m x) ∧
    (∀ c, Reach edited L₁ c₀ c → Done edited L₁ c → ∀ x, S.External A x → c.mem x = m x)

def SafeOriginal (K : Kernel) : Prop :=
  ∀ A, S.Pre A → ∀ m t, t ∈ (S.launch A false).threads → ∀ r p,
    Safe K (S.launch A false).alloc ((S.launch A false).ctx t)
      (S.R A) (S.W₀ A (gid A.B t)) (fun s _ => action K ((S.launch A false).ctx t) s = .done ∧ True)
      ⟨0,r,p⟩ m

/-- Execute edited thread, then directly execute each original owner with a
postcondition comparing its concrete final word with the edited final memory.
There is no intervening output specification or shared arithmetic function. -/
def ThreadRelation (K₀ K₁ : Kernel) : Prop :=
  ∀ A, S.Pre A → ∀ (m : Mem) (r : Tid → String → Val) (p : Tid → String → Bool)
    t, t ∈ (S.launch A true).threads →
    Safe K₁ (S.launch A true).alloc ((S.launch A true).ctx t)
      (S.R A) (S.W₁ A (gid A.B₁ t))
      (fun s M₁ => action K₁ ((S.launch A true).ctx t) s = .done ∧
        ∀ j < 2, let i := 2*gid A.B₁ t+j; i < A.n.toNat →
          let u := owner A.B i
          Safe K₀ (S.launch A false).alloc ((S.launch A false).ctx u)
            (S.R A) (S.W₀ A i)
            (fun s M₀ => action K₀ ((S.launch A false).ctx u) s = .done ∧
              rd32 M₀ (elem (A.base S.output) i) = rd32 M₁ (elem (A.base S.output) i))
            (s0 r p m u) m)
      (s0 r p m t) m

theorem oneD₀ : (S.launch A false).OneD A.G A.B := ⟨rfl,rfl⟩
theorem oneD₁ : (S.launch A true).OneD A.G₁ A.B₁ := ⟨rfl,rfl⟩

theorem access_input {S : Spec} {A : Args} (hp : S.Pre A) (b : Bool) {i : Nat} (hi : i < A.n.toNat+16) :
    accessOk (S.launch A b).alloc (elem (A.base S.input) i) .b4 = true := by
  simp only [accessOk,launch,Size.bytes_b4,Bool.and_eq_true,beq_iff_eq,
    aligned_elem hp.1 hi hp.2.2.1,true_and,List.any_cons,List.any_nil,Bool.or_false]
  simp [holds_elem hp.1 hi]

theorem access_output {S : Spec} {A : Args} (hp : S.Pre A) (b : Bool) {i : Nat} (hi : i < A.n.toNat) :
    accessOk (S.launch A b).alloc (elem (A.base S.output) i) .b4 = true := by
  simp only [accessOk,launch,Size.bytes_b4,Bool.and_eq_true,beq_iff_eq,
    aligned_elem hp.2.1 hi hp.2.2.2.1,true_and,List.any_cons,List.any_nil,Bool.or_false]
  simp [holds_elem hp.2.1 hi]

theorem load_foot {S : Spec} {A : Args} {i : Nat} {W} (hi : i < A.n.toNat+16) :
    InFoot (S.R A) W ⟨.global,elem (A.base S.input) i,.b4,.read⟩ :=
  ⟨rfl,nofun,fun _ hx => .inr ⟨rfl,i,hi,hx⟩⟩

theorem store_foot₀ {S : Spec} {A : Args} {i : Nat} (hi : i < A.n.toNat) :
    InFoot (S.R A) (S.W₀ A i) ⟨.global,elem (A.base S.output) i,.b4,.write⟩ :=
  ⟨rfl,nofun,fun _ hx => .inl ⟨hi,hx⟩⟩

theorem store_foot₁ {S : Spec} {A : Args} {g j : Nat} (hj : j < 2) (hi : 2*g+j < A.n.toNat) :
    InFoot (S.R A) (S.W₁ A g) ⟨.global,elem (A.base S.output) (2*g+j),.b4,.write⟩ :=
  ⟨rfl,nofun,fun _ hx => .inl ⟨j,hj,hi,hx⟩⟩

/-- Reads of the original input commute with this edit's output stores. -/
theorem input_read_frame {S : Spec} {A : Args} (hp : S.Pre A)
    {i j : Nat} (hi : i < A.n.toNat+16) (hj : j < A.n.toNat) (m : Mem) (v : Val) :
    rd32 (wr m (elem (A.base S.output) j) .b4 v) (elem (A.base S.input) i) =
      rd32 m (elem (A.base S.input) i) := by
  have sep := hp.2.2.2.2.1
  exact rd32_wr_disjoint (fun x hx => elem_disjoint₂ hp.1 hp.2.1 sep hi hj hx)


theorem elem_offset_words (base : Addr) (i k : Nat) :
    elem base i + BitVec.ofNat 64 (4*k) = elem base (i+k) := by
  simp [elem,Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]

theorem elem_offset_bytes (base : Addr) (i k : Nat) (hk : k%4=0) :
    elem base i + BitVec.ofNat 64 k = elem base (i+k/4) := by
  have he : BitVec.ofNat 64 k = BitVec.ofNat 64 (4*(k/4)) := congrArg (BitVec.ofNat 64) (by omega)
  rw [he]
  exact elem_offset_words base i (k/4)

theorem elem_offset_val (base : Addr) (i : Nat) (k : Addr) (hk : k.toNat%4=0) :
    elem base i + k = elem base (i+k.toNat/4) := by
  have he : k = BitVec.ofNat 64 k.toNat := by simp
  calc
    elem base i + k = elem base i + BitVec.ofNat 64 k.toNat := congrArg (fun z => elem base i+z) he
    _ = elem base (i+k.toNat/4) := elem_offset_bytes base i k.toNat hk

end Spec

namespace Spec

theorem equivalent_of_threads {S : Spec} {K₀ K₁ : Kernel}
    (hsh₀ : K₀.shared = []) (hsh₁ : K₁.shared = [])
    (safe₀ : S.SafeOriginal K₀) (rel : S.ThreadRelation K₀ K₁) : S.Equivalent K₀ K₁ := by
  classical
  refine ⟨hsh₀,hsh₁,?_⟩
  intro A m sh r p hp L₀ L₁ c₀
  obtain ⟨fi,fo,ai,ao,sep,hn₀,hm₀,hn₁,hm₁⟩ := hp
  have hp : S.Pre A := ⟨fi,fo,ai,ao,sep,hn₀,hm₀,hn₁,hm₁⟩
  have hd₀ := S.oneD₀ A
  have hd₁ := S.oneD₁ A
  have so₀ : ∀ t ∈ L₀.threads, ∃ k,
      Solo K₀ L₀.alloc (L₀.ctx t) (S.R A) (S.W₀ A (gid A.B t)) (s0 r p m t) m k := by
    intro t ht
    obtain ⟨k,hk,_⟩ := (safe₀ A hp m t ht (r t) (p t)).solo
    exact ⟨k,hk⟩
  let n₀ : Tid → Nat := fun t => if h : t ∈ L₀.threads then (so₀ t h).choose else 0
  have hs₀ : ∀ t ∈ L₀.threads,
      Solo K₀ L₀.alloc (L₀.ctx t) (S.R A) (S.W₀ A (gid A.B t)) (s0 r p m t) m (n₀ t) := by
    intro t ht
    simpa only [n₀,dite_eq_left ht] using (so₀ t ht).choose_spec
  let M₀ := fun t => (trace K₀ L₀.alloc (L₀.ctx t) (n₀ t) (s0 r p m t) m).2
  have dis₀ : ∀ t ∈ L₀.threads, ∀ u ∈ L₀.threads, t ≠ u → ∀ x,
      S.W₀ A (gid A.B t) x → ¬ S.R A x ∧ ¬ S.W₀ A (gid A.B u) x := by
    intro t ht u hu htu x ⟨hi,hx⟩
    refine ⟨?_,?_⟩
    · rintro ⟨j,hj,hcov⟩
      exact elem_disjoint₂ fo fi (by omega) hi hj hx hcov
    · rintro ⟨hj,hcov⟩
      exact elem_disjoint fo hi hj (fun e => htu (hd₀.gid_inj ht hu e)) hx hcov
  have dis₁ : ∀ t ∈ L₁.threads, ∀ u ∈ L₁.threads, t ≠ u → ∀ x,
      S.W₁ A (gid A.B₁ t) x → ¬ S.R A x ∧ ¬ S.W₁ A (gid A.B₁ u) x := by
    intro t ht u hu htu x ⟨j,hj,hi,hx⟩
    refine ⟨?_,?_⟩
    · rintro ⟨q,hq,hcov⟩
      exact elem_disjoint₂ fo fi (by omega) hi hq hx hcov
    · rintro ⟨k,hk,hki,hcov⟩
      have hn : gid A.B₁ t ≠ gid A.B₁ u := fun e => htu (hd₁.gid_inj ht hu e)
      exact elem_disjoint fo hi hki (by omega) hx hcov
  obtain ⟨b₀,g₀⟩ := grid_sound (P := fun t M => ∀ x, S.W₀ A (gid A.B t) x → M x = M₀ t x)
    (fun t ht => ⟨n₀ t,hs₀ t ht,fun _ _ => rfl⟩) dis₀ sh
  let P₁ := fun t M => ∀ j < 2,
    let i := 2*gid A.B₁ t+j
    i < A.n.toNat → ∃ k,
      Solo K₀ L₀.alloc (L₀.ctx (owner A.B i)) (S.R A) (S.W₀ A i)
        (s0 r p m (owner A.B i)) m k ∧
      rd32 (trace K₀ L₀.alloc (L₀.ctx (owner A.B i)) k (s0 r p m (owner A.B i)) m).2
        (elem (A.base S.output) i) = rd32 M (elem (A.base S.output) i)
  have so₁ : ∀ t ∈ L₁.threads, ∃ k,
      Solo K₁ L₁.alloc (L₁.ctx t) (S.R A) (S.W₁ A (gid A.B₁ t)) (s0 r p m t) m k ∧
      P₁ t (trace K₁ L₁.alloc (L₁.ctx t) k (s0 r p m t) m).2 := by
    intro t ht
    obtain ⟨k,hk,hrel⟩ := (rel A hp m r p t ht).solo
    refine ⟨k,hk,?_⟩
    intro j hj
    dsimp only
    intro hi
    exact (hrel j hj hi).solo
  obtain ⟨b₁,g₁⟩ := grid_sound so₁ dis₁ sh
  refine ⟨⟨g₀.noFault,g₀.progress,⟨b₀,g₀.bounded⟩,g₀.raceFree,g₀.exists_done⟩,
    ⟨g₁.noFault,g₁.progress,⟨b₁,g₁.bounded⟩,g₁.raceFree,g₁.exists_done⟩,?_,?_,?_⟩
  · intro c d hc hcd hd hdd i hi
    obtain ⟨ht₀,hgid₀⟩ := hd₀.owner_mem (i := i) (by omega)
    obtain ⟨ht₁,hgid₁⟩ := hd₁.owner_mem (i := i/2) (by omega)
    obtain ⟨MC,hMC,hC⟩ := (g₀.final c hc hcd).1 _ ht₀
    obtain ⟨MD,hMD,hD⟩ := (g₁.final d hd hdd).1 _ ht₁
    have hiw : S.W₀ A (gid A.B (owner A.B i)) = S.W₀ A i := by rw [hgid₀]
    have decomp : 2*(i/2)+i%2 = i := by omega
    have hrel := hMD (i%2) (by omega)
    dsimp only [P₁] at hrel
    rw [hgid₁,decomp] at hrel
    obtain ⟨k,hk,heq⟩ := hrel hi
    have hsolo := hs₀ _ ht₀
    have unique := solo_unique hsolo hk
    have hmem : M₀ (owner A.B i) =
        (trace K₀ L₀.alloc (L₀.ctx (owner A.B i)) k (s0 r p m (owner A.B i)) m).2 := by
      exact congrArg Prod.snd unique
    calc
      rd32 c.mem (elem (A.base S.output) i) = rd32 MC (elem (A.base S.output) i) :=
        rd32_congr (fun x hx => hC x (by rw [hgid₀]; exact ⟨hi,hx⟩))
      _ = rd32 (M₀ (owner A.B i)) (elem (A.base S.output) i) :=
        rd32_congr (fun x hx => hMC x (by rw [hgid₀]; exact ⟨hi,hx⟩))
      _ = rd32 (trace K₀ L₀.alloc (L₀.ctx (owner A.B i)) k (s0 r p m (owner A.B i)) m).2
          (elem (A.base S.output) i) := congrArg (fun M => rd32 M (elem (A.base S.output) i)) hmem
      _ = rd32 MD (elem (A.base S.output) i) := heq
      _ = rd32 d.mem (elem (A.base S.output) i) :=
        (rd32_congr (fun x hx => hD x (by
          refine ⟨i%2,by omega,?_⟩
          rw [hgid₁,decomp]
          exact ⟨hi,hx⟩))).symm
  · intro c hc hd x hx
    exact (g₀.final c hc hd).2 x (fun t ht hw => hx _ hw.1 hw.2)
  · intro c hc hd x hx
    exact (g₁.final c hc hd).2 x (fun t ht ⟨j,hj,hi,hw⟩ => hx _ hi hw)

end Spec

end Ptx.Auto.StencilPair
