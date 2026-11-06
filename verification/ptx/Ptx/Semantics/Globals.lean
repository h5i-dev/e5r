/- Statically initialized module data, from PTX ISA variable declarations.
The load image is not an instruction and is never substituted for arbitrary
caller memory: initialize writes precisely its bytes, and its relation to the
launch's symbol addresses, allocations and initial memory is explicit. -/
import Ptx.Semantics.SIMT

namespace Ptx

/-- Install one definition, preserving every other byte. -/
def GlobalVar.install (g : GlobalVar) (base : Addr) (m : Mem) : Mem := fun a =>
  if h : (a - base).toNat < g.bytes.length then g.bytes[(a - base).toNat] else m a

/-- The module loader's memory image at an arbitrary placement. -/
def installGlobals (globals : List GlobalVar) (sym : String → Addr) (m : Mem) : Mem :=
  globals.foldr (fun g rest => g.install (sym g.name) rest) m

/-- Exact byte initialization, including zeros implicit in PTX definitions. -/
def GlobalVar.Initialized (g : GlobalVar) (base : Addr) (m : Mem) : Prop :=
  ∀ i, (hi : i < g.bytes.length) → m (base + BitVec.ofNat 64 i) = g.bytes[i]'hi

/-- Static global allocation is explicit; it does not grant access to any
other address or overlap application buffers by changing the allocation list. -/
def Module.GlobalsReady (M : Module) (L : Launch) (m : Mem) : Prop :=
  (∀ g ∈ M.globals, 0 < g.align ∧ (L.shared g.name).toNat % g.align = 0 ∧
    (L.shared g.name).toNat + g.bytes.length ≤ 2^64 ∧
    (∃ region ∈ L.alloc, region.base = L.shared g.name ∧ region.size = g.bytes.length) ∧
    g.Initialized (L.shared g.name) m) ∧
  M.globals.Pairwise (fun g h => ∀ a,
    covers (L.shared g.name) g.bytes.length a → ¬ covers (L.shared h.name) h.bytes.length a)

/-- Load-time table bytes are hypotheses of execution proofs, not fresh axioms. -/
theorem GlobalVar.install_at (g : GlobalVar) (base : Addr) (m : Mem)
    (bound : g.bytes.length ≤ 2^64) (i : Nat) (hi : i < g.bytes.length) :
    g.install base m (base + BitVec.ofNat 64 i) = g.bytes[i] := by
  have hoff : (base + BitVec.ofNat 64 i - base).toNat = i := by
    simp only [add_sub_left, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  simp only [GlobalVar.install, hoff, dite_eq_left hi]

theorem GlobalVar.install_outside (g : GlobalVar) (base : Addr) (m : Mem) (a : Addr)
    (h : ¬ covers base g.bytes.length a) : g.install base m a = m a := by
  simp only [GlobalVar.install, covers] at *
  exact dite_eq_right h

/-- Initializing data preserves the whole arbitrary caller memory outside
all module definitions, including input/output allocations and canaries. -/
theorem installGlobals_frame (globals : List GlobalVar) (sym : String → Addr)
    (m : Mem) (a : Addr) (h : ∀ g ∈ globals, ¬ covers (sym g.name) g.bytes.length a) :
    installGlobals globals sym m a = m a := by
  induction globals with
  | nil => rfl
  | cons g rest ih =>
    change g.install (sym g.name) (installGlobals rest sym m) a = m a
    rw [g.install_outside _ _ _ (h g (by simp))]
    exact ih (fun v hv => h v (by simp [hv]))

/-- A concrete loader exists for every disjoint load image; the initialization
predicate is not vacuous even though the remaining caller bytes are arbitrary. -/
theorem installGlobals_initialized (globals : List GlobalVar) (sym : String → Addr)
    (m : Mem) (bounds : ∀ g ∈ globals, g.bytes.length ≤ 2^64)
    (disjoint : globals.Pairwise (fun g h => ∀ a,
      covers (sym g.name) g.bytes.length a → ¬ covers (sym h.name) h.bytes.length a)) :
    ∀ g ∈ globals, g.Initialized (sym g.name) (installGlobals globals sym m) := by
  induction globals with
  | nil => simp
  | cons head rest ih =>
    rw [List.pairwise_cons] at disjoint
    intro g hg i hi
    rcases List.mem_cons.mp hg with h | h
    · subst g
      exact head.install_at _ _ (bounds head (by simp)) i hi
    · have hoff : (sym g.name + BitVec.ofNat 64 i - sym g.name).toNat = i := by
        simp only [add_sub_left, BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (by have := bounds g (by simp [h]); omega)
      have hgcover : covers (sym g.name) g.bytes.length (sym g.name + BitVec.ofNat 64 i) := by
        simpa only [covers, hoff] using hi
      have hn : ¬ covers (sym head.name) head.bytes.length (sym g.name + BitVec.ofNat 64 i) := by
        intro hc
        exact disjoint.1 g h _ hc hgcover
      change head.install _ _ _ = _
      rw [head.install_outside _ _ _ hn]
      exact ih (fun v hv => bounds v (by simp [hv])) disjoint.2 g h i hi

/-- Explicit valid placements construct a ready module over any caller memory.
The initializer does not impose values on the caller's remaining memory. -/
theorem Module.globalsReady_install (M : Module) (L : Launch) (m : Mem)
    (placed : ∀ g ∈ M.globals, 0 < g.align ∧ (L.shared g.name).toNat % g.align = 0 ∧
      (L.shared g.name).toNat + g.bytes.length ≤ 2^64 ∧
      ∃ region ∈ L.alloc, region.base = L.shared g.name ∧ region.size = g.bytes.length)
    (disjoint : M.globals.Pairwise (fun g h => ∀ a,
      covers (L.shared g.name) g.bytes.length a → ¬ covers (L.shared h.name) h.bytes.length a)) :
    M.GlobalsReady L (installGlobals M.globals L.shared m) := by
  refine ⟨?_, disjoint⟩
  intro g hg
  obtain ⟨ha, hm, hb, hr⟩ := placed g hg
  refine ⟨ha, hm, hb, hr, ?_⟩
  exact installGlobals_initialized M.globals L.shared m
    (fun v hv => by have := (placed v hv).2.2.1; omega) disjoint g hg

/-- Actual four-byte global loads reconstruct the emitted little-endian table
bits exactly; neither decimal conversion nor a mathematical decoder is used. -/
theorem GlobalVar.Initialized.read32 {g : GlobalVar} {base : Addr} {m : Mem}
    (init : g.Initialized base m) (off : Nat) (hi : off + 4 ≤ g.bytes.length) :
    rd32 m (base + BitVec.ofNat 64 off) =
      g.bytes[off + 3]'(by omega) ++ g.bytes[off + 2]'(by omega) ++
      g.bytes[off + 1]'(by omega) ++ g.bytes[off]'(by omega) := by
  have addr (i : Nat) : base + BitVec.ofNat 64 off + BitVec.ofNat 64 i =
      base + BitVec.ofNat 64 (off + i) := by
    simp only [BitVec.ofNat_add, BitVec.add_assoc]
  unfold rd32
  rw [show (3 : Addr) = BitVec.ofNat 64 3 from rfl, addr 3,
      show (2 : Addr) = BitVec.ofNat 64 2 from rfl, addr 2,
      show (1 : Addr) = BitVec.ofNat 64 1 from rfl, addr 1]
  rw [init (off+3) (by omega), init (off+2) (by omega),
      init (off+1) (by omega), init off (by omega)]

/-- An ordinary kernel store whose footprint excludes a table preserves its
exact initialized state; no write protection is silently assumed. -/
theorem GlobalVar.Initialized.store_frame {g : GlobalVar} {base : Addr} {m : Mem}
    (init : g.Initialized base m) (dst : Addr) (sz : Size) (v : Val)
    (outside : ∀ i, i < g.bytes.length → ¬ covers dst sz.bytes (base + BitVec.ofNat 64 i)) :
    g.Initialized base (wr m dst sz v) := by
  intro i hi
  rw [wr_outside (outside i hi)]
  exact init i hi

#print axioms GlobalVar.Initialized.read32
#print axioms Module.globalsReady_install
#print axioms installGlobals_frame
#print axioms installGlobals_initialized
#print axioms GlobalVar.Initialized.store_frame
end Ptx
