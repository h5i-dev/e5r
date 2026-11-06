/- Bridge from both exact, unchanged exported entries and all original globals
into the already checked local FP4 lemma. This is not whole-kernel acceptance.
The remaining obligation is to prove the actual entry's write footprints and
finite-scale invariants for every reachable interleaving. -/
import Ptx.Semantics.Globals
import Ptx.Semantics.Warp
import Ptx.Logic.Regions
import FP4Original
import FP4Edited
import TableSign

namespace FP4Whole
open Ptx

def lut : GlobalVar := ⟨"fp4_dequantization_lut", 4,
  [0,0,0,0,171,170,170,59,171,170,42,63,0,0,128,63,
   171,170,170,62,0,0,0,63,171,170,42,62,0,0,128,62]⟩

theorem exact_globals_identical : FP4Original.module.globals = FP4Edited.module.globals := rfl

theorem actual_table_declared : lut ∈ FP4Original.module.globals := by
  decide +kernel

private theorem byte_table : ∀ i : Fin 8,
    lut.bytes[4*i.val+3]'(by have := i.isLt; change 4*i.val+3 < 32; omega) ++
    lut.bytes[4*i.val+2]'(by have := i.isLt; change 4*i.val+2 < 32; omega) ++
    lut.bytes[4*i.val+1]'(by have := i.isLt; change 4*i.val+1 < 32; omega) ++
    lut.bytes[4*i.val]'(by have := i.isLt; change 4*i.val < 32; omega) =
    BitVec.ofNat 32 (FP4Sign.table i) := by decide +kernel

theorem exact_initialized_load (L : Launch) (m : Mem)
    (ready : FP4Original.module.GlobalsReady L m) (i : Fin 8) :
    rd32 m (L.shared lut.name + BitVec.ofNat 64 (4*i.val)) =
      BitVec.ofNat 32 (FP4Sign.table i) := by
  have init := (ready.1 lut actual_table_declared).2.2.2.2
  rw [GlobalVar.Initialized.read32 init (4*i.val) (by have := i.isLt; change 4*i.val+4 ≤ 32; omega)]
  exact byte_table i

/-- Actual initialized table bits are preserved along every execution whose
real pending writes exclude this table. Write exclusion remains a required
kernel obligation, rather than a write-protection assumption in the model. -/
theorem exact_reachable_load (K : Kernel) (L : Launch) (initial c : Warp.State)
    (ready : FP4Original.module.GlobalsReady L initial.cfg.mem)
    (noWrite : ∀ d, Warp.Reach K L initial d → ∀ t ∈ L.threads, ∀ a,
      Warp.pending K L d t = some a → a.sp = .global → a.kind ≠ .read →
      ∀ x, covers (L.shared lut.name) 32 x → ¬ covers a.a a.sz.bytes x)
    (hc : Warp.Reach K L initial c) (i : Fin 8) :
    rd32 c.cfg.mem (L.shared lut.name + BitVec.ofNat 64 (4*i.val)) =
      BitVec.ofNat 32 (FP4Sign.table i) := by
  have frame := Warp.reach_global_frame K L initial (covers (L.shared lut.name) 32) noWrite hc
  have init := (ready.1 lut actual_table_declared).2.2.2.2
  have preserved : lut.Initialized (L.shared lut.name) c.cfg.mem := by
    intro j hj
    have hj' : j < 32 := hj
    rw [frame _ (by simp only [covers, add_sub_left, BitVec.toNat_ofNat];
                    rw [Nat.mod_eq_of_lt (by omega)]; exact hj')]
    exact init j hj
  rw [GlobalVar.Initialized.read32 preserved (4*i.val) (by have := i.isLt; change 4*i.val+4 ≤ 32; omega)]
  exact byte_table i

theorem actual_table_sign (L : Launch) (m : Mem)
    (ready : FP4Original.module.GlobalsReady L m) (i : Fin 8) (negative : Bool) :
    Fp.fmul .f32 .rn true false
      (rd32 m (L.shared lut.name + BitVec.ofNat 64 (4*i.val))).toNat
      (FP4Sign.originalSign negative) = some (FP4Sign.inserted i negative) := by
  rw [exact_initialized_load L m ready i]
  have small : FP4Sign.table i < 2^32 := by revert i; decide +kernel
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  exact FP4Sign.table_sign i negative

/-- Allocation and natural alignment of every actual LUT read follow from
module readiness; initialized values alone do not license an out-of-bounds load. -/
theorem exact_table_access (L : Launch) (m : Mem)
    (ready : FP4Original.module.GlobalsReady L m) (i : Fin 8) :
    accessOk L.alloc (L.shared lut.name + BitVec.ofNat 64 (4*i.val)) .b4 = true := by
  obtain ⟨_, align, bound, ⟨region, hr, hbase, hsize⟩, _⟩ := ready.1 lut actual_table_declared
  have fits : Fits (L.shared lut.name) 8 := bound
  have halign : (L.shared lut.name).toNat % 4 = 0 := align
  simp only [accessOk, Size.bytes_b4, Bool.and_eq_true, beq_iff_eq]
  refine ⟨aligned_elem fits i.isLt halign, List.any_eq_true.mpr ⟨region, hr, ?_⟩⟩
  have heq : region = ⟨L.shared lut.name, 32⟩ := by cases region; simp_all [lut]
  rw [heq]
  exact holds_elem fits i.isLt

abbrev originalEntry := FP4Original.«_Z20kDequantizeBlockwiseIfLi512ELi64ELi8ELi1EEvPfPhS0_PT_ii»
abbrev editedEntry := FP4Edited.«_Z20kDequantizeBlockwiseIfLi512ELi64ELi8ELi1EEvPfPhS0_PT_ii»

theorem original_load_statement : originalEntry.body[203]? =
    some ⟨none, .ld .global .f32 "%f22" (.reg "%rd29" 0)⟩ := by decide +kernel

theorem edited_load_statement : editedEntry.body[202]? =
    some ⟨none, .ld .global .f32 "%f22" (.reg "%rd29" 0)⟩ := by decide +kernel

/-- Cut-point rule for the actual first table load in either frozen entry,
with its actual destination register and instruction. Reachability of this
cut point/address invariant from entry PC0 remains a whole-proof obligation. -/
theorem actual_load_step (K : Kernel) (L : Launch) (c : Warp.State) (t : Tid)
    (ready : FP4Original.module.GlobalsReady L c.cfg.mem) (i : Fin 8)
    (statement : K.body[(c.cfg.ts t).pc]? =
      some ⟨none, .ld .global .f32 "%f22" (.reg "%rd29" 0)⟩)
    (address : (c.cfg.ts t).r "%rd29" = L.shared lut.name + BitVec.ofNat 64 (4*i.val)) :
    Warp.res K L c t = .ok ((c.cfg.ts t).set "%f22"
      (ext32 (BitVec.ofNat 32 (FP4Sign.table i)))) (c.cfg.heap t.ctaid) := by
  have act : Warp.action K (L.ctx t) (c.cfg.ts t) =
      .load .global (L.shared lut.name + BitVec.ofNat 64 (4*i.val)) .b4
        (fun v => (c.cfg.ts t).set "%f22" v) := by
    simp [Warp.action, Ptx.action, statement, guardHolds, exec, dataAddr, address, Ty.size, Ty.width]
  have nc : Warp.atNC K (c.cfg.ts t) = false := by simp [Warp.atNC, statement, guardHolds]
  unfold Warp.res
  dsimp only
  rw [act]
  simp only [Launch.allocs_global, exact_table_access L c.cfg.mem ready i, ↓reduceIte, nc, Bool.and_false,
    Bool.false_eq_true]
  change TRes.ok ((c.cfg.ts t).set "%f22"
    (ext32 (rd32 c.cfg.mem (L.shared lut.name + BitVec.ofNat 64 (4*i.val))))) _ = _
  rw [exact_initialized_load L c.cfg.mem ready i]

theorem original_first_table_step (L : Launch) (c : Warp.State) (t : Tid)
    (ready : FP4Original.module.GlobalsReady L c.cfg.mem) (i : Fin 8)
    (pc : (c.cfg.ts t).pc = 203)
    (address : (c.cfg.ts t).r "%rd29" = L.shared lut.name + BitVec.ofNat 64 (4*i.val)) :
    Warp.res originalEntry L c t = .ok ((c.cfg.ts t).set "%f22"
      (ext32 (BitVec.ofNat 32 (FP4Sign.table i)))) (c.cfg.heap t.ctaid) :=
  actual_load_step originalEntry L c t ready i (by rw [pc]; exact original_load_statement) address

theorem edited_first_table_step (L : Launch) (c : Warp.State) (t : Tid)
    (ready : FP4Original.module.GlobalsReady L c.cfg.mem) (i : Fin 8)
    (pc : (c.cfg.ts t).pc = 202)
    (address : (c.cfg.ts t).r "%rd29" = L.shared lut.name + BitVec.ofNat 64 (4*i.val)) :
    Warp.res editedEntry L c t = .ok ((c.cfg.ts t).set "%f22"
      (ext32 (BitVec.ofNat 32 (FP4Sign.table i)))) (c.cfg.heap t.ctaid) :=
  actual_load_step editedEntry L c t ready i (by rw [pc]; exact edited_load_statement) address

#print axioms exact_table_access
#print axioms original_first_table_step
#print axioms edited_first_table_step

#print axioms exact_globals_identical
#print axioms exact_initialized_load
#print axioms exact_reachable_load
#print axioms actual_table_sign
end FP4Whole
