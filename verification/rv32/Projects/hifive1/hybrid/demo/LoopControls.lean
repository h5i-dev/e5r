/-
  Negative controls for the loop demo, as kernel-checked refutations: each
  states that a weakened or false variant of a summary obligation is false
  on this binary, so the corresponding proof could not have succeeded.

  Original e5r code, Apache-2.0.

  * `false_post`: the summary cannot promise a head below 3 (it can reach 3).
  * `weak_pre`: with the precondition weakened to head <= 4, the real run
    stores 5, so the postcondition head < 4 fails: the bound is a genuine
    precondition, discharged at every delegated node by the checker's state.
  * `irq_needs_mask`: if MIE were not part of the precondition, an
    interrupt could arrive inside the region at a machine no certificate
    node describes, so the checker theorem's interrupt obligation
    (`Region.irq`: `MainInv`) would be false; masking is what discharges it.
  * `interior_not_delegated_exit`: the region's interior pcs are not
    certificate nodes at all, so nothing but the summary covers them.
-/
import Projects.hifive1.hybrid.demo.LoopProof

set_option maxRecDepth 100000

namespace E5R.HybridLoop.Controls
open E5R E5R.AI E5R.Hybrid E5R.HybridLoop.Job E5R.HybridLoop.Proof

/-- A concrete machine at the region entry with head `h`. -/
def atEntry (h : Word) (mie : Bool) : Machine :=
  ⟨{ pc := 0x20010018, x := fun r => if r.val = 12 then h else if r.val = 10 then 0x80000000 else 0,
     mie_ := mie, mpie := false, mpp := 0, mieReg := 0x80, mtvec := 0x20010000, mepc := 0,
     mcause := 0, mscratch := 0, resv := false }, fun _ => 0⟩

theorem atEntry_pre (h : Word) (hh : h.toNat < 4) : Pre (atEntry h false) := by
  have e12 : (atEntry h false).core.get 12 = h := rfl
  have e10 : (atEntry h false).core.get 10 = 0x80000000 := rfl
  exact ⟨rfl, by rw [e12]; exact hh, rfl, by rw [e10]; decide, by rw [e10]; decide⟩

/-- The summary cannot promise a head below 3. -/
theorem false_post : ¬ ∀ m₀ m, Pre m₀ → Spec m₀ m → (m.core.get 12).toNat < 3 := by
  intro h
  obtain ⟨m, -, sp⟩ := contract (atEntry 2 false) (atEntry_pre 2 (by decide))
  have := h _ _ (atEntry_pre 2 (by decide)) sp
  rw [sp.head] at this
  have e : (atEntry 2 false).core.get 12 = 2 := rfl
  rw [e] at this; revert this; decide

/-- Six steps of the real binary from a concrete machine (any oracle: the
    region has no environment choices). -/
def run6 (m : Machine) : Option Machine :=
  (List.range 6).foldlM (fun m _ => match stepInstr B img m (fun _ => 0) with
    | .ok c ram _ => some ⟨c, ram⟩ | .fault _ => none) m

/-- With head 4 the region stores 5: a precondition weakened to head <= 4
    would make the postcondition `head < 4` false. -/
theorem weak_pre : (run6 (atEntry 4 false)).map (fun m => ramRead m.ram 0x80000000 .w) = some 5 := by
  decide +kernel

/-- Without masking, an interrupt is enabled inside the region at a machine
    no certificate node describes. -/
theorem irq_needs_mask :
    irqEnabled (atEntry 2 true).core 7 = true ∧
    ∀ m : Machine, m.core.pc = 0x2001001a → ¬ MainInv Cert.cert m := by
  refine ⟨by decide, fun m hpc ⟨j, n, hn, _, hs⟩ => ?_⟩
  have hall : ∀ n ∈ Cert.cert.nodes, n.s.pc ≠ 0x2001001a := by decide +kernel
  have := hall n (List.mem_of_getElem? hn)
  have hp := hs.pc
  rw [hpc] at hp
  apply this
  have hlt : n.s.pc < 2^32 := by
    have : ∀ n ∈ Cert.cert.nodes, n.s.pc < 2^32 := by decide +kernel
    exact this n (List.mem_of_getElem? hn)
  have := congrArg BitVec.toNat hp
  simp [w] at this; omega

/-- Every interior pc of the region is absent from the certificate. -/
theorem interior_not_delegated_exit :
    ∀ n ∈ Cert.cert.nodes, n.s.pc ∉ [0x2001001a, 0x2001001e, 0x20010022, 0x20010024, 0x20010026] := by
  decide +kernel

end E5R.HybridLoop.Controls
