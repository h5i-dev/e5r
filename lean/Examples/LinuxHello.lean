import Examples.Hello
import NoCompiler.Linux.Process

/-
`hello` (Examples/Hello.lean) as a whole process under the Linux layer
(NoCompiler/Linux/Process.lean): from a kernel state that maps its data
and stack, the process runs safely until it leaves `hello`'s code or exits, and ends as `helloSpec` says.

The proof is the existing `hello_verified`, widened from `helloSpec`'s
permission to the process's mapped ranges (`Reach.widen`; the kernel state
must map hello's read-only data readable and its stack frame writable), then carried to the
process by `PReach.of_reach`. Nothing about `hello`'s code is proved again.
-/
namespace Examples.LinuxHello
open NoCompiler NoCompiler.Linux Examples.Hello Examples.Hello.Image

theorem perm_le (s : State) (k : Kern)
    (hro : ∃ r ∈ k.perm.rd ++ k.perm.wr, seg_rodata.region.within r)
    (hst : ∃ r ∈ k.perm.wr, (Spec.stackRegion s 16).within r) : (helloSpec.perm () s).le k.perm := by
  apply Perm.le_of
  · intro r hr
    simp only [Spec.perm, helloSpec, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact hro
  · intro r hr
    simp only [Spec.perm, helloSpec, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact hst

/-- `hello`, run as a process whose kernel maps its read-only data readable
    (read-only or read-write) and its 16-byte stack frame writable, is safe until it leaves its code or exits, and ends as
    `helloSpec` says. -/
theorem hello_process (s : State) (k : Kern) (he : Entry hello_dom hello_entry s) (hp : helloSpec.pre () s)
    (hro : ∃ r ∈ k.perm.rd ++ k.perm.wr, seg_rodata.region.within r)
    (hst : ∃ r ∈ k.perm.wr, (Spec.stackRegion s 16).within r) :
    PReach code hello_dom (fun t => Final hello_dom t ∧ helloSpec.Done () s t) (s, k) :=
  PReach.of_reach_le (perm_le s k hro hst) (hello_verified () s he hp)

/-- The same, stated on the mapped ranges, for a kernel with no protection
    overlays (every mapped range read-write; `Kern.perm_plain`). -/
theorem hello_process_plain (s : State) (k : Kern) (he : Entry hello_dom hello_entry s)
    (hp : helloSpec.pre () s) (h0 : k.ro = []) (h1 : k.noacc = [])
    (hro : ∃ q ∈ k.maps, seg_rodata.region.within ⟨q.1, q.2⟩)
    (hst : ∃ q ∈ k.maps, (Spec.stackRegion s 16).within ⟨q.1, q.2⟩) :
    PReach code hello_dom (fun t => Final hello_dom t ∧ helloSpec.Done () s t) (s, k) := by
  refine hello_process s k he hp ?_ ?_ <;> rw [Kern.perm_plain k h0 h1]
  · obtain ⟨q, hq, hw⟩ := hro
    exact ⟨⟨q.1, q.2⟩, by simp only [List.nil_append, List.mem_map]; exact ⟨q, hq, rfl⟩, hw⟩
  · obtain ⟨q, hq, hw⟩ := hst
    exact ⟨⟨q.1, q.2⟩, by simp only [List.mem_map]; exact ⟨q, hq, rfl⟩, hw⟩

/-- Control: a process with nothing mapped cannot even read hello's data: the
    permission is empty. -/
example : (Kern.init).perm.wr = [] := by decide

end Examples.LinuxHello
