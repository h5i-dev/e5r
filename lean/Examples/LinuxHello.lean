import Examples.Hello
import NoCompiler.Linux.Process

/-
`hello` (Examples/Hello.lean) as a whole process under the Linux layer
(NoCompiler/Linux/Process.lean): from any kernel state, the process runs
safely until it leaves `hello`'s code or exits, and ends as `helloSpec` says.

The proof is the existing `hello_verified`, widened from `helloSpec`'s
permission to all of memory (`Reach.widen`; this needs sp ≥ 16 so that the
16-byte stack frame does not wrap past 2^64), then carried to the process by
`PReach.of_reach`. Nothing about `hello`'s code is proved again.
-/
namespace Examples.LinuxHello
open NoCompiler NoCompiler.Linux Examples.Hello Examples.Hello.Image

theorem perm_le (s : State) (hsp : 16 ≤ (s.reg Reg.sp).toNat) : (helloSpec.perm () s).le Perm.top := by
  apply Perm.le_of
  · intro r hr
    simp only [Spec.perm, helloSpec, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨⟨0, 2 ^ 64⟩, by simp [Perm.top], Region.within_top (by decide)⟩
  · intro r hr
    simp only [Spec.perm, helloSpec, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    refine ⟨⟨0, 2 ^ 64⟩, by simp [Perm.top], Region.within_top ?_⟩
    simp only [Spec.stackRegion, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega

/-- `hello`, run as a process from any kernel state `k`, is safe until it leaves
    its code or exits, and ends as `helloSpec` says. -/
theorem hello_process (s : State) (k : Kern) (he : Entry hello_dom hello_entry s) (hp : helloSpec.pre () s)
    (hsp : 16 ≤ (s.reg Reg.sp).toNat) :
    PReach code hello_dom (fun t => Final hello_dom t ∧ helloSpec.Done () s t) (s, k) :=
  PReach.of_reach (Reach.widen (perm_le s hsp) (hello_verified () s he hp)) k

end Examples.LinuxHello
