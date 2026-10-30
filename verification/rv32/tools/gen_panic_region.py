#!/usr/bin/env python3
"""Regenerate the step-closure proof of Projects/rmk/PanicRegion.lean from the kernel-checked
facts in Projects/rmk/PanicFetch.lean. Usage: python3 tools/gen_panic_region.py (prints Lean)."""
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
import gen_seg as G

facts = G.load_facts(Path(__file__).resolve().parents[1] / 'Projects/rmk/PanicFetch.lean')
pcs = sorted(facts)
J = {}
for pc in pcs:
    f = G.parse(facts[pc][0])
    if f[0] == 'auipc':
        nxt = pc + facts[pc][1]
        imm = int(f[2].split('#')[0], 16)
        assert G.parse(facts[nxt][0])[0] == 'jalr', hex(pc)
        J[nxt] = (pc + imm) & 0xffffffff
S = [pc for pc in pcs if pc not in J]
out = []
out.append("/-- The region's pcs other than the five `jalr` calls. -/")
out.append("def panicS : List Word := [" + ", ".join(f"0x{p:x}" for p in S) + "]")
out.append("/-- The five calls, each with the return-address value its `auipc` set. -/")
out.append("def panicJ : List (Word × Word) := [" + ", ".join(f"(0x{p:x}, 0x{r:x})" for p, r in J.items()) + "]")
out.append("""
/-- Inside the panic path: at one of its pcs, or at one of its calls with ra as its `auipc` set. -/
def PanicRg (m : Machine) : Prop :=
  m.core.pc ∈ panicS ∨ ∃ q ∈ panicJ, m.core.pc = q.1 ∧ m.core.get 1 = q.2

theorem rg_step (m m₁ : Machine) (h : PanicRg m) (hd : DetStep B img m m₁) : PanicRg m₁ := by
  rcases h with hS | ⟨q, hq, hpc, hra⟩
  · simp only [panicS, List.mem_cons, List.not_mem_nil, or_false] at hS
    rcases hS with """ + " | ".join("h" for _ in S))
for pc in S:
    f = G.parse(facts[pc][0]); k = f[0]
    pre = f"(by rw [h]; decide) (by rw [h]; exact f{pc:x}) hd"
    if k in ('op', 'opimm', 'lui', 'store'):
        out.append(f"    · have e := PanicPc.pc_{k} {pre}; left; rw [e, h]; decide")
    elif k == 'auipc':
        j = pc + facts[pc][1]
        out.append(f"    · obtain ⟨e1, e2⟩ := PanicPc.pc_auipc {pre}; right")
        out.append(f"      exact ⟨(0x{j:x}, 0x{J[j]:x}), by decide, by rw [e1, h]; decide, by rw [e2, h]; decide⟩")
    elif k == 'branch':
        out.append(f"    · rcases PanicPc.pc_branch {pre} with e | e <;> (left; rw [e, h]; decide)")
    elif k == 'jal':
        out.append(f"    · have e := PanicPc.pc_jal {pre}; left; rw [e, h]; decide")
    else:
        raise SystemExit(f'kind {k} at {pc:x}')
out.append("  · simp only [panicJ, List.mem_cons, List.not_mem_nil, or_false] at hq")
out.append("    rcases hq with " + " | ".join("rfl" for _ in J))
for pc in J:
    out.append(f"    · have e := PanicPc.pc_jalr (by rw [hpc]; decide) (by rw [hpc]; exact f{pc:x}) hd; left; rw [e, hra]; decide")
print("\n".join(out))
