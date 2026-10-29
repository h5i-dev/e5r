#!/usr/bin/env python3
"""Regenerate the straight-line segments of Projects/rmk/Deframer/NextParts.lean (`nsaves`,
`nentry`) with tools/gen_seg.py from the kernel-checked facts in Projects/rmk/Deframer/NextFetch.lean.
Usage: python3 tools/gen_seg_next.py  (prints Lean to stdout)."""
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
import gen_seg as G

facts = G.load_facts(Path(__file__).resolve().parents[1] / 'Projects/rmk/Deframer/NextFetch.lean')

# frame and saves
AL = "simp only [alu_add]; bv_omega"
IN = "rw [B_ram]; simp only [alu_add]; constructor <;> bv_omega"
G.BASE = 'c'
print(G.emit(facts, 'nsaves', '(c : Core) (ram : Word → BitVec 8)',
  '(hpc : c.pc = 0x8001d43a) (hq : Quiet c) (hsp : (c.get 2).toNat % 4 = 0)\n'
  '    (hs : 0x80029bc8 + 0x40 ≤ (c.get 2).toNat ∧ (c.get 2).toNat ≤ 0x81000000)',
  0x8001d43a, 0x8001d456, {pc: {'al': AL, 'in': IN} for pc in range(0x8001d43c, 0x8001d456, 2)}, {},
  prefix='k'))

# entry checks
W = {'al': "bv_omega", 'in': "rw [B_ram]; constructor <;> bv_omega"}
NT = "simp only [taken, BitVec.ult, decide_eq_false_iff_not]; omega"
G.BASE = 'd'
print(G.emit(facts, 'nentry', '(d : Core) (R : Word → BitVec 8)',
  '(hpc : d.pc = 0x8001d456) (hq : Quiet d) (hal : (d.get 10).toNat % 4 = 0)\n'
  '    (hp : 0x80029bc8 ≤ (d.get 10).toNat ∧ (d.get 10).toNat + 12 ≤ 0x81000000)\n'
  '    (hle : (ramRead R (d.get 10 + 0x4#32) .w).toNat ≤ (d.get 12).toNat)\n'
  '    (hcf : (ramRead R (d.get 10) .w).toNat ≤ (ramRead R (d.get 10 + 0x4#32) .w).toNat)',
  0x8001d456, 0x8001d476,
  {0x8001d458: W, 0x8001d45a: W, 0x8001d45c: {'taken': False, 'why': NT},
   0x8001d460: {'taken': False, 'why': NT},
   0x8001d468: {'al': "omega", 'in': "rw [B_ram]; constructor <;> bv_omega"}}, {}, ram0='R', prefix='j'))
