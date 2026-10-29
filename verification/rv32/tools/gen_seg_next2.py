#!/usr/bin/env python3
"""Regenerate the straight-line segments of Projects/rmk/Deframer/NextSegs.lean with
tools/gen_seg.py. Every branch outcome and memory side condition that depends on the loop
invariant is a hypothesis of its segment (HYP), discharged where the segments are composed.
Usage: python3 tools/gen_seg_next2.py  (prints Lean to stdout)."""
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
import gen_seg as G

facts = G.load_facts(Path(__file__).resolve().parents[1] / 'Projects/rmk/Deframer/NextFetch.lean')
H = 'HYP'
MEM = {'al': H, 'in': H}
G.FIRST_HPC = True


def seg(name, base, start, stop, specs, ram='M', prefix=None):
    G.BASE = base
    print(G.emit(facts, name, f'({base} : Core) ({ram} : Word → BitVec 8)',
                 f'(hpc : {base}.pc = 0x{start:x}) (hq : Quiet {base})', start, stop, specs, {},
                 ram0=ram, prefix=prefix or name[:2]))


T, F = {'taken': True, 'why': H}, {'taken': False, 'why': H}
# loop head, cursor < filled: to the scan loop
seg('nhead', 'd', 0x8001d476, 0x8001d486, {0x8001d476: F})
# loop head, cursor = filled: to the exit test
seg('nend', 'd', 0x8001d476, 0x8001d4f8, {0x8001d476: T})
# a delimiter found while discarding: consumed := z + 1, discarding := 0, back to the loop head
seg('ndisc', 'e', 0x8001d49a, 0x8001d476, {0x8001d4a4: MEM, 0x8001d4a8: F, 0x8001d4ac: MEM, 0x8001d4d8: T})
# a delimiter found, not discarding: consumed := z + 1, bounds checks, call the wrapper
seg('ncall', 'e', 0x8001d49a, 0x8001e006, {0x8001d4a4: MEM, 0x8001d4a8: T, 0x8001d4b2: F, 0x8001d4b6: F,
                                            0x8001d4c4: {'target': 0x8001e006}})
# after the wrapper: error, short frame, or Some
seg('nerr', 'e', 0x8001d4c8, 0x8001d476, {0x8001d4c8: MEM, 0x8001d4ca: T, 0x8001d4d8: T})
seg('nshort', 'e', 0x8001d4c8, 0x8001d476, {0x8001d4c8: MEM, 0x8001d4ca: F, 0x8001d4ce: MEM, 0x8001d4d0: F,
                                             0x8001d4d8: T})
seg('nsome', 'e', 0x8001d4c8, 0x8001d530, {0x8001d4c8: MEM, 0x8001d4ca: F, 0x8001d4ce: MEM, 0x8001d4d0: T})
# Some, frame already at the front
seg('nfront', 'e', 0x8001d530, 0x8001d510, {0x8001d530: T})
# Some, frame moved: range check, then memmove
seg('nmove1', 'e', 0x8001d530, 0x8001ad76, {0x8001d530: F, 0x8001d546: {'target': 0x8001ad76}}, prefix='nv')
seg('nmove2', 'e', 0x8001ad76, 0x80020c1e, {0x8001ad76: F, 0x8001ad7a: F, 0x8001ad7e: {'ra': H},
                                             0x8001d558: {'target': 0x80020c1e}}, prefix='nw')
seg('nmoved', 'e', 0x8001d55c, 0x8001d510, {})
# the exit test at 0x8001d4f8
seg('nx1', 'e', 0x8001d4f8, 0x8001d510, {0x8001d4fc: T, 0x8001d508: MEM, 0x8001d50c: MEM})
seg('nx2', 'e', 0x8001d4f8, 0x8001d510, {0x8001d4fc: F, 0x8001d4fe: T})
seg('nx3', 'e', 0x8001d4f8, 0x8001d510, {0x8001d4fc: F, 0x8001d4fe: F, 0x8001d502: T})
seg('nx4', 'e', 0x8001d4f8, 0x8001d510, {0x8001d4fc: F, 0x8001d4fe: F, 0x8001d502: F,
                                         0x8001d508: MEM, 0x8001d50c: MEM})
# the epilogue
seg('nepi', 'e', 0x8001d510, None, {**{pc: MEM for pc in range(0x8001d512, 0x8001d52c, 2)},
                                          0x8001d52e: {'ra': H}})
