#!/usr/bin/env python3
"""Regenerate the straight-line segments of Projects/rmk/Deframer/SessionSegs.lean (the Rynk
session receive step) with tools/gen_seg.py from Projects/rmk/Deframer/SessionFetch.lean.
Usage: python3 tools/gen_seg_session.py  (prints Lean to stdout)."""
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
import gen_seg as G

facts = G.load_facts(Path(__file__).resolve().parents[1] / 'Projects/rmk/Deframer/SessionFetch.lean')
H = 'HYP'
MEM = {'al': H, 'in': H}
T, F = {'taken': True, 'why': H}, {'taken': False, 'why': H}


def seg(name, start, stop, specs, prefix):
    G.BASE = 'e'
    print(G.emit(facts, name, '(e : Core) (M : Word → BitVec 8)', f'(hpc : e.pc = 0x{start:x}) (hq : Quiet e)',
                 start, stop, specs, {}, ram0='M', prefix=prefix))


seg('scall', 0x80003e1a, 0x8001d43a, {0x80003e32: {'target': 0x8001d43a}}, 'sa')
seg('snone', 0x80003e36, 0x8001d576, {0x80003e38: T, 0x80003f58: MEM, 0x80003f5c: MEM, 0x80003f60: MEM,
                                      0x80003f64: MEM, 0x80003f74: {'target': 0x8001d576}}, 'sn')
seg('ssome', 0x80003e36, 0x8001d388, {0x80003e38: F, 0x80003e4a: {'target': 0x8001d388}}, 'ss')
seg('sdec', 0x80003e4e, 0x8001c3c6, {0x80003e56: MEM, 0x80003e5a: F, 0x80003e6c: {'target': 0x8001c3c6}}, 'sd')
seg('stail', 0x80003f78, 0x80003f7c, {}, 'st')
