#!/usr/bin/env python3
"""Regenerate Projects/rmk/Deframer/UnparkSiteSegs.lean (the session's unpark call site and the
jump back to the loop head) with tools/gen_seg.py. Usage: python3 tools/gen_seg_unparksite.py"""
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
import gen_seg as G

facts = G.load_facts(Path(__file__).resolve().parents[1] / 'Projects/rmk/Deframer/UnparkSiteFetch.lean')
G.BASE = 'e'
print(G.emit(facts, 'sunpk', '(e : Core) (M : Word → BitVec 8)', '(hpc : e.pc = 0x80003fd8) (hq : Quiet e)',
             0x80003fd8, 0x8001d3f2, {0x80003fd8: {'al': 'HYP', 'in': 'HYP'}, 0x80003fec: {'target': 0x8001d3f2}},
             {}, ram0='M', prefix='su'))
print(G.emit(facts, 'sback', '(e : Core) (M : Word → BitVec 8)', '(hpc : e.pc = 0x80003ff0) (hq : Quiet e)',
             0x80003ff0, 0x80003e1a, {}, {}, ram0='M', prefix='sb'))
