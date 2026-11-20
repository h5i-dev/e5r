#!/usr/bin/env python3
"""Regenerate Projects/rmk/Deframer/RxSegs.lean (the UART receive poll's straight-line segments
between its two device reads, and assert_offset) with tools/gen_seg.py.
Usage: python3 tools/gen_seg_rx.py"""
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
import gen_seg as G

facts = G.load_facts(Path(__file__).resolve().parents[1] / 'Projects/rmk/Deframer/RxFetch.lean')
H = 'HYP'
MEM = {'al': H, 'in': H}
T, F = {'taken': True, 'why': H}, {'taken': False, 'why': H}


def seg(name, start, stop, specs, prefix):
    G.BASE = 'e'
    print(G.emit(facts, name, '(e : Core) (M : Word → BitVec 8)', f'(hpc : e.pc = 0x{start:x}) (hq : Quiet e)',
                 start, stop, specs, {}, ram0='M', prefix=prefix))


seg('rxA', 0x80004374, 0x8001692e, {0x8000437c: {'target': 0x8001692e}}, 'ra')
seg('aoff', 0x8001692e, None, {0x80016934: MEM, 0x80016938: F, 0x8001693e: {'ra': H}}, 'ao')
seg('rxNo', 0x80004384, 0x800043a8, {0x80004386: T}, 'rn')
seg('rxB', 0x80004384, 0x8001692e, {0x80004386: F, 0x80004394: {'target': 0x8001692e}}, 'rb')
seg('rxLoop', 0x8000439c, 0x80004374, {0x8000439e: MEM, 0x800043a2: T}, 'rl')
seg('rxEnd', 0x8000439c, 0x800043a8, {0x8000439e: MEM, 0x800043a2: F}, 're')
