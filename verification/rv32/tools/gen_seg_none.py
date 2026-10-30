#!/usr/bin/env python3
"""Regenerate Projects/rmk/Deframer/NoneSegs.lean (the session's None path around the UART receive
poll) with tools/gen_seg.py. Usage: python3 tools/gen_seg_none.py"""
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
import gen_seg as G

facts = G.load_facts(Path(__file__).resolve().parents[1] / 'Projects/rmk/Deframer/NoneFetch.lean')
H = 'HYP'
MEM = {'al': H, 'in': H}
T, F = {'taken': True, 'why': H}, {'taken': False, 'why': H}
STORES = {pc: MEM for pc in (0x80003f84, 0x80003f88, 0x80003f8c, 0x80003f90, 0x80003f94, 0x80003f98, 0x80003f9c)}


def seg(name, start, stop, specs, prefix):
    G.BASE = 'e'
    print(G.emit(facts, name, '(e : Core) (M : Word → BitVec 8)', f'(hpc : e.pc = 0x{start:x}) (hq : Quiet e)',
                 start, stop, specs, {}, ram0='M', prefix=prefix))


seg('nDisc', 0x80003f7c, 0x80003ff2, {0x80003f7c: T}, 'nd')
seg('nNoP', 0x80003f7c, 0x80003ff2, {0x80003f7c: F, 0x80003f80: T}, 'np')
seg('nFull', 0x80003f7c, 0x80004428, {0x80003f7c: F, 0x80003f80: F, **STORES, 0x80003fa0: F}, 'nf')
seg('nGo1', 0x80003f7c, 0x8000434c, {0x80003f7c: F, 0x80003f80: F, **STORES, 0x80003fa0: T}, 'ng')
seg('nGo2', 0x8000434c, 0x80004374, {0x8000434c: MEM, 0x8000435e: F, 0x80004362: MEM}, 'nh')
seg('nZero', 0x800043a8, 0x80004428, {0x800043a8: T}, 'nz')
seg('nCommit', 0x800043a8, 0x80003e1a, {0x800043a8: F, 0x800043ac: MEM, 0x800043ae: MEM, 0x80003b98: MEM,
                                         0x80003b9e: MEM}, 'nc')
