#!/usr/bin/env python3
"""Regenerate Projects/rmk/Deframer/FromDecodedSeg.lean (RynkMessage::from_decoded, 0x8001c3c6,
the non-panicking path) with tools/gen_seg.py. Usage: python3 tools/gen_seg_fromdecoded.py"""
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
import gen_seg as G

facts = G.load_facts(Path(__file__).resolve().parents[1] / 'Projects/rmk/Deframer/FromDecodedFetch.lean')
H = 'HYP'
MEM = {'al': H, 'in': H}
G.BASE = 'e'
print(G.emit(facts, 'sfrom', '(e : Core) (M : Word → BitVec 8)', '(hpc : e.pc = 0x8001c3c6) (hq : Quiet e)',
             0x8001c3c6, None, {0x8001c3c8: {'taken': False, 'why': H}, 0x8001c3cc: MEM, 0x8001c3d0: MEM,
                                0x8001c3d4: MEM, 0x8001c3dc: MEM, 0x8001c3de: MEM, 0x8001c3e0: MEM,
                                0x8001c3e4: MEM, 0x8001c3e8: MEM, 0x8001c3ea: {'ra': H}}, {}, ram0='M', prefix='fd'))
