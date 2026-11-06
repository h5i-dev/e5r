#!/usr/bin/env python3
"""Exploratory bounded-byte widening in the full pinned generated PTX."""
import argparse
import json
import pathlib
import re

ap = argparse.ArgumentParser()
ap.add_argument('original', type=pathlib.Path)
ap.add_argument('edited', type=pathlib.Path)
opts = ap.parse_args()
text = opts.original.read_text()
name = '_Z21dequantize_block_q4_KIfEvPKvPT_'
start = text.index('.entry ' + name)
end = text.index('\n}', start) + 2
body = text[start:end]
pairs = []
for shift in re.finditer(r'shr\.u16\s+(%rs\d+),\s*(%rs\d+), 4;', body):
    dest, source = shift.groups()
    convert = re.search(r'cvt\.rn\.f32\.u16\s+(%f\d+),\s*' + re.escape(dest) + ';',
                        body[shift.end():])
    if convert:
        # The target source register must be zero extended from an unsigned byte.
        zero_extend = re.search(r'cvt\.u16\.u8\s+' + re.escape(source) + r',\s*(%rs\d+);', body)
        assert zero_extend
        assert re.search(r'ld\.global(?:\.nc)?\.u8\s+' + re.escape(zero_extend[1]) + r',', body)
        pairs.append((shift.group(), convert.group(), source, convert[1]))
assert len(pairs) == 4
for i, (shift, convert, source, dest) in enumerate(pairs):
    body = body.replace(shift, f'cvt.u32.u16 %wide{i}, {source};\n\tshr.u32 %wide{i}, %wide{i}, 4;')
    body = body.replace(convert, f'cvt.rn.f32.u32 {dest}, %wide{i};')
body = body.replace('{\n', '{\n\t.reg .b32 %wide<4>;\n', 1)
opts.edited.write_text(text[:start] + body + text[end:])
opts.edited.with_suffix('.edit.json').write_text(json.dumps({'entry': name, 'pairs': pairs}, indent=2) + '\n')
