#!/usr/bin/env python3
"""Emit the Lean boilerplate of a straight-line quiet run of the pinned memmove.

Original e5r code, Apache-2.0. Reads the instruction facts of MemmoveFetch.lean
and a path: start pc, then one decision per branch ('T' taken / 'N' not).
Prints, in the lazy style of MemmoveMisStart (each core written from the
previous core's registers, so every step is `rw [exec_*]; rfl`):

  * the cores `PFX1..PFXn` and RAMs (a new RAM after each store),
  * the obligations each step needs, as `have` lines whose proofs are left as
    `?_`-free placeholders named `HIN_i` (load/store in RAM), `HAL_i`
    (alignment, h/w only) and `HBR_i` (branch decision) -- they are
    printed as `(by OBLIGATION)` comments for the author to fill in,
  * the steps, the `sameCsr` chain and the run.

Usage: gen_path.py PFX START_PC N DECISIONS [CORE RAM]
"""
from pathlib import Path
import re
import sys

FETCH = Path(__file__).with_name('MemmoveFetch.lean')
facts = {}
for a, i in re.findall(r'theorem f(8002[0-9a-f]+) : fetchDecode img 0x[0-9a-f]+ = some \((.*)\) :=',
                       FETCH.read_text()):
    facts[int(a, 16)] = i


def parse(s):
    body, ln = s.rsplit(', ', 1)
    return body.split(' ', 1)[0].removeprefix('Instr.'), body, int(ln)


def imm(tok):
    v = int(tok.split('#')[0], 16)
    return v


def main():
    pfx, pc, n, dec = sys.argv[1], int(sys.argv[2], 16), int(sys.argv[3]), sys.argv[4]
    c0 = sys.argv[5] if len(sys.argv) > 5 else 'c'
    r0 = sys.argv[6] if len(sys.argv) > 6 else 'R'
    lets, steps, obls = [], [], []
    cur, ram, rams = c0, r0, 0
    di = 0
    cores = []
    for i in range(1, n + 1):
        kind, body, ln = parse(facts[pc])
        toks = body.replace('(', '').replace(')', '').split()
        nxt = pc + ln
        new = f'{pfx}{i}'
        nram = ram
        pcfact = (f'(by rw [hpc]; decide) (by rw [hpc]; exact f{pc:08x})' if cur == c0 else
                  f'(by show (0x{pc:08x} : Word).getLsbD 0 = false; decide) f{pc:08x}')
        tac = ''
        if kind in ('op', 'opimm'):
            op, rd, rs1, x = toks[1].split('.')[1], toks[2], toks[3], toks[4]
            arg = f'({cur}.get {x})' if kind == 'op' else x
            lets.append(f'  let {new} := {cur}.wr {rd} (alu .{op} ({cur}.get {rs1}) {arg}) 0x{nxt:08x}')
            tac = f'rw [exec_{kind}]; rfl'
        elif kind == 'load':
            w, sg, rd, rs1, off = toks[1].split('.')[1], toks[2], toks[3], toks[4], toks[5]
            addr = f'{cur}.get {rs1} + {off}'
            lets.append(f'  let {new} := {cur}.wr {rd} (extend .{w} {sg} (ramRead {ram} ({addr}) .{w})) 0x{nxt:08x}')
            al = '(by simp only [Width.bytes, Nat.mod_one])' if w == 'b' else f'HAL_{i}'
            obls.append(f'  have HIN_{i} : B.inRam ({addr}) {dict(b=1, h=2, w=4)[w]} = true := by OBLIGATION')
            if w != 'b':
                obls.append(f'  have HAL_{i} : ({addr}).toNat % {dict(h=2, w=4)[w]} = 0 := by OBLIGATION')
            tac = f'rw [exec_load, interp_load_ram (w := .{w}) o {al} HIN_{i}]; rfl'
        elif kind == 'store':
            w, rs1, rs2, off = toks[1].split('.')[1], toks[2], toks[3], toks[4]
            addr = f'{cur}.get {rs1} + {off}'
            rams += 1
            nram = f'{pfx}R{rams}'
            lets.append(f'  let {nram} := ramWrite {ram} ({addr}) ({cur}.get {rs2}) .{w}')
            lets.append(f'  let {new} := {cur}.goto 0x{nxt:08x}')
            al = '(by simp only [Width.bytes, Nat.mod_one])' if w == 'b' else f'HAL_{i}'
            obls.append(f'  have HIN_{i} : B.inRam ({addr}) {dict(b=1, h=2, w=4)[w]} = true := by OBLIGATION')
            if w != 'b':
                obls.append(f'  have HAL_{i} : ({addr}).toNat % {dict(h=2, w=4)[w]} = 0 := by OBLIGATION')
            tac = f'rw [exec_store, interp_store_ram (w := .{w}) o {al} HIN_{i}]; rfl'
        elif kind == 'branch':
            cond, rs1, rs2, off = toks[1].split('.')[1], toks[2], toks[3], imm(toks[4])
            t = dec[di]; di += 1
            tgt = (pc + off) % 2 ** 32
            obls.append(f'  have HBR_{i} : taken .{cond} ({cur}.get {rs1}) ({cur}.get {rs2}) = '
                        f'{"true" if t == "T" else "false"} := by OBLIGATION')
            if t == 'T':
                lets.append(f'  let {new} := {cur}.goto 0x{tgt:08x}')
                tac = (f'rw [exec_branch, HBR_{i}, if_pos rfl, show {cur}.pc + 0x{off:x}#32 = 0x{tgt:08x} by '
                       f'rw [show {cur}.pc = 0x{pc:08x} from rfl]; decide, jump_ok _ _ (by decide)]; rfl')
                nxt = tgt
            else:
                lets.append(f'  let {new} := {cur}.goto 0x{nxt:08x}')
                tac = f'rw [exec_branch, HBR_{i}]; rfl'
        elif kind == 'jal':
            rd, off = toks[1], imm(toks[2])
            assert rd == '0'
            tgt = (pc + off) % 2 ** 32
            lets.append(f'  let {new} := {cur}.goto 0x{tgt:08x}')
            tac = (f'rw [exec_jal, Core.set_zero, show {cur}.pc + 0x{off:x}#32 = 0x{tgt:08x} by '
                   f'rw [show {cur}.pc = 0x{pc:08x} from rfl]; decide, jump_ok _ _ (by decide)]; rfl')
            nxt = tgt
        else:
            raise SystemExit(f'unsupported {kind} at {pc:x}')
        if cur == c0:
            tac = tac.replace(f'rw [show {cur}.pc = 0x{pc:08x} from rfl]', 'rw [hpc]')
            if 'jump_ok' not in tac:
                tac = tac.replace(']; rfl', ', hpc]; rfl')
        steps.append(f'  have {pfx}s{i} : DetStep B img ⟨{cur}, {ram}⟩ ⟨{new}, {nram}⟩ := by\n'
                     f'    refine detStep_of {pcfact} fun o => ?_\n    {tac}')
        cores.append((new, kind in ('store', 'branch', 'jal')))
        cur, ram, pc = new, nram, nxt
    print('\n'.join(lets))
    print('\n'.join(obls))
    print('\n'.join(steps))
    prev = None
    for k, (cname, isgoto) in enumerate(cores, 1):
        lem = 'Core.sameCsr_goto _ _' if isgoto else 'Core.sameCsr_wr _ _ _ _'
        print(f'  have {pfx}k{k} : {cname}.sameCsr {c0} := ({lem})' + (f'.trans {pfx}k{k-1}' if k > 1 else ''))
    run = f'.single (Quiet.of_sameCsr {pfx}k{n-1} hq) {pfx}s{n}' if n > 1 else f'.single hq {pfx}s1'
    for k in range(n - 1, 0, -1):
        q = 'hq' if k == 1 else f'(Quiet.of_sameCsr {pfx}k{k-1} hq)'
        run = f'.step {q} {pfx}s{k} ({run})'
    print(f'  have {pfx}run : QRun B img {n} ⟨{c0}, {r0}⟩ ⟨{cur}, {ram}⟩ :=\n    {run}')
    print(f'  -- ends at 0x{pc:08x}')


if __name__ == '__main__':
    main()
