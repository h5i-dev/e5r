#!/usr/bin/env python3
"""Negative controls for the review harness: seeded model bugs must be caught.

Original review code, Apache-2.0. Each mutant edits one exact span of a copy
of Theories/Hart.lean or Platform.lean in a scratch directory (the span must
occur exactly once, so a stale mutant fails loudly instead of silently
testing the unmodified model), builds only the modules Diff.lean imports, and
re-runs the Lean comparison over the QEMU records of the last harness run.

Outcomes are kept apart:
  KILLED    -- the build succeeded and at least one case changed verdict
               against its expectation;
  SURVIVED  -- the build succeeded and every case still met its expectation;
  TOOL      -- the build or the comparison did not complete. That is not a
               kill: a crash says nothing about the semantics.

Usage: harness.py first (it leaves qemu.txt in --out), then mutants.py.
"""
import argparse
import json
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
RV32 = HERE.parent
sys.path.insert(0, str(HERE))

H, P = 'Theories/Hart.lean', 'Theories/Platform.lean'
MUTANTS = [
    ('mulh-truncating', H, '((a.toInt * b.toInt) / 4294967296)', '((a.toInt * b.toInt).tdiv 4294967296)'),
    ('mulhsu-unsigned', H, '(a.toInt * (b.toNat : Int))', '((a.toNat : Int) * (b.toNat : Int))'),
    ('div-by-zero-0', H, '.div => if b = 0 then BitVec.allOnes 32', '.div => if b = 0 then 0'),
    ('div-floor', H, 'BitVec.ofInt 32 (a.toInt.tdiv b.toInt)', 'BitVec.ofInt 32 (a.toInt.fdiv b.toInt)'),
    ('rem-by-zero-0', H, '.rem => if b = 0 then a', '.rem => if b = 0 then 0'),
    ('remu-by-zero-0', H, '.remu => if b = 0 then a', '.remu => if b = 0 then 0'),
    ('sra-logical', H, '.sra => a.sshiftRight (b.toNat % 32)', '.sra => a >>> (b.toNat % 32)'),
    ('sll-unmasked', H, '.sll => a <<< (b.toNat % 32)', '.sll => a <<< b.toNat'),
    ('sltu-signed', H, '.sltu => if a.ult b then 1 else 0', '.sltu => if a.slt b then 1 else 0'),
    ('x0-writable', H, 'def Core.get (c : Core) (r : Reg) : Word := if r.val = 0 then 0 else c.x r\n'
     'def Core.set (c : Core) (r : Reg) (v : Word) : Core :=\n  if r.val = 0 then c else',
     'def Core.get (c : Core) (r : Reg) : Word := c.x r\n'
     'def Core.set (c : Core) (r : Reg) (v : Word) : Core :=\n  if false then c else'),
    ('lb-zero-extends', H, '| .b, true => (v.setWidth 8).signExtend 32', '| .b, true => v &&& 0xff'),
    ('lhu-sign-extends', H, '| .h, false => v &&& 0xffff', '| .h, false => (v.setWidth 16).signExtend 32'),
    ('immB-bit11', H, 'bits w 7 1 * 2048 + bits w 25 6 * 32', 'bits w 7 1 * 1024 + bits w 25 6 * 32'),
    ('immJ-bit11', H, 'bits w 20 1 * 2048 + bits w 21 10 * 2', 'bits w 20 1 * 1024 + bits w 21 10 * 2'),
    ('immS-split', H, 'sext 12 (bits w 25 7 * 32 + bits w 7 5)', 'sext 12 (bits w 25 7 * 16 + bits w 7 5)'),
    ('c.lui-zero-ext', H, 'some (.lui rd (sext 18 (n * 4096)))', 'some (.lui rd (BitVec.ofNat 32 (n * 4096)))'),
    ('c.srli-accepts-shamt5', H, '| 0 => if bits h 12 1 = 0 then some (.opimm .srl r r sh) else none',
     '| 0 => some (.opimm .srl r r sh)'),
    ('c.addi4spn-scale', H, 'bits h 7 4 * 64 + bits h 11 2 * 16', 'bits h 7 4 * 32 + bits h 11 2 * 16'),
    ('c.lwsp-rd0-accepted', H, '  | 2, 2 =>\n    if rd.val = 0 then none else', '  | 2, 2 =>\n    if false then none else'),
    ('cj-bit-swap', H, 'bits h 6 1 * 128 + bits h 7 1 * 64', 'bits h 7 1 * 128 + bits h 6 1 * 64'),
    ('jalr-keeps-bit0', H, 'jump (c.set rd next) ((c.get rs1 + off) &&& ~~~1)', 'jump (c.set rd next) (c.get rs1 + off)'),
    ('jal-link-pc+4', H, '| .jal rd off => jump (c.set rd next)', '| .jal rd off => jump (c.set rd (c.pc + 4))'),
    ('jalr-link-after-read', H, '| .jalr rd rs1 off => jump (c.set rd next) ((c.get rs1 + off) &&& ~~~1)',
     '| .jalr rd rs1 off => let c1 := c.set rd next; jump c1 ((c1.get rs1 + off) &&& ~~~1)'),
    ('amomax-unsigned', H, '| .max => if old.slt v then v else old', '| .max => if old.ult v then v else old'),
    ('amo-rd-new', H, '.store .w (c.get rs1) (amoOp op old (c.get rs2)) true (adv (c.set rd old))',
     '.store .w (c.get rs1) (amoOp op old (c.get rs2)) true (adv (c.set rd (amoOp op old (c.get rs2))))'),
    ('sc-success-rd1', H, 'true (adv ({ c with resv := false }.set rd 0))', 'true (adv ({ c with resv := false }.set rd 1))'),
    ('lr-no-reservation', H, 'adv ({ c with resv := true }.set rd v)', 'adv ({ c with resv := false }.set rd v)'),
    ('mret-mpie-kept', H, 'jump { c with mie_ := c.mpie, mpie := true, mpp := 0 } c.mepc',
     'jump { c with mie_ := c.mpie, mpp := 0 } c.mepc'),
    ('mret-mpp-kept', H, 'jump { c with mie_ := c.mpie, mpie := true, mpp := 0 } c.mepc',
     'jump { c with mie_ := c.mpie, mpie := true } c.mepc'),
    ('irq-mepc-next', H, '.done { c with pc := target, mepc := c.pc,', '.done { c with pc := target, mepc := c.pc + 4,'),
    ('irq-vector-ignored', H, 'if c.mtvec.extractLsb\' 0 2 = 1 then base + BitVec.ofNat 32 (4 * code) else base', 'base'),
    ('irq-mpie-not-saved', H, 'mpie := c.mie_, mie_ := false, mpp := 3 }', 'mie_ := false, mpp := 3 }'),
    ('irq-ignores-mie-reg', H, 'c.mie_ && code ∈ irqCodes && c.mieReg.getLsbD code', 'c.mie_ && code ∈ irqCodes'),
    ('mstatus-mpp-shift', H, '(c.mpp.setWidth 32 <<< 11)', '(c.mpp.setWidth 32 <<< 12)'),
    ('mie-mask-no-mtie', H, 'def mieMask : Word := 0x888', 'def mieMask : Word := 0x808'),
    ('mepc-keeps-bit0', H, 'fin { c with mepc := v &&& ~~~1 }', 'fin { c with mepc := v }'),
    ('csr-ro-write-allowed', H, 'if writes && addr / 1024 == 3 then .trap .illegal else', 'if false then .trap .illegal else'),
    ('csrrs-x0-writes', H, 'let writes : Bool := op == .rw || !srcZero', 'let writes : Bool := true'),
    ('csr-rd-written-late', H, 'let c\' := c.set rd old\n    if !writes then fin c\' else',
     'let c\' := c\n    if !writes then fin (c.set rd old) else'),
    ('fencei-illegal', H, 'else if f3 = 1 then some .fencei else none', 'else none'),
    ('ecall-as-ebreak', H, 'if w = 0x00000073 then some .ecall', 'if w = 0x00000073 then some .ebreak'),
    ('ramWrite-h-swapped', P, '| .h => ramPut (ramPut ram a (byteOf v 0)) (a+1) (byteOf v 1)',
     '| .h => ramPut (ramPut ram a (byteOf v 1)) (a+1) (byteOf v 0)'),
    ('load-misaligned-unchecked', P, '  | .load w a atomic k, ram, i, evs =>\n    -- The E31 has no misaligned-access support: every misaligned load traps.\n    if a.toNat % w.bytes ≠ 0 then .fault .misaligned',
     '  | .load w a atomic k, ram, i, evs =>\n    if false then .fault .misaligned'),
    ('device-read-from-ram', P, '| some d => if d.read && w = .w then interp B img o (k (o i)) ram (i+1) evs',
     '| some d => if d.read && w = .w then interp B img o (k (ramRead ram a w)) ram (i+1) evs'),
]


def apply(src, old, new):
    text = src.read_text()
    n = text.count(old)
    if n != 1:
        raise SystemExit(f'mutation span occurs {n} times in {src}: stale mutant')
    src.write_text(text.replace(old, new))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', default='/dev/shm/e5r-isa-review-20261029T042314Z/diff')
    ap.add_argument('--work', default='/dev/shm/e5r-isa-review-20261029T042314Z/mutants')
    ap.add_argument('--only', default='')
    ap.add_argument('--summary', default='')
    args = ap.parse_args()
    import cases as catalog
    import harness
    cases = catalog.all_cases()
    harness.describe(cases)
    out = Path(args.out)
    results = []
    for name, rel, old, new in MUTANTS:
        if args.only and args.only not in name:
            continue
        root = Path(args.work) / name
        if root.exists():
            shutil.rmtree(root)
        root.mkdir(parents=True)
        for f in ['lakefile.lean', 'lean-toolchain', 'lake-manifest.json']:
            shutil.copy(RV32 / f, root / f)
        shutil.copytree(RV32 / 'Theories', root / 'Theories',
                        ignore=shutil.ignore_patterns('*.olean', '*.ilean'))
        apply(root / rel, old, new)
        b = subprocess.run(['lake', 'build', 'Theories.Board.Hifive1Revb'], cwd=root,
                           capture_output=True, text=True, timeout=1200)
        if b.returncode != 0:
            results.append({'mutant': name, 'outcome': 'TOOL', 'detail': 'build failed: ' +
                            (b.stdout + b.stderr)[-600:]})
            print(f'{name:28s} TOOL (build failed)')
            continue
        mo = out / f'mut-{name}'
        mo.mkdir(exist_ok=True)
        shutil.copy(out / 'qemu.txt', mo / 'qemu.txt')
        rc, _, unexpected, _, err = harness.evaluate(cases, mo, lean_root=root)
        if rc == 3:
            results.append({'mutant': name, 'outcome': 'TOOL', 'detail': err[-600:]})
            print(f'{name:28s} TOOL (comparison did not run)')
        elif unexpected:
            results.append({'mutant': name, 'outcome': 'KILLED', 'cases': len(unexpected),
                            'first': unexpected[:3]})
            print(f'{name:28s} KILLED by {len(unexpected)} cases; e.g. {unexpected[0][:110]}')
        else:
            results.append({'mutant': name, 'outcome': 'SURVIVED'})
            print(f'{name:28s} SURVIVED')
        shutil.rmtree(root)
    if args.summary:
        Path(args.summary).write_text(json.dumps(results, indent=1) + '\n')
    return 0


if __name__ == '__main__':
    sys.exit(main())
