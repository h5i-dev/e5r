#!/usr/bin/env python3
"""Generate a straight-line QRun segment proof in the style of Projects/rmk/Deframer/*.lean.

The segment is given as a Python dict (see SEGMENTS in the caller); instruction encodings come
from the kernel-checked fact file. Output is Lean text: a `def` for the final core, a `def` for
the final RAM, and a theorem `QRun B img N ⟨c, ram⟩ ⟨core, ram'⟩`."""
import re
import sys

FACT = re.compile(r'theorem f([0-9a-f]+) : fetchDecode img 0x[0-9a-f]+ = some \((.*), 0x([0-9a-f]+)#32\) :=')


def load_facts(path):
    facts = {}
    for line in open(path):
        m = FACT.match(line)
        if m:
            facts[int(m.group(1), 16)] = (m.group(2), int(m.group(3), 16))
    return facts


def parse(instr):
    s = instr.replace('E5R.Instr.', '').replace('E5R.AluOp.', '').replace('E5R.Width.', '').replace(
        'E5R.BrCond.', '').replace('(', '').replace(')', '')
    return s.split()


class Seg:
    def __init__(self, facts, core0, ram0, regs, prefix):
        self.facts = facts
        self.regs = dict(regs)          # reg -> Lean expr
        self.core = core0
        self.ram = ram0
        self.lets = []                  # (name, expr)
        self.steps = []                 # (src, dst, ram_src, ram_dst, proof)
        self.quiet = []                 # (name, proof)
        self.prefix = prefix
        self.n = 0
        self.qname = 'hq'
        self.lastcore_expr = core0
        self.ramlets = []

    def E(self, r):
        r = int(r)
        if r == 0:
            return '0'
        return self.regs.get(r, f'{BASE}.get {r}')

    def names(self):
        return ', '.join(n for n, _ in self.lets) if self.lets else ''

    def getfact(self, core, r):
        """`have` proving core.get r = E(r)."""
        r = int(r)
        lets = ', '.join([n for n, _ in self.lets])
        return f"(show {core}.get {r} = {self.E(r)} by simp [{lets}{', ' if lets else ''}Core.wr_get_ne, Core.wr_get_self{EXTRA_SIMP}])"

    def newcore(self, expr):
        self.n += 1
        name = f'{self.prefix}{self.n}'
        self.lets.append((name, expr))
        q = f'q{self.prefix}{self.n}'
        kind = 'Core.sameCsr_goto _ _' if '.goto' in expr.split(' ')[0] or expr.startswith('(') and expr.rstrip().endswith(')') and False else None
        return name, q

    def step(self, pc, spec):
        instr, ln = self.facts[pc]
        f = parse(instr)
        kind = f[0]
        npc = pc + ln
        src = self.core
        hal = f"(by show (0x{pc:x} : Word).getLsbD 0 = false; decide)"
        fact = f"f{pc:x}"
        ramsrc = self.ram
        ramdst = self.ram
        if kind in ('op', 'opimm'):
            op, rd, rs1, x = f[1], int(f[2]), f[3], f[4]
            if kind == 'op':
                rhs = f"alu .{op} ({self.E(rs1)}) ({self.E(x)})"
                rws = []
                for r in sorted({int(rs1), int(x)}):
                    rws.append('Core.get_zero' if r == 0 else self.getfact(src, r))
            else:
                rhs = f"alu .{op} ({self.E(rs1)}) {x}"
                rws = ['Core.get_zero' if int(rs1) == 0 else self.getfact(src, rs1)]
            expr = f"{src}.wr {rd} ({rhs}) 0x{npc:x}"
            proof = f"rw [exec_{kind}{''.join(', ' + r for r in rws)}]; rfl"
            sc = 'Core.sameCsr_wr _ _ _ _'
            self.regs[rd] = rhs
        elif kind == 'lui':
            rd, imm = int(f[1]), f[2]
            expr = f"{src}.wr {rd} {imm} 0x{npc:x}"
            proof = "rw [exec_lui]; rfl"
            sc = 'Core.sameCsr_wr _ _ _ _'
            self.regs[rd] = imm
        elif kind == 'auipc':
            rd, imm = int(f[1]), f[2]
            rhs = f"(0x{pc:x} + {imm})"
            expr = f"{src}.wr {rd} {rhs} 0x{npc:x}"
            proof = "rw [exec_auipc]; rfl"
            sc = 'Core.sameCsr_wr _ _ _ _'
            self.regs[rd] = rhs
        elif kind == 'load':
            w, signed, rd, rs1, off = f[1], f[2], int(f[3]), f[4], f[5]
            base = self.E(rs1)
            addr = base if off == '0x00000000#32' else f"{base} + {off}"
            bytes_ = {'w': 4, 'h': 2, 'b': 1}[w]
            val = f"ramRead {self.ram} ({addr}) .{w}"
            if w != 'w':
                val = f"extend .{w} {signed} ({val})"
            expr = f"{src}.wr {rd} ({val}) 0x{npc:x}"
            al, inr = spec['al'], spec['in']
            z = ', BitVec.add_zero' if off == '0x00000000#32' else ''
            proof = (f"rw [exec_load, {self.getfact(src, rs1)}{z}, interp_load_ram (w := .{w}) o "
                     f"(show ({addr}).toNat % {bytes_} = 0 by {al}) "
                     f"(show B.inRam ({addr}) {bytes_} = true by {inr})]; rfl")
            sc = 'Core.sameCsr_wr _ _ _ _'
            self.regs[rd] = val
        elif kind == 'store':
            w, rs1, rs2, off = f[1], f[2], int(f[3]), f[4]
            base = self.E(rs1)
            addr = base if off == '0x00000000#32' else f"{base} + {off}"
            bytes_ = {'w': 4, 'h': 2, 'b': 1}[w]
            v = self.E(rs2)
            expr = f"{src}.goto 0x{npc:x}"
            rws = [self.getfact(src, rs1)]
            rws.append('Core.get_zero' if rs2 == 0 else self.getfact(src, rs2))
            z = ', BitVec.add_zero' if off == '0x00000000#32' else ''
            al, inr = spec['al'], spec['in']
            proof = (f"rw [exec_store, {', '.join(rws)}{z}, interp_store_ram (w := .{w}) o "
                     f"(show ({addr}).toNat % {bytes_} = 0 by {al}) "
                     f"(show B.inRam ({addr}) {bytes_} = true by {inr})]; rfl")
            sc = 'Core.sameCsr_goto _ _'
            newram = f"ramWrite {self.ram} ({addr}) ({v}) .{w}"
            rn = f"{self.prefix}R{len(self.ramlets) + 1}"
            self.ramlets.append((rn, newram))
            self.lets.append((rn, newram))
            ramdst = rn
            self.ram = rn
        elif kind == 'branch':
            cond, rs1, rs2, off = f[1], int(f[2]), int(f[3]), f[4]
            tk = spec['taken']
            offv = int(off.split('#')[0], 16)
            if offv >= 1 << 31:
                offv -= 1 << 32
            tgt = (pc + offv) & 0xffffffff
            expr = f"{src}.goto 0x{(tgt if tk else npc):x}"
            rws = []
            for r in sorted({rs1, rs2}):
                rws.append('Core.get_zero' if r == 0 else self.getfact(src, r))
            A = self.E(rs1); Bv = self.E(rs2)
            ht = f"(show taken .{cond} ({A}) ({Bv}) = {'true' if tk else 'false'} by {spec['why']})"
            if tk:
                proof = (f"rw [exec_branch, {', '.join(rws)}, {ht}]; simp only [↓reduceIte]; "
                         f"rw [show ({src}).pc + {off} = 0x{tgt:x} from rfl, jump_ok _ _ (by decide)]; rfl")
            else:
                proof = f"rw [exec_branch, {', '.join(rws)}, {ht}]; simp only [↓reduceIte, Bool.false_eq_true]; rfl"
            sc = 'Core.sameCsr_goto _ _'
        elif kind == 'jal':
            rd, off = int(f[1]), f[2]
            assert rd == 0
            offv = int(off.split('#')[0], 16)
            if offv >= 1 << 31:
                offv -= 1 << 32
            tgt = (pc + offv) & 0xffffffff
            expr = f"{src}.goto 0x{tgt:x}"
            proof = (f"rw [exec_jal, Core.set_zero, show ({src}).pc + {off} = 0x{tgt:x} from rfl, "
                     f"jump_ok _ _ (by decide)]; rfl")
            sc = 'Core.sameCsr_goto _ _'
        elif kind == 'jalr':
            rd, rs1, off = int(f[1]), int(f[2]), f[3]
            tgt = spec['target']
            assert rd == 1
            expr = f"{src}.wr 1 0x{npc:x} 0x{tgt:x}"
            proof = (f"rw [exec_jalr, {self.getfact(src, rs1)}, show ({self.E(rs1)}) + {off} &&& ~~~1 = 0x{tgt:x} by decide, "
                     f"jump_ok _ _ (by decide)]; rfl")
            sc = 'Core.sameCsr_wr _ _ _ _'
            self.regs[1] = f"0x{npc:x}"
        else:
            raise SystemExit(f'unsupported {kind} at {pc:x}')
        if self.n == 0 and FIRST_HPC:
            hal = "(by rw [hpc]; decide)"
            fact = f"(by rw [hpc]; exact {fact})"
            k = proof.rfind(']; rfl')
            proof = proof[:k] + ', hpc' + proof[k:]
        name, q = self.newcore(expr)
        self.steps.append((src, name, ramsrc, ramdst, f"refine detStep_of {hal} {fact} fun o => ?_\n    {proof}", self.qname))
        self.quiet.append((q, f"Quiet.of_sameCsr ({sc}) {self.qname}"))
        self.qname = q
        self.core = name
        return npc


BASE = 'c'
EXTRA_SIMP = ''
FIRST_HPC = True


def emit(facts, name, params, hyps, start, stop, specs, regs, ram0='ram', prefix='k', pre=''):
    """Lean text: `theorem name params hyps : QRun B img N ⟨c, ram0⟩ ⟨core, ram⟩` with the final core
    and ram returned as `let`-free expressions in a pair of defs."""
    s = Seg(facts, BASE, ram0, regs, prefix)
    pc = start
    while pc != stop:
        pc = s.step(pc, specs.get(pc, {}))
    N = len(s.steps)
    # final expressions with lets inlined, for the defs
    env = {}
    for n, e in s.lets:
        for k, v in env.items():
            e = re.sub(rf'(?<![\w.]){re.escape(k)}(?![\w])', f'({v})', e)
        env[n] = e
    core_def = env[s.core]
    ram_def = env.get(s.ram, s.ram)
    out = []
    out.append(f"def {name}Core {params} : Core :=\n  {core_def}\n")
    out.append(f"def {name}Ram {params} : Word → BitVec 8 :=\n  {ram_def}\n")
    args = ' '.join(p.split(':')[0].strip('( ').split()[0] for p in re.findall(r'\([^()]*\)', params))
    out.append(f"theorem {name} {params} {hyps} :\n    QRun B img {N} ⟨{BASE}, {ram0}⟩ ⟨{name}Core {args}, {name}Ram {args}⟩ := by")
    if pre:
        out.append(pre)
    for n, e in s.lets:
        out.append(f"  let {n} := {e}")
    for q, p in s.quiet:
        out.append(f"  have {q} : Quiet {q[1:]} := {p}")
    for i, (src, dst, rs, rd, proof, q) in enumerate(s.steps):
        out.append(f"  have s{i} : DetStep B img ⟨{src}, {rs}⟩ ⟨{dst}, {rd}⟩ := by\n    {proof}")
    chain = ''
    for i in range(N - 1, -1, -1):
        q = s.steps[i][5]
        if i == N - 1:
            chain = f"(.single {q} s{i})"
        else:
            chain = f"(.step {q} s{i} {chain})"
    out.append(f"  exact {chain[1:-1]}")
    return '\n'.join(out) + '\n'


if __name__ == '__main__':
    print('library; import and call emit()')
