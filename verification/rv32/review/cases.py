"""Boundary-case catalog for the review harness.

Original review code, Apache-2.0. Each case names what QEMU should do
(`expect`) and what the model should do (`model`): `agree` (same post-state or
same trap class) or `decline` (the model returns `unsupported`, a documented
restriction). A case whose outcome differs from either is reported, so a
test that silently stopped exercising its target is visible, not a pass.
"""
import encode as E
from harness import Case, RECORD, WINDOW, fwd, FT_TO_TK

M32 = 0xffffffff
EDGE = [0, 1, 2, 0x7fffffff, 0x80000000, 0x80000001, 0xffffffff, 0xfffffffe, 0x12345678,
        0xedcba987]
PAIRS = [(a, b) for a in [0, 1, 0x7fffffff, 0x80000000, 0xffffffff, 0x12345678, 0xfffffff9]
         for b in [0, 1, 0x7fffffff, 0x80000000, 0xffffffff, 0x00000007, 0xfffffffe]]
SHIFTS = [0, 1, 15, 31, 32, 33, 63, 0xffffffe1, 0x80000000]
CAUSE_ILLEGAL, CAUSE_LMIS, CAUSE_SMIS, CAUSE_LACC, CAUSE_SACC = 2, 4, 6, 5, 7

MSTATUS, MIE, MTVEC, MSCRATCH, MEPC, MCAUSE, MIP, MHARTID = (
    0x300, 0x304, 0x305, 0x340, 0x341, 0x342, 0x344, 0xf14)


def alu():
    out = []
    for name in ['add', 'sub', 'slt', 'sltu', 'xor', 'or', 'and']:
        for a, b in PAIRS:
            out.append(Case(f'{name} {a:#x},{b:#x}', 'rv32i-op', [E.op(name, 10, 11, 12)],
                            regs={11: a, 12: b}))
    for name in ['sll', 'srl', 'sra']:
        for a in [0x80000001, 0xffffffff, 0x12345678, 1]:
            for s in SHIFTS:
                out.append(Case(f'{name} {a:#x},{s:#x}', 'rv32i-op', [E.op(name, 10, 11, 12)],
                                regs={11: a, 12: s}))
    # Aliasing and x0: rd = rs1 = rs2, rd = x0 (must stay 0), rs = x0.
    out.append(Case('add x5,x5,x5', 'rv32i-op', [E.op('add', 5, 5, 5)], regs={5: 0x80000001}))
    out.append(Case('sub x0,x11,x12', 'x0', [E.op('sub', 0, 11, 12)], regs={11: 5, 12: 9}))
    out.append(Case('sltu x10,x0,x11', 'rv32i-op', [E.op('sltu', 10, 0, 11)], regs={11: 1}))
    out.append(Case('sltu x10,x0,x0', 'rv32i-op', [E.op('sltu', 10, 0, 0)]))
    for rd in range(1, 32):
        if rd in (27,):
            continue
        out.append(Case(f'addi x{rd} every rd', 'rv32i-imm', [E.opimm('addi', rd, 0, -1)]))
    for name in ['addi', 'slti', 'sltiu', 'xori', 'ori', 'andi']:
        for a in [0, 1, 0x7fffffff, 0x80000000, 0xffffffff, 0x800]:
            for imm in [-2048, -1, 0, 1, 2047]:
                out.append(Case(f'{name} {a:#x},{imm}', 'rv32i-imm', [E.opimm(name, 10, 11, imm)],
                                regs={11: a}))
    for name in ['slli', 'srli', 'srai']:
        for a in [0x80000001, 0xffffffff, 0x40000000]:
            for s in [0, 1, 16, 31]:
                out.append(Case(f'{name} {a:#x},{s}', 'rv32i-imm', [E.shifti(name, 10, 11, s)],
                                regs={11: a}))
    # shamt[5] = 1 is reserved on RV32 (f7 bit 0), and SRAI with other f7 bits.
    for name in ['slli', 'srli', 'srai']:
        out.append(Case(f'{name} shamt[5]=1', 'illegal', [E.shifti(name, 10, 11, 1, f7_extra=1)],
                        expect='trap:2'))
    out.append(Case('srli f7=0x10', 'illegal', [E.shifti('srli', 10, 11, 1, f7_extra=0x10)],
                    expect='trap:2'))
    out.append(Case('addi x0,x11,7 (hint)', 'x0', [E.opimm('addi', 0, 11, 7)]))
    # Write x0, then read it back through every operand position.
    out.append(Case('write x0 then read', 'x0', [E.opimm('addi', 0, 11, 7), E.op('add', 10, 0, 0),
                                                E.opimm('addi', 12, 0, 0), E.store('sw', 13, 0, 0)],
                    regs={11: 5, 13: WINDOW}))
    out.append(Case('c.li x0 then c.mv', 'x0', [E.c_li(0, 5), E.op('or', 10, 0, 10)],
                    regs={10: 0x55}))
    for imm20 in [0, 1, 0x7ffff, 0x80000, 0xfffff]:
        out.append(Case(f'lui {imm20:#x}', 'rv32i-imm', [E.u_type(0x37, 10, imm20)]))
        out.append(Case(f'auipc {imm20:#x}', 'rv32i-imm', [E.u_type(0x17, 10, imm20)]))
    out.append(Case('lui x0', 'x0', [E.u_type(0x37, 0, 0xfffff)]))
    return out


def muldiv():
    out = []
    special = [(0x80000000, 0xffffffff), (0x80000000, 1), (0xfffffff9, 2), (7, 0xfffffffe),
               (0xfffffff9, 0xfffffffe), (0xffffffff, 1), (1, 0xffffffff), (0, 0),
               (0x80000000, 0), (5, 0), (0xfffffffb, 0), (0x7fffffff, 0x7fffffff),
               (0x80000000, 0x80000000), (0x12345678, 0x9abcdef0), (3, 0x80000000)]
    for name in ['mul', 'mulh', 'mulhsu', 'mulhu', 'div', 'divu', 'rem', 'remu']:
        for a, b in PAIRS + special:
            out.append(Case(f'{name} {a:#x},{b:#x}', 'rv32m', [E.op(name, 10, 11, 12)],
                            regs={11: a, 12: b}))
        out.append(Case(f'{name} x0 dest', 'x0', [E.op(name, 0, 11, 12)], regs={11: 7, 12: 3}))
        out.append(Case(f'{name} rd=rs1=rs2', 'rv32m', [E.op(name, 13, 13, 13)],
                        regs={13: 0xfffffff9}))
    return out


def branches():
    out = []
    vals = [(0, 0), (1, 0), (0, 1), (0x80000000, 0x7fffffff), (0x7fffffff, 0x80000000),
            (0xffffffff, 0), (0, 0xffffffff), (0xffffffff, 0xffffffff)]
    for name in E.BRANCH:
        for a, b in vals:
            # Taken target: forward K = 0 lands right after the save block.
            off = fwd(4)
            out.append(Case(f'{name} {a:#x},{b:#x} fwd', 'branch', [E.branch(name, 11, 12, off)],
                            regs={11: a, 12: b}, tk=('fwd', 0)))
        out.append(Case(f'{name} back -8', 'branch', [E.branch(name, 11, 11, -8)],
                        regs={11: 3}, tk=('bk', 0)))
        out.append(Case(f'{name} back -4096', 'branch', [E.branch(name, 11, 11, -4096)],
                        regs={11: 3}, tk=('bk', 4096 - 8)))
        out.append(Case(f'{name} fwd +4094', 'branch', [E.branch(name, 11, 11, 4094)],
                        regs={11: 3}, tk=('fwd', 4094 - fwd(4))))
        out.append(Case(f'{name} x0,x0', 'branch', [E.branch(name, 0, 0, fwd(4))],
                        tk=('fwd', 0)))
    # Taken branch to an address that is only 2-aligned: legal with C.
    out.append(Case('beq to 2 mod 4', 'branch', [E.branch('beq', 0, 0, fwd(4, 2))],
                    tk=('fwd', 2)))
    return out


def jumps():
    out = []
    for rd in [0, 1, 5]:
        out.append(Case(f'jal x{rd} fwd', 'jump', [E.j_type(rd, fwd(4))], tk=('fwd', 0)))
        out.append(Case(f'jal x{rd} back', 'jump', [E.j_type(rd, -8)], tk=('bk', 0)))
    out.append(Case('jal max fwd', 'jump', [E.j_type(1, 1048574)], tk=('fwd', 1048574 - fwd(4))))
    out.append(Case('jal far back', 'jump', [E.j_type(1, -(1 << 20) + 4096)],
                    tk=('bk', (1 << 20) - 4096 - 8)))
    for rd, rs1, imm, bit0 in [(1, 11, 0, 0), (0, 11, 0, 1), (5, 11, -2048, 0), (11, 11, 2047, 0),
                               (12, 11, 1, 0), (1, 1, -4, 1)]:
        # rs1 = tk - imm + bit0: bit 0 of the sum is cleared by JALR.
        regs = {rs1: f'tk_{{n}} - {imm - bit0}' if imm - bit0 >= 0 else f'tk_{{n}} + {bit0 - imm}'}
        out.append(Case(f'jalr x{rd},{imm}(x{rs1}) bit0={bit0}', 'jump', [E.jalr(rd, rs1, imm)],
                        regs=regs, tk=('fwd', 0)))
    out.append(Case('jalr f3=1', 'illegal', [E.i_type(0x67, 1, 1, 11, 0)], expect='trap:2'))
    return out


def memory():
    out = []
    base = WINDOW + 32
    for name in E.LOAD:
        for off in [-32, -31, -30, -29, 0, 1, 2, 3, 28, 31]:
            width = {'lb': 1, 'lbu': 1, 'lh': 2, 'lhu': 2, 'lw': 4}[name]
            mis = (base + off) % width != 0
            # QEMU 8.2 TCG performs misaligned loads/stores; the E31 traps
            # (FE310-G002 manual), and so does the model.
            out.append(Case(f'{name} {off}', 'load', [E.load(name, 10, 11, off)], regs={11: base},
                            model='oracle-divergence' if mis else 'agree',
                            note='QEMU emulates misaligned access' if mis else ''))
        out.append(Case(f'{name} x0 dest', 'x0', [E.load(name, 0, 11, 0)], regs={11: base}))
    out.append(Case('lw imm -2048', 'load', [E.load('lw', 10, 11, -2048)], regs={11: WINDOW + 2048}))
    out.append(Case('lw imm 2047', 'load', [E.load('lw', 10, 11, 2047)], regs={11: WINDOW - 2047}))
    out.append(Case('lw rd=rs1', 'load', [E.load('lw', 11, 11, 4)], regs={11: WINDOW}))
    for name in E.STORE:
        for off in [-32, -31, -30, 0, 1, 2, 3, 30]:
            width = {'sb': 1, 'sh': 2, 'sw': 4}[name]
            mis = (base + off) % width != 0
            out.append(Case(f'{name} {off}', 'store', [E.store(name, 11, 12, off)],
                            regs={11: base, 12: 0x8badf00d},
                            model='oracle-divergence' if mis else 'agree',
                            note='QEMU emulates misaligned access' if mis else ''))
    out.append(Case('sw x0 source', 'x0', [E.store('sw', 11, 0, 0)], regs={11: base}))
    out.append(Case('sw rs1=rs2', 'store', [E.store('sw', 11, 11, 0)], regs={11: base}))
    # Store-then-load round trips (byte order, sign extension of stored data).
    out.append(Case('sb;lb sign', 'store', [E.store('sb', 11, 12, 5), E.load('lb', 13, 11, 5),
                                           E.load('lbu', 14, 11, 5), E.load('lw', 15, 11, 4)],
                    regs={11: base, 12: 0x1234ff80}))
    out.append(Case('sh;lh sign', 'store', [E.store('sh', 11, 12, 6), E.load('lh', 13, 11, 6),
                                           E.load('lhu', 14, 11, 6), E.load('lw', 15, 11, 4)],
                    regs={11: base, 12: 0x12348001}))
    # Loads from the read-only image (flash) and a store to it.
    out.append(Case('lw from flash (own code)', 'load', [E.load('lw', 10, 11, 0)],
                    regs={11: 'cand_{n}'}))
    out.append(Case('lhu from flash', 'load', [E.load('lhu', 10, 11, 2)], regs={11: 'cand_{n}'}))
    out.append(Case('sw to flash', 'store', [E.store('sw', 11, 12, 0)], regs={11: 'cand_{n}'},
                    expect='ok', model='decline',
                    note='QEMU ignores ROM writes; the model declines (fails closed)'))
    # Unmapped addresses: QEMU raises access faults, the model declines.
    out.append(Case('lw unmapped', 'load', [E.load('lw', 10, 11, 0)], regs={11: 0x40000000},
                    expect='trap:5', model='decline'))
    out.append(Case('sw unmapped', 'store', [E.store('sw', 11, 12, 0)], regs={11: 0x40000000},
                    expect='trap:7', model='decline'))
    out.append(Case('lw past end of RAM', 'load', [E.load('lw', 10, 11, 0)], regs={11: 0x80004000},
                    expect='trap:5', model='decline'))
    # Device registers: word access is modeled (read = environment), byte is not.
    out.append(Case('lw mtime_lo', 'device', [E.load('lw', 10, 11, -8)], regs={11: 0x0200c000}))
    out.append(Case('sw msip=1', 'device', [E.store('sw', 11, 12, 0)], regs={11: 0x02000000, 12: 1}))
    out.append(Case('sb msip', 'device', [E.store('sb', 11, 12, 0)], regs={11: 0x02000000, 12: 1},
                    expect='trap:7', model='decline', note='byte device access is outside the model'))
    return out


def atomics():
    out = []
    a = WINDOW + 16
    for name in E.AMO:
        for old, v in [(0x80000000, 0x7fffffff), (0x7fffffff, 0x80000000), (0xffffffff, 1),
                       (1, 0xffffffff), (5, 5), (0, 0x80000000)]:
            win = list(range(16))
            win[4] = old
            out.append(Case(f'{name} {old:#x},{v:#x}', 'amo', [E.amo(name, 10, 11, 12)],
                            regs={11: a, 12: v}, win=win))
        out.append(Case(f'{name} rd=x0', 'x0', [E.amo(name, 0, 11, 12)], regs={11: a, 12: 3}))
        out.append(Case(f'{name} rd=rs2', 'amo', [E.amo(name, 12, 11, 12)], regs={11: a, 12: 3}))
        out.append(Case(f'{name} misaligned', 'amo', [E.amo(name, 10, 11, 12)],
                        regs={11: a + 2, 12: 3}, expect='trap:4',
                        note='QEMU reports load-misaligned (4) for an AMO'))
        out.append(Case(f'{name} aq rl', 'amo', [E.amo(name, 10, 11, 12, 1, 1)],
                        regs={11: a, 12: 3}))
    out.append(Case('amoadd to device', 'amo', [E.amo('amoadd.w', 10, 11, 12)],
                    regs={11: 0x02000000, 12: 0}, expect='ok', model='decline'))
    out.append(Case('lr;sc same addr', 'lrsc', [E.lr(10, 11), E.sc(13, 11, 12)],
                    regs={11: a, 12: 0xabcdef01}))
    out.append(Case('sc without lr', 'lrsc', [E.sc(13, 11, 12)], regs={11: a, 12: 0xabcdef01}))
    out.append(Case('lr;sc;sc', 'lrsc', [E.lr(10, 11), E.sc(13, 11, 12), E.sc(14, 11, 12)],
                    regs={11: a, 12: 0x5}))
    out.append(Case('lr;sc other addr', 'lrsc', [E.lr(10, 11), E.sc(13, 14, 12)],
                    regs={11: a, 14: a + 8, 12: 0x77},
                    note='QEMU fails it; the model may also succeed (unaddressed reservation)'))
    out.append(Case('lr misaligned', 'lrsc', [E.lr(10, 11)], regs={11: a + 1}, expect='trap:4'))
    out.append(Case('lr rs2!=0 reserved', 'illegal', [E.lr(10, 11, 5)], regs={11: a},
                    expect='trap:2'))
    # Misaligned SC with no reservation: the spec (Zalrsc) requires an
    # address-misaligned or access-fault exception regardless of success.
    # FINDING F1: the spec requires an exception for a misaligned (or
    # non-memory) SC whether or not it would succeed. QEMU 8.2 completes these
    # with rd = 1; on 593ed31 the model did too. With the fix the model faults,
    # so QEMU is the wrong oracle here.
    f1 = 'spec: misaligned SC always raises; QEMU completes it (F1)'
    out.append(Case('sc misaligned no resv', 'lrsc', [E.sc(13, 11, 12)], regs={11: a + 2},
                    model='oracle-divergence', note=f1))
    out.append(Case('sc unmapped no resv', 'lrsc', [E.sc(13, 11, 12)], regs={11: 0x40000000},
                    model='decline', note='the model declines an SC outside RAM (F1 fix)'))
    out.append(Case('lr;sc misaligned', 'lrsc', [E.lr(10, 11), E.sc(13, 14, 12)],
                    regs={11: a, 14: a + 2}, model='oracle-divergence', note=f1))
    out.append(Case('amo f3=3 (RV64 .d)', 'illegal', [E.amo('amoadd.w', 10, 11, 12) ^ (1 << 12)],
                    regs={11: a}, expect='trap:2'))
    out.append(Case('amo funct5=0x1f', 'illegal', [(0x1f << 27) | 12 << 20 | 11 << 15 | 2 << 12 |
                                                   10 << 7 | 0x2f], regs={11: a}, expect='trap:2'))
    return out


def compressed():
    out = []
    sp = WINDOW
    out.append(Case('c.addi4spn 4', 'rvc', [E.c_addi4spn(8, 4)], regs={2: 0x10}))
    out.append(Case('c.addi4spn 1020', 'rvc', [E.c_addi4spn(15, 1020)], regs={2: 0xfffffff0}))
    out.append(Case('c.addi4spn 0 reserved', 'rvc-illegal', [E.c_addi4spn(9, 0)],
                    expect='trap:2'))
    out.append(Case('c.unimp 0x0000', 'rvc-illegal', [0x0000], expect='trap:2'))
    for uimm in [0, 4, 60, 124]:
        out.append(Case(f'c.lw {uimm}', 'rvc', [E.c_lw(9, 10, uimm)], regs={10: WINDOW}))
        out.append(Case(f'c.sw {uimm}', 'rvc', [E.c_sw(10, 9, uimm)], regs={10: WINDOW, 9: 0x1234abcd}))
    for imm in [-32, -1, 1, 31]:
        out.append(Case(f'c.addi {imm}', 'rvc', [E.c_addi(10, imm)], regs={10: 0x7fffffff}))
        out.append(Case(f'c.li {imm}', 'rvc', [E.c_li(10, imm)]))
        out.append(Case(f'c.andi {imm}', 'rvc', [E.c_andi(9, imm)], regs={9: 0xa5a5a5a5}))
        out.append(Case(f'c.lui {imm}', 'rvc', [E.c_lui(10, imm)]))
    out.append(Case('c.addi x0 (hint/nop)', 'rvc-hint', [E.c_addi(0, 5)]))
    out.append(Case('c.nop', 'rvc-hint', [0x0001]))
    out.append(Case('c.addi rd, 0 (hint)', 'rvc-hint', [E.c_addi(10, 0)]))
    out.append(Case('c.li x0 (hint)', 'rvc-hint', [E.c_li(0, 5)]))
    out.append(Case('c.lui x0 (hint)', 'rvc-hint', [E.c_lui(0, 1)]))
    out.append(Case('c.lui 0 reserved', 'rvc-illegal', [E.c_lui(10, 0)], expect='trap:2'))
    for imm in [-512, -16, 16, 496]:
        out.append(Case(f'c.addi16sp {imm}', 'rvc', [E.c_addi16sp(imm)], regs={2: 0x80001000 + 0x400}))
    out.append(Case('c.addi16sp 0 reserved', 'rvc-illegal', [E.c_addi16sp(16) & ~0x107c],
                    expect='trap:2'))
    for sh in [1, 16, 31]:
        out.append(Case(f'c.srli {sh}', 'rvc', [E.c_shift(0, 9, sh)], regs={9: 0x80000001}))
        out.append(Case(f'c.srai {sh}', 'rvc', [E.c_shift(1, 9, sh)], regs={9: 0x80000001}))
        out.append(Case(f'c.slli {sh}', 'rvc', [E.c_slli(10, sh)], regs={10: 0x80000001}))
    out.append(Case('c.srli 0 (hint)', 'rvc-hint', [E.c_shift(0, 9, 0)], regs={9: 0x80000001}))
    out.append(Case('c.slli x0 (hint)', 'rvc-hint', [E.c_slli(0, 3)]))
    for kind, nm in [(0, 'c.srli'), (1, 'c.srai')]:
        out.append(Case(f'{nm} shamt[5]=1 (RV32 NSE)', 'rvc-illegal', [E.c_shift(kind, 9, 33)],
                        expect='trap:2'))
    out.append(Case('c.slli shamt[5]=1 (RV32 NSE)', 'rvc-illegal', [E.c_slli(10, 33)],
                    expect='trap:2'))
    for nm in ['sub', 'xor', 'or', 'and']:
        out.append(Case(f'c.{nm}', 'rvc', [E.c_arith(nm, 9, 10)], regs={9: 0x80000000, 10: 0xffffffff}))
    for f2 in ['sub', 'xor']:  # bit12 = 1: c.subw / c.addw (RV64), reserved on RV32
        out.append(Case(f'c.{f2} bit12 (c.subw/c.addw)', 'rvc-illegal', [E.c_arith(f2, 9, 10, 1)],
                        expect='trap:2'))
    for nm in ['or', 'and']:   # bit12 = 1, f2 = 2/3: reserved
        out.append(Case(f'c.{nm} bit12 reserved', 'rvc-illegal', [E.c_arith(nm, 9, 10, 1)],
                        expect='trap:2'))
    for uimm in [0, 4, 252]:
        out.append(Case(f'c.lwsp {uimm}', 'rvc', [E.c_lwsp(10, uimm)], regs={2: WINDOW - uimm + 8}))
        out.append(Case(f'c.swsp {uimm}', 'rvc', [E.c_swsp(10, uimm)],
                        regs={2: WINDOW - uimm + 12, 10: 0xcafef00d}))
    out.append(Case('c.lwsp x0 reserved', 'rvc-illegal', [E.c_lwsp(0, 4)], regs={2: sp},
                    expect='trap:2'))
    out.append(Case('c.mv', 'rvc', [E.c_cr(0, 10, 11)], regs={11: 0x80000000}))
    out.append(Case('c.mv x0 (hint)', 'rvc-hint', [E.c_cr(0, 0, 11)]))
    out.append(Case('c.add', 'rvc', [E.c_cr(1, 10, 11)], regs={10: 0xffffffff, 11: 2}))
    out.append(Case('c.add x0 (hint)', 'rvc-hint', [E.c_cr(1, 0, 11)]))
    out.append(Case('c.jr x0 reserved', 'rvc-illegal', [E.c_cr(0, 0, 0)], expect='trap:2'))
    out.append(Case('c.ebreak', 'rvc', [E.c_cr(1, 0, 0)], expect='trap:3'))
    out.append(Case('c.jr', 'rvc-jump', [E.c_cr(0, 11, 0)], regs={11: 'tk_{n}'}, tk=('fwd', 0)))
    out.append(Case('c.jalr', 'rvc-jump', [E.c_cr(1, 11, 0)], regs={11: 'tk_{n}'}, tk=('fwd', 0)))
    out.append(Case('c.jalr x1 (rs1 = link)', 'rvc-jump', [E.c_cr(1, 1, 0)], regs={1: 'tk_{n}'},
                    tk=('fwd', 0)))
    out.append(Case('c.j fwd', 'rvc-jump', [E.c_j(fwd(2))], tk=('fwd', 0)))
    out.append(Case('c.j back', 'rvc-jump', [E.c_j(-8)], tk=('bk', 0)))
    out.append(Case('c.j -2048', 'rvc-jump', [E.c_j(-2048)], tk=('bk', 2048 - 8)))
    out.append(Case('c.jal fwd 2046', 'rvc-jump', [E.c_jal(2046)], tk=('fwd', 2046 - fwd(2))))
    out.append(Case('c.jal back', 'rvc-jump', [E.c_jal(-8)], tk=('bk', 0)))
    for v in [0, 1, 0x80000000]:
        out.append(Case(f'c.beqz {v:#x}', 'rvc-jump', [E.c_beqz(9, fwd(2))], regs={9: v}, tk=('fwd', 0)))
        out.append(Case(f'c.bnez {v:#x}', 'rvc-jump', [E.c_bnez(9, fwd(2))], regs={9: v}, tk=('fwd', 0)))
    out.append(Case('c.beqz -256', 'rvc-jump', [E.c_beqz(9, -256)], regs={9: 0}, tk=('bk', 248)))
    out.append(Case('c.bnez +254', 'rvc-jump', [E.c_bnez(9, 254)], regs={9: 1}, tk=('fwd', 254 - fwd(2))))
    # Floating-point compressed loads/stores: no F/D on the E31 -> illegal.
    for f3, q in [(1, 0), (3, 0), (5, 0), (7, 0), (1, 2), (3, 2), (5, 2), (7, 2)]:
        out.append(Case(f'c.f* q{q} f3={f3}', 'rvc-illegal', [f3 << 13 | 1 << 7 | 1 << 2 | q],
                        regs={2: sp, 9: sp, 8: sp}, expect='trap:2'))
    out.append(Case('c q0 f3=4 reserved', 'rvc-illegal', [4 << 13 | 0x44], expect='trap:2'))
    # A sequence mixing 16- and 32-bit parcels (fall-through length 2 vs 4).
    out.append(Case('c.li; addi; c.addi', 'rvc', [E.c_li(10, 5), E.opimm('addi', 10, 10, 100),
                                                 E.c_addi(10, -3)]))
    return out


def system():
    out = []
    out.append(Case('ecall', 'system', [0x00000073], expect='trap:11'))
    out.append(Case('ebreak', 'system', [0x00100073], expect='trap:3'))
    out.append(Case('fence', 'system', [0x0ff0000f]))
    out.append(Case('fence.tso', 'system', [0x8330000f]))
    out.append(Case('fence odd fields', 'system', [0xf0a5800f]))
    out.append(Case('fence.i', 'system', [0x0000100f]))
    out.append(Case('pause (fence w,0)', 'system', [0x0100000f]))
    out.append(Case('misc-mem f3=2', 'illegal', [0x0000200f], expect='trap:2'))
    out.append(Case('sret', 'illegal', [0x10200073], expect='trap:2'))
    out.append(Case('uret/system f3=0 other', 'illegal', [0x00200073], expect='trap:2'))
    out.append(Case('sfence.vma', 'illegal', [0x12000073], model='oracle-divergence',
                    note='no S-mode on the E31: illegal; QEMU 8.2 executes it in M-mode'))
    out.append(Case('system f3=4', 'illegal', [0x00004073], expect='trap:2'))
    out.append(Case('wfi with pending msip', 'system', [0x10500073],
                    csr={'mie': 0x8, 'msip': 1}))
    for enc, nm in [(0x0000000b, 'custom-0'), (0x0000001b, 'addiw (RV64)'), (0x0000003b, 'addw (RV64)'),
                    (0x00003003, 'ld (RV64)'), (0x00006003, 'lwu (RV64)'), (0x00003023, 'sd (RV64)'),
                    (0x00002007, 'flw (no F)'), (0x02000053, 'fadd.s (no F)'),
                    (0x0000007f, '>=80-bit prefix'), (0x0000001f, '48-bit prefix'),
                    (0x00007063 | 0, 'branch f3=2? (f3=7 legal)'), (0x00002063, 'branch f3=2'),
                    (0x00003063, 'branch f3=3'), (0x04000033, 'op f7=2'), (0x40001033, 'sll f7=0x20'),
                    (0xffffffff, 'all ones')]:
        if nm.startswith('branch f3=2?'):
            continue
        out.append(Case(f'illegal {nm}', 'illegal', [enc], expect='trap:2'))
    return out


def csrs():
    out = []
    c = lambda name, rd, src, addr: E.csr(name, rd, src, addr)
    # mscratch: full read/write, every op form, rd = x0, rs = x0.
    for name in ['csrrw', 'csrrs', 'csrrc']:
        out.append(Case(f'{name} mscratch', 'csr', [c(name, 10, 11, MSCRATCH)], regs={11: 0xf0f0f0f0},
                        csr={'mscratch': 0x3c3c3c3c}))
        out.append(Case(f'{name} mscratch rs=x0', 'csr', [c(name, 10, 0, MSCRATCH)],
                        csr={'mscratch': 0x3c3c3c3c}))
        out.append(Case(f'{name} mscratch rd=rs', 'csr', [c(name, 11, 11, MSCRATCH)],
                        regs={11: 0xf0f0f0f0}, csr={'mscratch': 0x3c3c3c3c}))
    for name in ['csrrwi', 'csrrsi', 'csrrci']:
        for u in [0, 1, 31]:
            out.append(Case(f'{name} mscratch {u}', 'csr', [c(name, 10, u, MSCRATCH)],
                            csr={'mscratch': 0x3c3c3c3d}))
    out.append(Case('csrrw x0,mscratch', 'csr', [c('csrrw', 0, 11, MSCRATCH)], regs={11: 5}))
    # mepc: bit 0 is cleared (IALIGN = 16); bit 1 is kept.
    for v in [0x20010003, 0xffffffff, 0x20010002]:
        odd = v & 1
        out.append(Case(f'csrrw mepc {v:#x}', 'csr', [c('csrrw', 10, 11, MEPC)], regs={11: v},
                        model='oracle-divergence' if odd else 'agree',
                        note='spec: mepc[0] is always zero; QEMU 8.2 keeps the bit' if odd else ''))
    # mtvec: direct and vectored modes; modes 2/3 are outside the model.
    for v in [0x20010000, 0x20010041, 0x20010004]:
        out.append(Case(f'csrrw mtvec {v:#x}', 'csr', [c('csrrw', 10, 11, MTVEC)], regs={11: v}))
    out.append(Case('csrrw mtvec mode 2', 'csr', [c('csrrw', 10, 11, MTVEC)], regs={11: 0x20010002},
                    model='decline'))
    # mie: only MSIE/MTIE/MEIE are implemented on the E31.
    out.append(Case('csrrw mie 0x888', 'csr', [c('csrrw', 10, 11, MIE)], regs={11: 0x888}))
    out.append(Case('csrrs mie -1', 'csr', [c('csrrs', 10, 11, MIE)], regs={11: 0xffffffff},
                    model='oracle-divergence',
                    note='FE310 manual: other mie bits are hardwired 0; QEMU keeps more'))
    out.append(Case('csrrc mie', 'csr', [c('csrrc', 10, 11, MIE)], regs={11: 0x8}, csr={'mie': 0x888}))
    # mstatus: MIE, MPIE, MPP (M or U).
    for v in [0x0, 0x80, 0x1880, 0x1800, 0x1888 & ~0x8]:
        out.append(Case(f'csrrw mstatus {v:#x}', 'csr', [c('csrrw', 10, 11, MSTATUS)], regs={11: v}))
    out.append(Case('csrrsi mstatus MIE (no pending)', 'csr', [c('csrrsi', 10, 8, MSTATUS)]))
    out.append(Case('csrrci mstatus MIE', 'csr', [c('csrrci', 10, 8, MSTATUS)],
                    csr={'mstatus': 0x1888}))
    out.append(Case('csrrw mstatus MPP=1', 'csr', [c('csrrw', 10, 11, MSTATUS)], regs={11: 0x0800},
                    model='decline', note='WARL legalization is outside the model'))
    out.append(Case('csrrw mstatus MPRV', 'csr', [c('csrrw', 10, 11, MSTATUS)], regs={11: 0x21800},
                    model='decline'))
    out.append(Case('csrrs mstatus x0 read', 'csr', [c('csrrs', 10, 0, MSTATUS)],
                    csr={'mstatus': 0x1880}))
    # mcause: read; a write is outside the model.
    out.append(Case('csrr mcause', 'csr', [c('csrrs', 10, 0, MCAUSE)], csr={'mcause': 0x8000000b}))
    out.append(Case('csrw mcause', 'csr', [c('csrrw', 10, 11, MCAUSE)], regs={11: 3},
                    model='decline'))
    # mip: read is environmental; write has no effect on MSIP/MTIP/MEIP.
    out.append(Case('csrr mip (msip pending)', 'csr', [c('csrrs', 10, 0, MIP)],
                    csr={'msip': 1}))
    out.append(Case('csrrw mip', 'csr', [c('csrrw', 10, 11, MIP)], regs={11: 0xffffffff},
                    csr={'msip': 1}))
    # mhartid and other read-only CSRs: reads, and writes that must trap.
    out.append(Case('csrr mhartid', 'csr', [c('csrrs', 10, 0, MHARTID)]))
    out.append(Case('csrrsi mhartid,0 (no write)', 'csr', [c('csrrsi', 10, 0, MHARTID)]))
    out.append(Case('csrrw mhartid (write ro)', 'csr', [c('csrrw', 10, 11, MHARTID)], expect='trap:2'))
    out.append(Case('csrrs mhartid,x11 (write ro)', 'csr', [c('csrrs', 10, 11, MHARTID)],
                    regs={11: 1}, expect='trap:2'))
    out.append(Case('csrrwi x0, mhartid (write ro)', 'csr', [c('csrrwi', 0, 0, MHARTID)],
                    expect='trap:2'))
    out.append(Case('csrr misa', 'csr', [c('csrrs', 10, 0, 0x301)], model='decline'))
    out.append(Case('csrr mcycle', 'csr', [c('csrrs', 10, 0, 0xb00)], model='decline'))
    out.append(Case('csrr cycle (U counter)', 'csr', [c('csrrs', 10, 0, 0xc00)], model='decline'))
    out.append(Case('csrr nonexistent 0x7c0', 'csr', [c('csrrs', 10, 0, 0x7c0)], expect='trap:2',
                    model='decline'))
    out.append(Case('csrr sstatus (no S)', 'csr', [c('csrrs', 10, 0, 0x100)], expect='trap:2',
                    model='decline'))
    return out


def privileged():
    out = []
    # MRET to M: MIE <- MPIE, MPIE <- 1, MPP <- U (least privileged supported).
    for ms in [0x1880, 0x1800, 0x1808, 0x1888]:
        out.append(Case(f'mret mstatus {ms:#x}', 'mret', [0x30200073],
                        csr={'mstatus': ms, 'mepc': 'tk_{n}'}, tk=('fwd', 0)))
    out.append(Case('mret to 2-aligned mepc', 'mret', [0x30200073],
                    csr={'mstatus': 0x1800, 'mepc': 'tk_{n}'}, tk=('fwd', 2)))
    # Interrupt entry. MSIP pending + MSIE, enabled by the candidate.
    for vec in [0, 1]:
        mt = 'vtable + 1' if vec else 'handler'
        out.append(Case(f'irq msip after csrsi (mtvec mode {vec})', 'irq',
                        [E.csr('csrrsi', 0, 8, MSTATUS)],
                        csr={'mie': 0x8, 'msip': 1, 'mtvec': mt, 'mstatus': 0x1880},
                        expect='irq:3'))
        out.append(Case(f'irq mtip after csrsi (mtvec mode {vec})', 'irq',
                        [E.csr('csrrsi', 0, 8, MSTATUS)],
                        csr={'mie': 0x80, 'mtimecmp_lo': 0, 'mtimecmp_hi': 0, 'mtvec': mt},
                        expect='irq:7'))
    # Interrupt raised by a device store in the candidate: sw msip = 1 with MIE on.
    out.append(Case('irq raised by sw msip', 'irq', [E.store('sw', 11, 12, 0), 0x00000013],
                    regs={11: 0x02000000, 12: 1}, csr={'mie': 0x8, 'mstatus': 0x1808},
                    expect='irq:3'))
    # Enabled via mie, not mstatus.
    out.append(Case('irq after csrw mie', 'irq', [E.csr('csrrs', 0, 11, MIE)], regs={11: 0x8},
                    csr={'msip': 1, 'mstatus': 0x1808}, expect='irq:3'))
    # Pending but disabled (MSIE off): no interrupt, wfi falls through.
    out.append(Case('pending, MSIE off: no irq', 'irq', [E.csr('csrrsi', 0, 8, MSTATUS), 0x00000013],
                    csr={'msip': 1, 'mie': 0x80}))
    return out


def all_cases():
    return alu() + muldiv() + branches() + jumps() + memory() + atomics() + compressed() + system() + \
        csrs() + privileged()
