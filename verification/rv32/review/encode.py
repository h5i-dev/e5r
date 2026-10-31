"""RISC-V instruction encoders for the review harness.

Original review code, Apache-2.0. Written from the RISC-V Unprivileged ISA
20240411 encoding tables (chapters 2, 13, 14 and 28 / "RV32/64G Instruction
Set Listings" and the RVC tables). Nothing is taken from Theories/Hart.lean:
the point is that the encodings and the model's decoder were written
independently, so a shared misreading of the spec is the only way both agree
on a wrong answer, and the assembler cross-check in harness.py narrows that.
"""


def _chk(v, bits, signed):
    lo, hi = (-(1 << (bits - 1)), (1 << (bits - 1)) - 1) if signed else (0, (1 << bits) - 1)
    if not lo <= v <= hi:
        raise ValueError(f'{v} does not fit in {bits} bits')
    return v & ((1 << bits) - 1)


def r_type(op, f3, f7, rd, rs1, rs2):
    return f7 << 25 | rs2 << 20 | rs1 << 15 | f3 << 12 | rd << 7 | op


def i_type(op, f3, rd, rs1, imm):
    return _chk(imm, 12, True) << 20 | rs1 << 15 | f3 << 12 | rd << 7 | op


def s_type(op, f3, rs1, rs2, imm):
    imm = _chk(imm, 12, True)
    return (imm >> 5) << 25 | rs2 << 20 | rs1 << 15 | f3 << 12 | (imm & 31) << 7 | op


def b_type(f3, rs1, rs2, off):
    assert off % 2 == 0
    imm = _chk(off, 13, True)
    return ((imm >> 12 & 1) << 31 | (imm >> 5 & 63) << 25 | rs2 << 20 | rs1 << 15 |
            f3 << 12 | (imm >> 1 & 15) << 8 | (imm >> 11 & 1) << 7 | 0x63)


def u_type(op, rd, imm20):
    return _chk(imm20, 20, False) << 12 | rd << 7 | op


def j_type(rd, off):
    assert off % 2 == 0
    imm = _chk(off, 21, True)
    return ((imm >> 20 & 1) << 31 | (imm >> 1 & 1023) << 21 | (imm >> 11 & 1) << 20 |
            (imm >> 12 & 255) << 12 | rd << 7 | 0x6f)


OP = {'add': (0, 0), 'sub': (0, 32), 'sll': (1, 0), 'slt': (2, 0), 'sltu': (3, 0),
      'xor': (4, 0), 'srl': (5, 0), 'sra': (5, 32), 'or': (6, 0), 'and': (7, 0),
      'mul': (0, 1), 'mulh': (1, 1), 'mulhsu': (2, 1), 'mulhu': (3, 1),
      'div': (4, 1), 'divu': (5, 1), 'rem': (6, 1), 'remu': (7, 1)}
OPIMM = {'addi': 0, 'slti': 2, 'sltiu': 3, 'xori': 4, 'ori': 6, 'andi': 7}
SHIFTI = {'slli': (1, 0), 'srli': (5, 0), 'srai': (5, 32)}
BRANCH = {'beq': 0, 'bne': 1, 'blt': 4, 'bge': 5, 'bltu': 6, 'bgeu': 7}
LOAD = {'lb': 0, 'lh': 1, 'lw': 2, 'lbu': 4, 'lhu': 5}
STORE = {'sb': 0, 'sh': 1, 'sw': 2}
AMO = {'amoadd.w': 0, 'amoswap.w': 1, 'amoxor.w': 4, 'amoor.w': 8, 'amoand.w': 12,
       'amomin.w': 16, 'amomax.w': 20, 'amominu.w': 24, 'amomaxu.w': 28}
CSR = {'csrrw': 1, 'csrrs': 2, 'csrrc': 3, 'csrrwi': 5, 'csrrsi': 6, 'csrrci': 7}


def op(name, rd, rs1, rs2):
    f3, f7 = OP[name]
    return r_type(0x33, f3, f7, rd, rs1, rs2)


def opimm(name, rd, rs1, imm):
    return i_type(0x13, OPIMM[name], rd, rs1, imm)


def shifti(name, rd, rs1, sh, f7_extra=0):
    f3, f7 = SHIFTI[name]
    return r_type(0x13, f3, f7 | f7_extra, rd, rs1, _chk(sh, 5, False))


def load(name, rd, rs1, off):
    return i_type(0x03, LOAD[name], rd, rs1, off)


def store(name, rs1, rs2, off):
    return s_type(0x23, STORE[name], rs1, rs2, off)


def branch(name, rs1, rs2, off):
    return b_type(BRANCH[name], rs1, rs2, off)


def jalr(rd, rs1, off):
    return i_type(0x67, 0, rd, rs1, off)


def amo(name, rd, rs1, rs2, aq=0, rl=0):
    return AMO[name] << 27 | aq << 26 | rl << 25 | rs2 << 20 | rs1 << 15 | 2 << 12 | rd << 7 | 0x2f


def lr(rd, rs1, rs2=0):
    return 2 << 27 | rs2 << 20 | rs1 << 15 | 2 << 12 | rd << 7 | 0x2f


def sc(rd, rs1, rs2):
    return 3 << 27 | rs2 << 20 | rs1 << 15 | 2 << 12 | rd << 7 | 0x2f


def csr(name, rd, src, addr):
    return _chk(addr, 12, False) << 20 | src << 15 | CSR[name] << 12 | rd << 7 | 0x73


# ---- RVC (chapter "C" Standard Extension, RV32 rows) -------------------

def _c(op, f3, body):
    return f3 << 13 | body | op


def _cr(r):
    assert 8 <= r <= 15
    return r - 8


def c_addi4spn(rd, nzuimm):
    u = nzuimm
    assert u % 4 == 0 and 0 <= u < 1024
    body = ((u >> 4 & 3) << 11 | (u >> 6 & 15) << 7 | (u >> 2 & 1) << 6 |
            (u >> 3 & 1) << 5 | _cr(rd) << 2)
    return _c(0, 0, body)


def c_lw(rd, rs1, uimm):
    u = uimm
    assert u % 4 == 0 and 0 <= u < 128
    return _c(0, 2, (u >> 3 & 7) << 10 | _cr(rs1) << 7 | (u >> 2 & 1) << 6 |
              (u >> 6 & 1) << 5 | _cr(rd) << 2)


def c_sw(rs1, rs2, uimm):
    return c_lw(rs2, rs1, uimm) | 4 << 13


def _ci(op, f3, rd, imm6):
    i = imm6 & 63
    return _c(op, f3, (i >> 5) << 12 | rd << 7 | (i & 31) << 2)


def c_addi(rd, imm):
    return _ci(1, 0, rd, _chk(imm, 6, True))


def c_li(rd, imm):
    return _ci(1, 2, rd, _chk(imm, 6, True))


def c_lui(rd, imm6):
    """imm6 is the 6-bit field nzimm[17:12] as a signed number."""
    return _ci(1, 3, rd, _chk(imm6, 6, True))


def c_addi16sp(imm):
    i = _chk(imm, 10, True)
    assert imm % 16 == 0
    return _c(1, 3, (i >> 9 & 1) << 12 | 2 << 7 | (i >> 4 & 1) << 6 | (i >> 6 & 1) << 5 |
              (i >> 7 & 3) << 3 | (i >> 5 & 1) << 2)


def _cj(f3, off):
    i = _chk(off, 12, True)
    assert off % 2 == 0
    return _c(1, f3, (i >> 11 & 1) << 12 | (i >> 4 & 1) << 11 | (i >> 8 & 3) << 9 |
              (i >> 10 & 1) << 8 | (i >> 6 & 1) << 7 | (i >> 7 & 1) << 6 |
              (i >> 1 & 7) << 3 | (i >> 5 & 1) << 2)


def c_jal(off):
    return _cj(1, off)


def c_j(off):
    return _cj(5, off)


def _cb(f3, rs1, off):
    i = _chk(off, 9, True)
    assert off % 2 == 0
    return _c(1, f3, (i >> 8 & 1) << 12 | (i >> 3 & 3) << 10 | _cr(rs1) << 7 |
              (i >> 6 & 3) << 5 | (i >> 1 & 3) << 3 | (i >> 5 & 1) << 2)


def c_beqz(rs1, off):
    return _cb(6, rs1, off)


def c_bnez(rs1, off):
    return _cb(7, rs1, off)


def c_shift(kind, rd, sh):
    """kind 0 = srli, 1 = srai; sh may be 0..63 (shamt[5] set is reserved on RV32)."""
    return _c(1, 4, (sh >> 5 & 1) << 12 | kind << 10 | _cr(rd) << 7 | (sh & 31) << 2)


def c_andi(rd, imm):
    i = _chk(imm, 6, True) & 63
    return _c(1, 4, (i >> 5) << 12 | 2 << 10 | _cr(rd) << 7 | (i & 31) << 2)


def c_arith(name, rd, rs2, bit12=0):
    f2 = {'sub': 0, 'xor': 1, 'or': 2, 'and': 3}[name]
    return _c(1, 4, bit12 << 12 | 3 << 10 | _cr(rd) << 7 | f2 << 5 | _cr(rs2) << 2)


def c_slli(rd, sh):
    return _c(2, 0, (sh >> 5 & 1) << 12 | rd << 7 | (sh & 31) << 2)


def c_lwsp(rd, uimm):
    u = uimm
    assert u % 4 == 0 and 0 <= u < 256
    return _c(2, 2, (u >> 5 & 1) << 12 | rd << 7 | (u >> 2 & 7) << 4 | (u >> 6 & 3) << 2)


def c_swsp(rs2, uimm):
    u = uimm
    assert u % 4 == 0 and 0 <= u < 256
    return _c(2, 6, (u >> 2 & 15) << 9 | (u >> 6 & 3) << 7 | rs2 << 2)


def c_cr(bit12, rd, rs2):
    """C.JR / C.MV (bit12 = 0) and C.EBREAK / C.JALR / C.ADD (bit12 = 1)."""
    return _c(2, 4, bit12 << 12 | rd << 7 | rs2 << 2)
