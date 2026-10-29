#!/usr/bin/env python3
"""Which mnemonics a replayed trace executed: llvm-objdump of the test ELF
joined with the pcs in the compact trace. Exits non-zero if any required
instruction kind was never executed."""
import subprocess
import sys

REQUIRED = """add sub sll slt sltu xor srl sra or and addi slti sltiu xori ori andi slli srli srai
lui auipc beq bne blt bge bltu bgeu jal jalr lb lbu lh lhu lw sb sh sw
mul mulh mulhsu mulhu div divu rem remu lr.w sc.w amoswap.w amoadd.w amoxor.w amoand.w
amoor.w amomin.w amomax.w amominu.w amomaxu.w fence fence.i
c.addi c.li c.lui c.mv c.add c.sub c.xor c.or c.and c.srli c.srai c.andi c.slli c.lw c.sw
c.lwsp c.swsp c.addi16sp c.addi4spn c.beqz c.bnez c.j c.jal c.jr c.jalr c.nop""".split()


def main():
    objdump, elf, traces = sys.argv[1], sys.argv[2], sys.argv[3:]
    dis = subprocess.check_output([objdump, '-d', '--mattr=+m,+a,+c,+zifencei', '--no-show-raw-insn',
                                   '-M', 'no-aliases', elf], text=True)
    at = {}
    for line in dis.splitlines():
        parts = line.strip().split(':', 1)
        if len(parts) == 2 and all(c in '0123456789abcdef' for c in parts[0]) and parts[0]:
            fields = parts[1].split()
            if fields:
                at[int(parts[0], 16)] = fields[0].split('.aq')[0].split('.rl')[0]
    seen = {}
    for t in traces:
        for line in open(t):
            pc = int(line.split()[1], 16)
            m = at.get(pc)
            if m:
                seen[m] = seen.get(m, 0) + 1
    missing = [m for m in REQUIRED if m not in seen]
    print(f'{sum(seen.values())} executed instructions, {len(seen)} kinds: ' +
          ' '.join(f'{k}:{v}' for k, v in sorted(seen.items())))
    if missing:
        sys.exit(f'never executed: {" ".join(missing)}')
    print('every required instruction kind executed')


if __name__ == '__main__':
    main()
