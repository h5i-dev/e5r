import subprocess, sys, os, re
src = open('Projects/rmk/Uart/SendRound.lean', encoding='utf-8').read()
S = sys.argv[1]
cases = [
  ("sp-sesspre", "  sp : 0x8002a7f4 + 0x50 ≤ (m.core.get 2).toNat", "  sp : 0x8002a798 + 0x70 ≤ (m.core.get 2).toNat", "send_bytes' frame may overlap the slots"),
  ("len-zero", "  len : 1 ≤ (m.core.get 11).toNat", "  len : 0 ≤ (m.core.get 11).toNat", "empty response: the len=0 panic at 0x800042b4"),
  ("stride-2", "  stride : (m.ram (uOf m.ram + 0x00000020#32)).toNat = 1", "  stride : (m.ram (uOf m.ram + 0x00000020#32)).toNat = 2", "UART register stride 2: send_bytes' SendEnv"),
  ("struct-in-slots", "  selfSlots : (uOf m.ram).toNat + 0x21 ≤ 0x8002a7c4 ∨ 0x8002a7f1 ≤ (uOf m.ram).toNat", "  selfSlots : True", "the loop's slot stores may overwrite the UART struct"),
  ("outer-len", "  outer : ramRead m.ram 0x8002a7cc .w = m.core.get 11", "  outer : True", "the outer slice length unknown: slice panic 0x800042d0 / remaining != 0"),
  ("q-no-yield", "     (m.core.pc = 0x8001e14a ∧ m.core.get 1 = 0x80004324", "     (False ∧ m.core.get 1 = 0x80004324", "SendQ without the yield boundary (send_bytes may return 0)"),
]
for name, old, new, why in cases:
    assert src.count(old) == 1, name
    p = os.path.join(S, f"M_{name.replace('-', '_')}.lean")
    open(p, 'w', encoding='utf-8').write(src.replace(old, new))
    r = subprocess.run(['lean', p], capture_output=True, text=True, env={**os.environ, 'LEAN_PATH': '.'}, timeout=1500)
    errs = [l for l in (r.stdout + r.stderr).splitlines() if ': error' in l]
    first = errs[0] if errs else ''
    m = re.search(r':(\d+):\d+: error', first)
    thm = '?'
    if m:
        lines = open(p, encoding='utf-8').read().splitlines()[:int(m.group(1))]
        thm = next((re.match(r'theorem (\S+)', l).group(1) for l in reversed(lines) if l.startswith('theorem ')), '?')
    verdict = 'rejected' if r.returncode != 0 and errs and 'unknown' not in first.lower() else ('PROVED (control FAILED)' if r.returncode == 0 else 'tool/other')
    print(f"{name}: {verdict} first error in {thm} | {why} | {first.split('error:',1)[-1].strip()[:120]}", flush=True)
# baseline: unmodified copy must check
p = os.path.join(S, 'M_baseline.lean'); open(p, 'w', encoding='utf-8').write(src)
r = subprocess.run(['lean', p], capture_output=True, text=True, env={**os.environ, 'LEAN_PATH': '.'}, timeout=1500)
print('baseline:', 'proved' if r.returncode == 0 else 'FAILED', flush=True)
