"""Resolve auipc+jalr / jal call targets in an llvm-objdump -d listing and count
call sites of Rust panic entry points per calling function (RMK recon, untrusted
evidence, not a proof). Original e5r code, Apache-2.0.
Usage: panic_sites.py LISTING.dis
"""
import re,sys,collections
D=sys.argv[1]
syms={}; func=None; owner={}
last_auipc={}
calls=collections.defaultdict(list)
for l in open(D):
    m=re.match(r'^([0-9a-f]+) <(.*)>:$',l)
    if m: syms[int(m[1],16)]=m[2]; func=m[2]; last_auipc={}; continue
    m=re.match(r'^([0-9a-f]+):\s+[0-9a-f]+\s+\t(\S+)\t?(.*)$',l.rstrip('\n'))
    if not m: continue
    a=int(m[1],16); op=m[2]; args=m[3]
    if op=='auipc':
        r,imm=[x.strip() for x in args.split(',')]
        last_auipc[r]=(a,int(imm,0)<<12); continue
    t=None
    m2=re.match(r'(?:ra, )?(-?0x[0-9a-f]+|-?\d+)\((\w+)\)',args) if op in('jalr','jr') else None
    if m2 and m2[2] in last_auipc:
        base,hi=last_auipc[m2[2]]; t=(base+hi+int(m2[1],0))&0xffffffff
    elif op in ('jal','j','call','tail'):
        m3=re.search(r'0x([0-9a-f]+)',args)
        if m3: t=int(m3[1],16)
    if t is not None: calls[t].append((a,func))
targets=[a for a,n in syms.items() if re.search(r'panic|unwrap_failed|expect_failed|slice_index_fail|rust_begin_unwind|assert_failed',n)]
for t in sorted(targets):
    fs=collections.Counter(f for _,f in calls[t])
    print(hex(t), syms[t][-60:], len(calls[t]), 'sites in', len(fs), 'fns')
print('rust_begin_unwind callers:', [ (hex(a),f[-50:]) for a,f in calls[[a for a,n in syms.items() if 'rust_begin_unwind' in n][0]]][:5])
for key in ('panic_bounds_check','slice_index_fail','div_by_zero','rem_by_zero','unwrap_failed','expect_failed'):
    for t in [a for a,n in syms.items() if key in n]:
        print('==',key)
        for f,c in collections.Counter(f for _,f in calls[t]).most_common(): print('  ',c, f[:150])
