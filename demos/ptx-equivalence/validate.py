"""GPU/Lean bfi correspondence and independent unpack/equivalence tests.
All GPU activity is serialized with the host-wide advisory lock.
"""
from pathlib import Path
import fcntl, hashlib, json, os, subprocess, sys
import numpy as np
import cupy as cp
D=Path(__file__).resolve().parent
sys.path.insert(0,str(D.parent/'verified-packing'))
from benchmark import uncontended
W=Path(os.environ.get('E5R_DEMO_SCRATCH','/mnt/scratch/e5r-ptx-demo'))/'equivalence'


def bfi(a,b,pos,length):
    out=b
    for i in range(length):
        if pos+i>=32:break
        out=(out&~(1<<(pos+i)))|(((a>>i)&1)<<(pos+i))
    return out


def insertion():
    limits=[0,1,4,14,28,31,32]
    cases=[(p,l) for p in range(33) for l in range(33-p)]
    rng=np.random.default_rng(936)
    values=[0,1,0xffffffff,0x12345678,0xaaaa5555]+[int(x) for x in rng.integers(0,2**32,size=27,dtype=np.uint32)]
    pairs=[(a,b) for a in values for b in values[:5]]
    source='''.version 9.2
.target sm_86
.address_size 64
.visible .entry probe(.param .u64 input, .param .u64 output) {
.reg .b32 %r<6>; .reg .b64 %rd<8>;
ld.param.u64 %rd1,[input]; ld.param.u64 %rd2,[output];
mov.u32 %r1,%tid.x; mul.wide.u32 %rd3,%r1,8;
add.u64 %rd4,%rd1,%rd3; ld.global.u32 %r2,[%rd4]; ld.global.u32 %r3,[%rd4+4];
mul.wide.u32 %rd5,%r1,2244; add.u64 %rd6,%rd2,%rd5;
'''
    for i,(pos,length) in enumerate(cases):
        source+=f'bfi.b32 %r4,%r2,%r3,{pos},{length}; st.global.u32 [%rd6+{4*i}],%r4;\n'
    source+='ret; }\n'
    (W/'bfi-probe.ptx').write_text(source)
    mod=cp.RawModule(path=str(W/'bfi-probe.ptx'))
    x=cp.asarray(np.array(pairs,dtype=np.uint32));y=cp.empty((len(pairs),len(cases)),dtype=np.uint32)
    mod.get_function('probe')((1,),(len(pairs),),(x,y))
    expected=np.array([[bfi(a,b,p,l) for p,l in cases] for a,b in pairs],dtype=np.uint32)
    actual=y.get()
    bad=np.argwhere(actual!=expected)
    if len(bad):
        raise AssertionError([(pairs[i],cases[j],int(actual[i,j]),int(expected[i,j])) for i,j in bad[:15]])
    np.testing.assert_array_equal(actual,expected)
    # Evaluate the actual Lean semantic definition on exactly the same vectors.
    lean='import Ptx.Semantics.Instruction\nopen Ptx\n'
    lean+='def pairs : List (Nat × Nat) := ['+','.join(f'({a},{b})' for a,b in pairs)+']\n'
    lean+='''def reference (a b pos len : Nat) : Nat :=
  (List.range len).foldl (fun out i =>
    (out &&& (4294967295 ^^^ (1 <<< (pos+i)))) |||
      (((a >>> i) &&& 1) <<< (pos+i))) b
#eval (do
  let mut count := 0
  for (a,b) in pairs do
    for pos in List.range 33 do
      for len in List.range (33-pos) do
        let actual := (bfi32 (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) pos len).toNat
        if actual != reference a b pos len then
          throw (IO.userError "bfi semantic mismatch")
        count := count + 1
  IO.println s!"bfi Lean vectors passed: {count}"
  : IO Unit)
'''
    (W/'BfiCheck.lean').write_text(lean)
    run=subprocess.run(['lake','env','lean',str(W/'BfiCheck.lean')],cwd=D.parent.parent/'verification/ptx',text=True,capture_output=True,env={**os.environ,'LEAN_NUM_THREADS':'2'},timeout=180)
    if run.returncode:raise RuntimeError(run.stdout+run.stderr)
    return dict(cases=int(expected.size),lean_output=run.stdout.strip(),probe_sha256=hashlib.sha256(source.encode()).hexdigest())


def kernels():
    modules=[cp.RawModule(path=str(D/(name+'.ptx'))) for name in ('original','optimized')]
    funcs=[m.get_function('unpack4') for m in modules]
    rng=np.random.default_rng(6041);count=0
    for words in [0,1,2,7,8,31,32,33,255,256,257,1024,8193]:
        inputs=[np.zeros(words,dtype=np.uint32),np.full(words,0xffffffff,dtype=np.uint32),
            np.full(words,0x80000001,dtype=np.uint32),rng.integers(0,2**32,size=words,dtype=np.uint32)]
        if words:
            for bit in range(32):inputs.append(np.full(words,1<<bit,dtype=np.uint32))
        for a in inputs:
            x=cp.asarray(a);n=words*8
            expected=np.unpackbits(a.view(np.uint8),bitorder='little')
            for block in [32,128,256]:
                # Extra inactive threads exercise guarded return as well.
                grid=max(1,(n+block-1)//block+1)
                for fn in funcs:
                    storage=cp.full(n*4+32,0xa5,dtype=np.uint8);y=storage[16:-16]
                    if n:fn((grid,),(block,),(x,y,np.uint32(n)))
                    np.testing.assert_array_equal(y.get(),expected)
                    np.testing.assert_array_equal(storage[:16].get(),0xa5)
                    np.testing.assert_array_equal(storage[-16:].get(),0xa5)
                    cp.testing.assert_array_equal(x,cp.asarray(a))
                    count+=1
                uncontended()
    return count


def main():
    W.mkdir(parents=True,exist_ok=True);uncontended()
    result=dict(bfi=insertion(),unpack_program_cases=kernels(),
        ptx_sha256={name:hashlib.sha256((D/(name+'.ptx')).read_bytes()).hexdigest() for name in ('original','optimized')},
        gpu=subprocess.check_output(['nvidia-smi','--query-gpu=name,uuid,driver_version','--format=csv,noheader'],text=True).strip(),
        seed=6041,lock='/mnt/scratch/e5r-gpu-benchmark.lock',foreign_processes_observed=False)
    (D/'results/correctness.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':
    with open('/mnt/scratch/e5r-gpu-benchmark.lock','w') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX);main()
