"""Independent mathematical byte reference, adversarial and CuPy differential tests."""
import fcntl, json, hashlib, os, subprocess
from pathlib import Path
import numpy as np
import cupy as cp
from runtime import Packing, D

def reference(op,x):
    if op=='unpack':
        return np.array([(int(b)//(2**k))%2 for b in x for k in range(8)],dtype=np.uint8)
    return np.array([sum((int(x[j+k])>127 if op=='threshold' else int(x[j+k])!=0)*2**k
        for k in range(8)) for j in range(0,len(x),8)],dtype=np.uint8)

def tests():
    from benchmark import uncontended
    uncontended()
    rt=Packing();rng=np.random.default_rng(6041);cases=0
    # Every byte value, every single-bit position, alternating, extrema,
    # random, and every valid boundary around one thread block.
    for op in rt.kernels:
        unit=4 if op=='unpack' else 32
        arrays=[np.full(unit*8,v,dtype=np.uint8) for v in (0,1,2,127,128,129,254,255)]
        arrays += [np.arange(256,dtype=np.uint8),np.tile(np.array([0,255],dtype=np.uint8),128)]
        for k in range(unit*8):
            a=np.zeros(unit*8,dtype=np.uint8);a[k]=1 if op!='threshold' else 128;arrays.append(a)
        arrays += [rng.integers(0,256,size=unit*n,dtype=np.uint8) for n in (0,1,2,31,32,33,255,256,257,1025)]
        for a in arrays:
            uncontended()
            x=cp.asarray(a); y=cp.full(a.size*8 if op=='unpack' else a.size//8,0xa5,dtype=cp.uint8)
            rt.run(op,x,y)
            expected=reference(op,a)
            np.testing.assert_array_equal(cp.asnumpy(y),expected)
            oss=cp.unpackbits(x,bitorder='little') if op=='unpack' else cp.packbits(x>127 if op=='threshold' else x,bitorder='little')
            np.testing.assert_array_equal(cp.asnumpy(oss),expected);cases+=1
    for op in rt.kernels:
        unit=4 if op=='unpack' else 32
        try: rt.run(op,cp.zeros(unit+1,dtype=cp.uint8),cp.empty(1,dtype=cp.uint8))
        except ValueError: pass
        else: raise AssertionError('tail accepted')
    cp.cuda.get_current_stream().synchronize()
    return {'cases':cases,'seed':6041,'correctness':'passed','cupy':cp.__version__,
        'ptx_sha256':{op:hashlib.sha256((D/f'{op}.ptx').read_bytes()).hexdigest() for op in rt.kernels},
        'lock':'/mnt/scratch/e5r-gpu-benchmark.lock','foreign_processes_observed':False}

if __name__=='__main__':
    with open('/mnt/scratch/e5r-gpu-benchmark.lock','w') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        result=tests();print(json.dumps(result,indent=2));(D/'results/correctness.json').write_text(json.dumps(result,indent=2)+'\n')
