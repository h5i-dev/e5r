#!/usr/bin/env python3
"""Exact full-TU FP4 kernels: adversarial differential and randomized graph timing."""
import argparse, ctypes as c, hashlib, json, math, os, random, statistics, time
from pathlib import Path
import numpy as np
HERE=Path(__file__).resolve().parent
ap=argparse.ArgumentParser(); ap.add_argument('--output',type=Path,required=True); ap.add_argument('--samples',type=int,default=21)
ap.add_argument('--input-offset',type=int,choices=[0,1],default=0)
args=ap.parse_args()
# The imported harness takes flock and checks foreign compute PIDs before cuInit.
import driver as d
from driver import ptr,u64,stream
scratch=Path(os.environ.get('FP4_SCRATCH','/mnt/scratch/e5r-oss-ptx/int4/fp4-sign'))
build=json.loads((HERE/'build.json').read_text())
rng=np.random.default_rng(616886); order_rng=random.Random(616886)
variants={}; modules=[]
for impl in ['original','edited','cuda']:
    module=ptr(); d.load(c.byref(module),os.fsencode(scratch/(impl+'.cubin'))); modules.append(module)
    for row in build['rows']:
        if row['implementation']!=impl: continue
        fn=ptr(); d.function(c.byref(fn),module,row['symbol'].encode()); variants[impl,row['variant']]=fn
mag=np.array([0,0x3baaaaab,0x3f2aaaab,0x3f800000,0x3eaaaaab,0x3f000000,0x3e2aaaab,0x3e800000],dtype=np.uint32)
allocation_bases={}
def alloc(size,offset=0):
    p=u64(); d.allocate(c.byref(p),size+offset)
    shifted=u64(p.value+offset); allocation_bases[shifted.value]=p
    return shifted
def free(p): d.free(allocation_bases.pop(p.value))

def upload(p,a): d.upload(p,a.ctypes.data,a.nbytes)

def reference(packed,scales,n,bs,kind):
    codes=np.empty(packed.size*2,dtype=np.uint32); codes[0::2]=packed>>4; codes[1::2]=packed&15; codes=codes[:n]
    signed=(mag[codes&7]|((codes&8)<<28)).view(np.float32)
    scale=scales[np.arange(n)//bs].copy(); bits=scale.view(np.uint32)
    bits[(bits&0x7f800000)==0]&=np.uint32(0x80000000)
    with np.errstate(all='ignore'): product=(signed*scale).astype(np.float32)
    bits=product.view(np.uint32); bits[(bits&0x7f800000)==0]&=np.uint32(0x80000000)
    if kind=='fp4-fp32': return bits.tobytes()
    if kind=='fp4-fp16':
        with np.errstate(all='ignore'): return product.astype(np.float16).tobytes()
    # RN-even BF16 (NaN payloads separately checked as NaNs).
    rounded=((bits.astype(np.uint64)+0x7fff+((bits>>16)&1))>>16).astype(np.uint16)
    rounded[np.isnan(product)]=0x7fff
    return rounded.tobytes()

def nan_mask(raw,kind):
    ty=np.uint32 if kind=='fp4-fp32' else np.uint16
    x=np.frombuffer(raw,dtype=ty)
    exp,frac=(0x7f800000,0x7fffff) if kind=='fp4-fp32' else ((0x7c00,0x3ff) if kind=='fp4-fp16' else (0x7f80,0x7f))
    return ((x&exp)==exp)&((x&frac)!=0)

def setup(n,bs,kind,exceptional=False,slots=1):
    packed=rng.integers(0,256,(n+1)//2,dtype=np.uint8)
    if packed.size>=256: packed[:256]=np.arange(256,dtype=np.uint8)
    # All 64 threads read their scale, including lanes beyond the logical tail.
    ns=math.ceil(n/1024)*1024//bs+2
    if exceptional:
        patterns=np.array([0,0x80000000,1,0x80000001,0x007fffff,0x00800000,0x3f800000,0xbf800000,0x7f7fffff,0xff7fffff,0x7f800000,0xff800000,0x7fc00000,0x7f800001,0xffc12345],dtype=np.uint32)
        scales=np.resize(patterns,ns).view(np.float32).copy()
    else: scales=rng.uniform(0.01,4,ns).astype(np.float32)
    width=4 if kind=='fp4-fp32' else 2
    inp=alloc(packed.nbytes,args.input_offset); scale=alloc(scales.nbytes)
    upload(inp,packed); upload(scale,scales)
    outputs=[alloc(n*width+128) for _ in range(slots)]
    return packed,scales,inp,scale,outputs,width

def launch(fn,n,bs,inp,scale,out):
    code=u64(0); target=u64(out.value+64); block=c.c_int(bs//2); length=c.c_int(n)
    params=(ptr*6)(*[c.cast(c.byref(v),ptr) for v in [code,inp,scale,target,block,length]])
    d.launch(fn,math.ceil(n/1024),1,1,64,1,1,0,stream,params,None)

result={'schema':1,'seed':616886,'proof':'none; standalone finite-table lemma is separate',
 'gpu':d.subprocess.check_output(['nvidia-smi','--query-gpu=name,driver_version,temperature.gpu,clocks.sm,clocks.mem','--format=csv,noheader'],text=True).strip(),
 'input_byte_offset':args.input_offset,'gpu_lock':'exclusive /mnt/scratch/e5r-gpu-benchmark.lock; foreign compute PIDs refused before cuInit',
 'predeclared':{'outputs':[4096,65536,1048576,16777216],'blocksizes':[64,4096],'dtypes':['fp4-fp32','fp4-fp16','fp4-bf16'],'modes':['hot','rotating'],'samples':args.samples,'graph_launches':32,'warmup_graphs':5,'success':'at least 5% median speedup at two adjacent representative sizes without material regression; exact differential; direct proof required for accepted win'},
 'validation':[],'rows':[]}
for kind in result['predeclared']['dtypes']:
    for bs in [32,64,128,256,512,1024,2048,4096]:
        for n in [1,2,3,31,32,33,63,64,65,511,512,513,1023,1024,1025,4095,16385]:
            packed,scales,inp,scale,outputs,width=setup(n,bs,kind,True)
            out=outputs[0]; expected=reference(packed,scales,n,bs,kind); baseline=None
            for impl in ['original','edited','cuda']:
                d.memset(out,0xa5,n*width+128); launch(variants[impl,kind],n,bs,inp,scale,out); d.sync(stream)
                host=c.create_string_buffer(n*width+128); d.download(host,out,len(host)); raw=host.raw
                assert raw[:64]==b'\xa5'*64 and raw[-64:]==b'\xa5'*64,(impl,kind,n,bs,'canary')
                actual=raw[64:-64]
                if baseline is None: baseline=actual
                assert actual==baseline,(impl,kind,n,bs,'bit differential')
                dtype=np.uint32 if width==4 else np.uint16
                av=np.frombuffer(actual,dtype=dtype); ev=np.frombuffer(expected,dtype=dtype)
                assert np.all((av==ev)|(nan_mask(actual,kind)&nan_mask(expected,kind))),(impl,kind,n,bs,'CPU')
            # Inputs and scales are read-only, including bytes around the logical tail.
            input_after=np.empty_like(packed); scale_after=np.empty_like(scales)
            d.download(input_after.ctypes.data,inp,input_after.nbytes); d.download(scale_after.ctypes.data,scale,scale_after.nbytes)
            assert input_after.tobytes()==packed.tobytes() and scale_after.tobytes()==scales.tobytes()
            result['validation'].append({'dtype':kind,'n':n,'blocksize':bs,'differential':'bit-exact all 3','CPU':'all finite bits and signed zeros; NaNs by class','canaries':'both 64-byte pass','sha256':hashlib.sha256(baseline).hexdigest()})
            for p in [inp,scale,*outputs]: free(p)
    print('validated',kind,flush=True)
args.output.write_text(json.dumps(result,indent=2)+'\n')
for kind in result['predeclared']['dtypes']:
 for bs in result['predeclared']['blocksizes']:
  for n in result['predeclared']['outputs']:
   for mode in result['predeclared']['modes']:
    # 16 distinct buffers at small sizes, four at large sizes. Small rotating
    # cases can still fit in L2; record footprint rather than calling all cold.
    slots=1 if mode=='hot' else (16 if n<=1048576 else 4)
    packed,scales,inp,scale,outputs,width=setup(n,bs,kind,slots=slots)
    graphs={}
    for impl in ['original','edited','cuda']:
        graph,executable=ptr(),ptr(); d.begin(stream,0)
        for i in range(32): launch(variants[impl,kind],n,bs,inp,scale,outputs[i%slots])
        d.end(stream,c.byref(graph)); d.instantiate(c.byref(executable),graph,0); graphs[impl]=(graph,executable)
        for _ in range(5): d.graph_launch(executable,stream)
        d.sync(stream)
    times={impl:[] for impl in graphs}; orders=[]
    for _ in range(args.samples):
        order=list(graphs); order_rng.shuffle(order); orders.append(order)
        for impl in order:
            d.record(d.events[0],stream); d.graph_launch(graphs[impl][1],stream); d.record(d.events[1],stream); d.event_sync(d.events[1])
            ms=c.c_float(); d.elapsed(c.byref(ms),*d.events); times[impl].append(ms.value*1000/32)
    row={'dtype':kind,'blocksize':bs,'n':n,'mode':mode,'output_slots':slots,'footprint_bytes':slots*n*width+packed.nbytes+scales.nbytes,'samples_us':times,'order':orders,'median_us':{k:statistics.median(v) for k,v in times.items()}}
    row['normal_over_edited']=row['median_us']['original']/row['median_us']['edited']; row['normal_over_cuda']=row['median_us']['original']/row['median_us']['cuda']
    result['rows'].append(row); args.output.write_text(json.dumps(result,indent=2)+'\n'); print(kind,bs,n,mode,round(row['normal_over_edited'],3),round(row['normal_over_cuda'],3),flush=True)
    for g,e in graphs.values(): d.exec_destroy(e); d.graph_destroy(g)
    for p in [inp,scale,*outputs]: free(p)
result['completed_utc']=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()); args.output.write_text(json.dumps(result,indent=2)+'\n')
