#!/usr/bin/env python3
"""Check supported host subset and separately assembled cubin under the GPU lock."""
import argparse
import json
from pathlib import Path
from gpu import exclusive_gpu, no_foreign


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--scratch',type=Path,default=Path('/mnt/scratch/e5r-ptx-from-spec'))
    parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args()
    with exclusive_gpu(3600):
        import cupy as cp
        import numpy as np
        from endian import endian_xor
        assembled=cp.RawModule(path=str(args.scratch/'endian_xor.cubin')).get_function('endian_xor')
        passed=[]
        stream=cp.cuda.Stream(non_blocking=True)
        with stream:
            for n in [0,1,3,4,31,255,256,257,1025,65537]:
                no_foreign()
                host=(np.arange(n,dtype=np.uint32)*np.uint32(0x01020301))
                x=cp.asarray(host)
                out=cp.empty_like(x)
                ref=host.byteswap() ^ np.uint32(0x87654321)
                assert endian_xor(x,0x87654321,out=out) is out
                stream.synchronize()
                np.testing.assert_array_equal(cp.asnumpy(out),ref)
                allocated=endian_xor(x,0x87654321)
                stream.synchronize()
                np.testing.assert_array_equal(cp.asnumpy(allocated),ref)
                assembled((max(1,(n+255)//256),),(256,),(x,out,np.uint32(n),np.uint32(0x87654321)))
                stream.synchronize()
                np.testing.assert_array_equal(cp.asnumpy(out),ref)
                passed.append(n)
            # Candidate's formal domain requires 4-byte alignment, not uint4 alignment.
            host=np.arange(257,dtype=np.uint32)*np.uint32(0x1020301)
            storage_x=cp.empty(258,dtype=cp.uint32)
            storage_y=cp.empty(258,dtype=cp.uint32)
            x4,y4=storage_x[1:],storage_y[1:]
            assert x4.data.ptr % 16 == 4 and y4.data.ptr % 16 == 4
            x4.set(host,stream=stream)
            endian_xor(x4,0x87654321,out=y4)
            stream.synchronize()
            np.testing.assert_array_equal(cp.asnumpy(y4),host.byteswap() ^ np.uint32(0x87654321))
            assembled((2,),(256,),(x4,y4,np.uint32(257),np.uint32(0x87654321)))
            stream.synchronize()
            np.testing.assert_array_equal(cp.asnumpy(y4),host.byteswap() ^ np.uint32(0x87654321))
            x=cp.arange(16,dtype=cp.uint32)
            invalid=[('inplace',lambda:endian_xor(x,1,out=x)),
                     ('overlap',lambda:endian_xor(x[:8],1,out=x[4:12])),
                     ('stride',lambda:endian_xor(x[::2],1)),
                     ('misaligned',lambda:endian_xor(cp.ndarray((4,),cp.uint32,memptr=x.data+1),1)),
                     ('signed',lambda:endian_xor(x.view(cp.int32),1)),
                     ('multidim',lambda:endian_xor(x.reshape(4,4),1)),
                     ('mask_fractional',lambda:endian_xor(x,1.5)),
                     ('mask_negative',lambda:endian_xor(x,-1)),
                     ('mask_overflow',lambda:endian_xor(x,2**32)),
                     ('wrong_out_shape',lambda:endian_xor(x,1,out=cp.empty(8,dtype=cp.uint32)))]
            rejected=[]
            for name,f in invalid:
                try: f()
                except ValueError: rejected.append(name)
                else: raise AssertionError(name)
            stream.synchronize()
        no_foreign()
    data={'schema':'e5r.endian.wrapper.v1','wrapper_and_ptxas_cubin_lengths':passed,
          'invalid_calls_rejected':rejected,'non_default_stream':True,'four_byte_not_sixteen_byte_alignment':True,'passed':True}
    args.out.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(data))

if __name__=='__main__': main()
