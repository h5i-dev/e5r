#!/usr/bin/env python3
"""Freeze cuDF source and attempt unchanged-TU and normal configuration; no GPU."""
import hashlib,json,os,subprocess,tarfile
from pathlib import Path
HERE=Path(__file__).resolve().parent
SCRATCH=Path('/mnt/scratch/e5r-oss-ptx/int4')
UP=SCRATCH/'cudf'; RMM=SCRATCH/'rmm'; OUT=SCRATCH/'cudf-build'
PIN='d71b3b743ca6fc9d8d4b1718d845eec4bc63dee6'
def run(cmd):
 p=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 return p.returncode,p.stdout
assert run(['git','-C',str(UP),'rev-parse','HEAD'])[1].decode().strip()==PIN
paths=['LICENSE','cpp/CMakeLists.txt','cpp/src/io/parquet/decode_fixed.cu','cpp/src/io/parquet/rle_stream.cuh','cpp/src/io/parquet/parquet_gpu.hpp','cpp/src/io/parquet/page_data.cuh','cpp/cmake/thirdparty/get_cccl.cmake','cpp/cmake/thirdparty/get_rmm.cmake']
evidence=HERE/'evidence';evidence.mkdir(exist_ok=True)
with tarfile.open(evidence/'sources.tar.gz','w:gz') as tar:
 for path in paths: tar.add(UP/path,arcname=path)
flags=['/usr/local/cuda/bin/nvcc','-std=c++20','-O3','-DNDEBUG','-arch=sm_86','--threads','1','-ptx','-I',str(RMM/'cpp/include'),'-I',str(UP/'cpp/include'),'-I',str(UP/'cpp/src'),str(UP/'cpp/src/io/parquet/decode_fixed.cu'),'-o',str(OUT/'decode_fixed.ptx')]
normal=['cmake','-S',str(UP/'cpp'),'-B',str(OUT/'normal'),'-DCMAKE_CUDA_ARCHITECTURES=86','-DCMAKE_BUILD_TYPE=Release','-DBUILD_TESTS=OFF','-DBUILD_BENCHMARKS=OFF','-DCUDF_BUILD_TESTUTIL=OFF','-DCMAKE_EXPORT_COMPILE_COMMANDS=ON']
results=[]
for name,cmd in [('normal-cmake',normal),('unchanged-tu',flags)]:
 code,data=run(cmd);(evidence/(name+'.log')).write_bytes(data)
 results.append({'name':name,'command':cmd,'returncode':code,'log_sha256':hashlib.sha256(data).hexdigest()})
rmm_evidence={}
for source,target in [('LICENSE','RMM.LICENSE'),('cpp/include/rmm/detail/export.hpp','rmm-export.hpp'),('cpp/CMakeLists.txt','rmm-CMakeLists.txt')]:
 data=(RMM/source).read_bytes();(evidence/target).write_bytes(data)
 rmm_evidence[target]=hashlib.sha256(data).hexdigest()
x={'rmm_selected_evidence_sha256':rmm_evidence,'repository':'https://github.com/rapidsai/cudf','commit':PIN,'license':'Apache-2.0',
 'source_hashes':{p:hashlib.sha256((UP/p).read_bytes()).hexdigest() for p in paths},
 'rmm_attempt_pin':run(['git','-C',str(RMM),'rev-parse','HEAD'])[1].decode().strip(),
 'normal_kernel':'decode_page_data_generic in cpp/src/io/parquet/decode_fixed.cu; actual host template launches retained',
 'lead':'cross-word integer extraction; existing __funnelshift_r in page_data.cuh, existing guarded unaligned 32-bit literal path in rle_stream.cuh',
 'commands':results,'frozen_normal_build':False,'direct_edit':False,'gpu_executed':False,'accepted_proof':False,
 'status':'incomplete compiler screen, dependency/configuration rejection; source inspection establishes existing techniques only; no production performance conclusion'}
(HERE/'result.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x,indent=2))
