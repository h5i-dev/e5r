#!/usr/bin/env python3
"""Driver-launch exact full-cubin Q4_K entry; no E5R proof is implied."""
import argparse
import ctypes as c
import fcntl
import hashlib
import json
import os
import pathlib
import statistics
import struct
import subprocess
import time

ap = argparse.ArgumentParser()
ap.add_argument('--artifacts', type=pathlib.Path, required=True)
ap.add_argument('--output', type=pathlib.Path, required=True)
args = ap.parse_args()
lock = open('/mnt/scratch/e5r-gpu-benchmark.lock', 'a')
fcntl.flock(lock, fcntl.LOCK_EX)
foreign = subprocess.check_output(['nvidia-smi', '--query-compute-apps=pid,process_name,used_memory',
                                   '--format=csv,noheader,nounits'], text=True).strip()
if foreign:
    raise SystemExit('Refusing GPU work: existing compute process(es): ' + foreign)

cu = c.CDLL('libcuda.so.1')
u64 = c.c_uint64
ptr = c.c_void_p


def api(name, types):
    f = getattr(cu, name)
    f.argtypes = types
    f.restype = c.c_int
    def call(*values):
        result = f(*values)
        if result:
            raise RuntimeError(f'{name}: CUDA error {result}')
    return call


init = api('cuInit', [c.c_uint])
primary = api('cuDevicePrimaryCtxRetain', [c.POINTER(ptr), c.c_int])
current = api('cuCtxSetCurrent', [ptr])
load = api('cuModuleLoad', [c.POINTER(ptr), c.c_char_p])
function = api('cuModuleGetFunction', [c.POINTER(ptr), ptr, c.c_char_p])
allocate = api('cuMemAlloc_v2', [c.POINTER(u64), c.c_size_t])
free = api('cuMemFree_v2', [u64])
upload = api('cuMemcpyHtoD_v2', [u64, ptr, c.c_size_t])
download = api('cuMemcpyDtoH_v2', [ptr, u64, c.c_size_t])
memset = api('cuMemsetD8_v2', [u64, c.c_ubyte, c.c_size_t])
stream_create = api('cuStreamCreate', [c.POINTER(ptr), c.c_uint])
sync = api('cuStreamSynchronize', [ptr])
launch = api('cuLaunchKernel', [ptr, c.c_uint, c.c_uint, c.c_uint, c.c_uint, c.c_uint,
                              c.c_uint, c.c_uint, ptr, c.POINTER(ptr), ptr])
begin = api('cuStreamBeginCapture_v2', [ptr, c.c_int])
end = api('cuStreamEndCapture', [ptr, c.POINTER(ptr)])
instantiate = api('cuGraphInstantiateWithFlags', [c.POINTER(ptr), ptr, c.c_ulonglong])
graph_launch = api('cuGraphLaunch', [ptr, ptr])
graph_destroy = api('cuGraphDestroy', [ptr])
exec_destroy = api('cuGraphExecDestroy', [ptr])
event_create = api('cuEventCreate', [c.POINTER(ptr), c.c_uint])
record = api('cuEventRecord', [ptr, ptr])
event_sync = api('cuEventSynchronize', [ptr])
elapsed = api('cuEventElapsedTime', [c.POINTER(c.c_float), ptr, ptr])
init(0)
context = ptr()
primary(c.byref(context), 0)
current(context)
stream = ptr()
stream_create(c.byref(stream), 1)
events = [ptr(), ptr()]
for event in events:
    event_create(c.byref(event), 0)
variants = {}
for name, file in [('normal', 'llama/convert.sm_86.cubin'),
                   ('intrinsic', 'llama-intrinsic/convert.sm_86.cubin'),
                   ('inline', 'llama-inline/convert.sm_86.cubin'),
                   ('edited', 'llama-edited/convert.cubin')]:
    module, fn = ptr(), ptr()
    load(c.byref(module), os.fsencode(args.artifacts / file))
    function(c.byref(fn), module, b'_Z21dequantize_block_q4_KIfEvPKvPT_')
    variants[name] = (module, fn)

# Finite exact binary scales, exhaustive nibble values and scale boundary bits.
scales = bytes([0, 63, 1, 62, 32, 31, 16, 47, 0, 255, 15, 240])
quants = bytes((i * 37 + 19) & 255 for i in range(128))
block = struct.pack('<ee', 0.5, 0.25) + scales + quants
reference = []
def decode_scale(j):
    if j < 4:
        return scales[j] & 63, scales[j + 4] & 63
    return ((scales[j + 4] & 15) | ((scales[j - 4] >> 6) << 4),
            (scales[j + 4] >> 4) | ((scales[j] >> 6) << 4))
for group in range(4):
    d1, m1 = decode_scale(2 * group)
    d2, m2 = decode_scale(2 * group + 1)
    q = quants[32 * group:32 * group + 32]
    reference += [0.5 * d1 * (x & 15) - 0.25 * m1 for x in q]
    reference += [0.5 * d2 * (x >> 4) - 0.25 * m2 for x in q]
expected_block = struct.pack('<256f', *reference)
result = {'schema': 1, 'kind': 'exploratory execution and hot-cache CUDA graph timing',
          'proof': 'none', 'gpu': subprocess.check_output(['nvidia-smi', '--query-gpu=name,driver_version',
                     '--format=csv,noheader'], text=True).strip(),
          'shapes_predeclared': [16, 256, 4096, 65536], 'launch': 'grid=(nb,1,1),block=(32,1,1)',
          'input': 'repeated Q4_K block; finite binary scale0.5/min0.25, nibble and scale boundaries',
          'repetitions_per_graph': 32, 'warmup_graphs': 5, 'samples': 15,
          'metric': 'CUDA event elapsed milliseconds / 32; graph construction and transfers excluded',
          'rows': []}
for nb in result['shapes_predeclared']:
    source_bytes, output_bytes = block * nb, 1024 * nb
    source_buffer = c.create_string_buffer(source_bytes)
    host_output = c.create_string_buffer(output_bytes + 64)
    device_input, device_output = u64(), u64()
    allocate(c.byref(device_input), len(source_bytes))
    allocate(c.byref(device_output), output_bytes + 64)
    upload(device_input, source_buffer, len(source_bytes))
    parameters = (ptr * 2)(c.cast(c.byref(device_input), ptr), c.cast(c.byref(device_output), ptr))
    graphs = {}
    baseline_hash = None
    for name, (_, fn) in variants.items():
        memset(device_output, 0xA5, output_bytes + 64)
        launch(fn, nb, 1, 1, 32, 1, 1, 0, stream, parameters, None)
        sync(stream)
        download(host_output, device_output, output_bytes + 64)
        actual = host_output.raw
        assert actual[output_bytes:] == bytes([0xA5]) * 64, (name, nb, 'canary')
        # Verify every output block against a separately decoded CPU reference.
        assert actual[:output_bytes] == expected_block * nb, (name, nb, 'CPU reference')
        output_hash = hashlib.sha256(actual[:output_bytes]).hexdigest()
        if baseline_hash is None:
            baseline_hash = output_hash
        assert output_hash == baseline_hash
        graph, executable = ptr(), ptr()
        begin(stream, 0)
        for _ in range(32):
            launch(fn, nb, 1, 1, 32, 1, 1, 0, stream, parameters, None)
        end(stream, c.byref(graph))
        instantiate(c.byref(executable), graph, 0)
        graphs[name] = (graph, executable)
        for _ in range(5):
            graph_launch(executable, stream)
        sync(stream)
    times = {name: [] for name in variants}
    for sample in range(15):
        # Rotate order to avoid permanently favoring one variant.
        order = list(variants)
        order = order[sample % 4:] + order[:sample % 4]
        for name in order:
            record(events[0], stream)
            graph_launch(graphs[name][1], stream)
            record(events[1], stream)
            event_sync(events[1])
            milliseconds = c.c_float()
            elapsed(c.byref(milliseconds), events[0], events[1])
            times[name].append(milliseconds.value * 1000 / 32)
    for name, samples in times.items():
        row = {'nb': nb, 'values': nb * 256, 'variant': name, 'microseconds': samples,
               'median_us': statistics.median(samples), 'min_us': min(samples),
               'max_us': max(samples), 'output_sha256': baseline_hash, 'canary': 'pass',
               'CPU_reference': 'every element pass'}
        result['rows'].append(row)
        print(nb, name, round(row['median_us'], 4), flush=True)
    for graph, executable in graphs.values():
        exec_destroy(executable)
        graph_destroy(graph)
    free(device_input)
    free(device_output)
result['completed_utc'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
args.output.write_text(json.dumps(result, indent=2) + '\n')
