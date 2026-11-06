"""CUDA driver harness, initializes only while holding the shared GPU lock."""
import ctypes as c
import fcntl
import subprocess
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
