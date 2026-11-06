// Independently authored specialization comparator. Not the direct-edit candidate.
struct A { int* p; long size,shape,stride; }; struct B {unsigned char* p;long size,shape,stride;};struct I {long size,shape,index;};
#define LOOP for(long i=long(blockIdx.x)*blockDim.x+threadIdx.x;i<idx.size;i+=long(blockDim.x)*gridDim.x)
extern "C" __global__ void cupy_tri(int m,int k,A out,I idx){LOOP out.p[i]=(int(i%256)<=int(i/256)+k);}
extern "C" __global__ void cupy_resize(A x,long size,A out,I idx){LOOP out.p[i]=x.p[i&255];}
extern "C" __global__ void cupy_putmask_kernel(B mask,A vals,unsigned long size,A out,I idx){LOOP if(mask.p[i])out.p[i]=vals.p[i&255];}
extern "C" __global__ void cupy_flatiter_setitem_slice(A vals,long start,long step,A out,I idx){LOOP out.p[start+i*step]=vals.p[i&255];}
extern "C" __global__ void cupy_flatiter_getitem_slice(A x,long start,long step,A out,I idx){LOOP out.p[i]=x.p[start+i];}
