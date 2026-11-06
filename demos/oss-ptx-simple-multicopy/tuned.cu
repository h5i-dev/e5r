// Matching comparator, NOT the frozen original or the direct PTX candidate.
// incKernel body from NVIDIA CUDA Samples, BSD-3-Clause (see upstream/LICENSE).
// The sole change is restrict on the two normally disjoint allocations.
__global__ void incKernel(int *__restrict__ g_out, int *__restrict__ g_in, int N, int inner_reps)
{
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < N) {
        for (int i = 0; i < inner_reps; ++i) {
            g_out[idx] = g_in[idx] + 1;
        }
    }
}
