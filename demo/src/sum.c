/* The first nocompiler examples: the sum of an array of 64-bit words, and a caller.
 * lean/Examples/Sum.lean proves `sum` correct, memory-safe and terminating
 * as compiled here, and lean/Examples/Sum2.lean proves `sum2` from `sum`'s
 * specification alone. examples/build.sh builds it, and `_start` lets it run
 * under qemu-riscv64 (the exit status is the result modulo 256). */
typedef unsigned long u64;

/* noinline: `sum2` is about calling a verified function, not inlining it. */
__attribute__((noinline)) u64 sum(const u64 *a, u64 n) {
  u64 s = 0;
  for (u64 i = 0; i < n; i++)
    s += a[i];
  return s;
}

u64 sum2(const u64 *a, u64 n, const u64 *b, u64 m) {
  return sum(a, n) + sum(b, m);
}

static long sys1(long nr, long a0) {
  register long a7 asm("a7") = nr;
  register long r0 asm("a0") = a0;
  asm volatile("ecall" : "+r"(r0) : "r"(a7) : "memory");
  return r0;
}

u64 data[5] = {1, 2, 3, 4, 5};

void _start(void) {
  sys1(93, (long)sum2(data, 5, data + 1, 3));
}
