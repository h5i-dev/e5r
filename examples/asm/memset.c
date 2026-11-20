/* The same memset in C, for the comparison in examples/asm/README.md: built
 * with `nocompiler cc -O2` into examples/elf/memset_cc.elf and proved in
 * lean/Examples/MemsetCc.lean against the same specification. */
typedef unsigned long u64;

__attribute__((noinline)) void *memset(void *p, int c, u64 n) {
  unsigned char *q = p;
  while (n--)
    *q++ = (unsigned char)c;
  return p;
}

static unsigned char buf[64];

void _start(void) {
  memset(buf, 'x', sizeof buf);
  for (;;) {
  }
}
