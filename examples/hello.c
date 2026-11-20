/* A function that talks to the kernel: write all of a buffer, however the
 * kernel splits it. lean/Examples/Hello.lean proves `write_all` as compiled
 * here: on success the bytes of the `write` events it adds to the trace are
 * exactly the buffer; on an error they are a prefix of it and the error is
 * returned. `hello` writes a message from .rodata through it and exits. */
typedef unsigned long u64;

static long sys3(long nr, long a0, long a1, long a2) {
  register long a7 asm("a7") = nr;
  register long r0 asm("a0") = a0;
  register long r1 asm("a1") = a1;
  register long r2 asm("a2") = a2;
  asm volatile("ecall" : "+r"(r0) : "r"(a7), "r"(r1), "r"(r2) : "memory");
  return r0;
}

__attribute__((noinline)) long write_all(long fd, const char *buf, u64 n) {
  while (n > 0) {
    long r = sys3(64, fd, (long)buf, (long)n);
    if (r < 0)
      return r;
    buf += r;
    n -= (u64)r;
  }
  return 0;
}

static const char msg[] = "nocompiler\n";

/* Not declared noreturn, so the code after the exit ecall is an ordinary
 * return: the profile's rule R2 cannot see that the ecall does not return,
 * and would reject a function whose last instruction is that ecall. The
 * proof shows the return is never reached. */
__attribute__((noinline)) void hello(void) {
  long r = write_all(1, msg, sizeof msg - 1);
  sys3(93, r < 0 ? 1 : 0, 0, 0);
}

void _start(void) { hello(); }
