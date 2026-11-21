/* Linux-layer probe: each modelled syscall on concrete inputs; prints
   "name result" lines (results as signed decimals). Freestanding, rv64. */
typedef unsigned long u64;
typedef long i64;
static i64 sc(i64 n, i64 a, i64 b, i64 c, i64 d, i64 e, i64 f) {
  register i64 a0 __asm__("a0") = a; register i64 a1 __asm__("a1") = b;
  register i64 a2 __asm__("a2") = c; register i64 a3 __asm__("a3") = d;
  register i64 a4 __asm__("a4") = e; register i64 a5 __asm__("a5") = f;
  register i64 a7 __asm__("a7") = n;
  __asm__ volatile("ecall" : "+r"(a0) : "r"(a1), "r"(a2), "r"(a3), "r"(a4), "r"(a5), "r"(a7) : "memory");
  return a0;
}
static void out(const char *s, int n) { sc(64, 1, (i64)s, n, 0, 0, 0); }
static int len(const char *s) { int n = 0; while (s[n]) n++; return n; }
static void put(const char *name, i64 v) {
  char b[32]; int i = 31; int neg = v < 0; u64 u = neg ? -(u64)v : (u64)v;
  b[i--] = '\n';
  do { b[i--] = '0' + u % 10; u /= 10; } while (u);
  if (neg) b[i--] = '-';
  out(name, len(name)); out(" ", 1); out(b + i + 1, 31 - i);
}
static void putbytes(const char *name, const char *p, int n) {
  out(name, len(name)); out(" ", 1); out(p, n); out("\n", 1);
}
struct iov { void *base; u64 len; };
static char buf[64], b1[8], b2[8], st[128];
void main_(u64 *sp) {
  const char *file = (const char *)sp[2];
  i64 fd = sc(56, -100, (i64)file, 0, 0, 0, 0);       put("openat", fd);
  put("read4", sc(63, fd, (i64)buf, 4, 0, 0, 0));      putbytes("read4.bytes", buf, 4);
  put("lseek.cur0", sc(62, fd, 0, 1, 0, 0, 0));
  put("lseek.end-2", sc(62, fd, -2, 2, 0, 0, 0));
  put("lseek.data2", sc(62, fd, 2, 3, 0, 0, 0));
  put("lseek.hole2", sc(62, fd, 2, 4, 0, 0, 0));
  put("lseek.data6", sc(62, fd, 6, 3, 0, 0, 0));
  put("lseek.whence5", sc(62, fd, 0, 5, 0, 0, 0));
  put("lseek.set-1", sc(62, fd, -1, 0, 0, 0, 0));
  put("lseek.set0", sc(62, fd, 0, 0, 0, 0, 0));
  struct iov v[2] = {{b1, 2}, {b2, 3}};
  put("readv23", sc(65, fd, (i64)v, 2, 0, 0, 0));      putbytes("readv.b1", b1, 2); putbytes("readv.b2", b2, 3);
  put("read10", sc(63, fd, (i64)buf, 10, 0, 0, 0));    putbytes("read10.bytes", buf, 1);
  put("read.eof", sc(63, fd, (i64)buf, 10, 0, 0, 0));
  put("fstat", sc(80, fd, (i64)st, 0, 0, 0, 0));       put("fstat.size", *(i64 *)(st + 48));
  put("openat.missing", sc(56, -100, (i64)"/nonexistent-nc-probe", 0, 0, 0, 0));
  put("close", sc(57, fd, 0, 0, 0, 0, 0));
  put("close.again", sc(57, fd, 0, 0, 0, 0, 0));
  put("read.closed", sc(63, fd, (i64)buf, 1, 0, 0, 0));
  put("lseek.closed", sc(62, fd, 0, 0, 0, 0, 0));
  put("fstat.closed", sc(80, fd, (i64)st, 0, 0, 0, 0));
  put("readv.1025", sc(65, 0, (i64)v, 1025, 0, 0, 0));
  put("reopen", sc(56, -100, (i64)file, 0, 0, 0, 0));
  /* emulated by qemu-user, not passed to the host kernel */
  put("mprotect.unaligned", sc(226, 0x1001, 4096, 1, 0, 0, 0));
  put("munmap.unaligned", sc(215, 0x1001, 4096, 0, 0, 0, 0));
  sc(94, 0, 0, 0, 0, 0, 0);
}
__asm__(".globl _start\n_start:\n  mv a0, sp\n  call main_\n");
