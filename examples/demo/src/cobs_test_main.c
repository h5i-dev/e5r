/* Test driver: reads records `u64 len; u8 bytes[len]` from stdin until EOF,
 * decodes each in place with cobs_decode, and writes `report (24 bytes);
 * bytes[len]` to stdout. examples/demo/test/cobs_test.py compares it with a reference. */
typedef unsigned long u64;
typedef unsigned char u8;
struct cobs_report { u64 tag, a, b; };
void cobs_decode(struct cobs_report *r, u8 *buf, u64 len);

static long sys3(long nr, long a0, long a1, long a2) {
  register long a7 asm("a7") = nr;
  register long r0 asm("a0") = a0;
  register long r1 asm("a1") = a1;
  register long r2 asm("a2") = a2;
  asm volatile("ecall" : "+r"(r0) : "r"(a7), "r"(r1), "r"(r2) : "memory");
  return r0;
}

static __attribute__((noreturn)) void die(long code) {
  sys3(93, code, 0, 0);
  for (;;) {
  }
}

/* 1: all of it; 0: EOF before the first byte. */
static int read_full(u8 *p, u64 n) {
  u64 got = 0;
  while (got < n) {
    long r = sys3(63, 0, (long)(p + got), (long)(n - got));
    if (r < 0)
      die(2);
    if (r == 0) {
      if (got == 0)
        return 0;
      die(3);
    }
    got += (u64)r;
  }
  return 1;
}

static void write_full(const u8 *p, u64 n) {
  while (n > 0) {
    long r = sys3(64, 1, (long)p, (long)n);
    if (r <= 0)
      die(4);
    p += r;
    n -= (u64)r;
  }
}

static u8 buf[1 << 16];

void _start(void) {
  for (;;) {
    u64 len;
    if (!read_full((u8 *)&len, 8))
      die(0);
    if (len > sizeof buf)
      die(5);
    if (len && !read_full(buf, len))
      die(3);
    struct cobs_report r = {0xaaaaaaaaaaaaaaaaUL, 0xbbbbbbbbbbbbbbbbUL, 0xccccccccccccccccUL};
    cobs_decode(&r, buf, len);
    write_full((const u8 *)&r, sizeof r);
    write_full(buf, len);
  }
}
