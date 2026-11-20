/* In-place COBS decode, with the contract of the Rust `cobs` crate's
 * `decode_in_place_report` (the function experiment/.../rmk/Cobs proves on
 * RV32): decode `buf[0, n)`, where n is the index of the first zero byte (or
 * len if there is none), into the front of the same buffer, and report
 *
 *   len = 0          tag 1, a = 0 (empty frame)
 *   invalid frame    tag 1, a = 1, b = bytes decoded before the bad code
 *   success          tag 0, a = source bytes used (n), b = bytes decoded
 *
 * lean/Demo/CobsB.lean and CobsA.lean prove `cobs_decode` as nocompiler cc and
 * as plain clang -march=rv64gc compile it (examples/demo/build.sh).
 * "Target too small", the crate's third error, cannot happen in place: the
 * output never overtakes the input. */
typedef unsigned long u64;
typedef unsigned char u8;

struct cobs_report {
  u64 tag;
  u64 a;
  u64 b;
};

__attribute__((noinline)) void cobs_decode(struct cobs_report *r, u8 *buf, u64 len) {
  if (len == 0) {
    r->tag = 1;
    r->a = 0;
    return;
  }
  u64 n = 0;
  while (n < len && buf[n] != 0)
    n++;
  u64 src = 0, dst = 0;
  while (src < n) {
    u64 code = buf[src];
    if (src + code > n) {
      r->tag = 1;
      r->a = 1;
      r->b = dst;
      return;
    }
    u64 end = src + code;
    src++;
    while (src < end)
      buf[dst++] = buf[src++];
    if (code != 0xff && src < n)
      buf[dst++] = 0;
  }
  r->tag = 0;
  r->a = src;
  r->b = dst;
}
