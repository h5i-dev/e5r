/* Functions with frames, for the v1 frame rule R6 (docs/isa/v1.md): saves,
 * spills, address-taken locals and arrays passed to callees, structs on the
 * stack, calls in loops, variadic functions, and the two shapes that are
 * outside L2 on purpose (a variable-length array, more than eight
 * arguments). Each function is noinline so it keeps its own frame. */
typedef unsigned long u64;
typedef long i64;
#define NI __attribute__((noinline))

NI u64 leaf_add(u64 a, u64 b) { return a + b; }
NI void fill(u64 *p, u64 n, u64 v) {
  for (u64 i = 0; i < n; i++)
    p[i] = v + i;
}
NI u64 sum_arr(const u64 *p, u64 n) {
  u64 s = 0;
  for (u64 i = 0; i < n; i++)
    s += p[i];
  return s;
}
NI void set_one(u64 *p) { *p = 1; }
NI void set_int(int *p, int v) { *p = v; }

/* Callee-saved registers across a call. */
NI u64 keep_across(u64 a, u64 b, u64 c) {
  u64 x = leaf_add(a, b);
  return x + leaf_add(b, c) + a + c;
}

/* A call in a loop: the loop state lives in saved registers. */
NI u64 call_in_loop(const u64 *p, u64 n) {
  u64 s = 0;
  for (u64 i = 0; i < n; i++)
    s = leaf_add(s, p[i]);
  return s;
}

/* An address-taken scalar passed to a callee and read after it. */
NI u64 addr_scalar(u64 a) {
  u64 x = a;
  set_one(&x);
  return x + a;
}

/* An address-taken 32-bit local. */
NI int addr_int(int a) {
  int x;
  set_int(&x, a);
  return x * 2;
}

/* A local array filled and summed by callees. */
NI u64 local_array(u64 v) {
  u64 a[8];
  fill(a, 8, v);
  return sum_arr(a, 8);
}

/* Two arrays and a scalar, all address-taken. */
NI u64 two_arrays(u64 v) {
  u64 a[4], b[6];
  u64 x = v;
  fill(a, 4, v);
  fill(b, 6, v + 1);
  set_one(&x);
  return sum_arr(a, 4) + sum_arr(b, 6) + x;
}

struct pt {
  i64 x, y, z;
};
NI void move(struct pt *p, i64 d) {
  p->x += d;
  p->y -= d;
  p->z ^= d;
}
/* A struct on the stack, passed by pointer. */
NI i64 struct_local(i64 a) {
  struct pt p = {a, 2 * a, 3 * a};
  move(&p, 5);
  return p.x + p.y + p.z;
}

/* Many live values across a call: spills or many saves. */
NI u64 many_live(u64 a, u64 b, u64 c, u64 d, u64 e, u64 f) {
  u64 x1 = a * 3, x2 = b * 5, x3 = c * 7, x4 = d * 11, x5 = e * 13, x6 = f * 17;
  u64 y = leaf_add(x1, x2);
  u64 x7 = x3 ^ x4, x8 = x5 + x6, x9 = x1 - x6, x10 = x2 | x5, x11 = x3 & x4, x12 = y + 1;
  u64 z = leaf_add(y, x7);
  return x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 + x12 + y + z;
}

/* Two calls whose results are combined. */
NI u64 two_calls(const u64 *p, u64 n, const u64 *q, u64 m) { return sum_arr(p, n) + sum_arr(q, m); }

/* A tail call with a frame before it. */
NI u64 tail_after_frame(u64 a) {
  u64 x = a;
  set_one(&x);
  return leaf_add(x, a);
}

/* Eight arguments: still all in registers. */
NI u64 eight_args(u64 a, u64 b, u64 c, u64 d, u64 e, u64 f, u64 g, u64 h) {
  return a + 2 * b + 3 * c + 4 * d + 5 * e + 6 * f + 7 * g + 8 * h;
}
NI u64 calls_eight(u64 v) { return eight_args(v, v + 1, v + 2, v + 3, v + 4, v + 5, v + 6, v + 7) + 1; }

/* Nine arguments: the ninth is on the stack (outside L2, 6c). */
NI u64 nine_args(u64 a, u64 b, u64 c, u64 d, u64 e, u64 f, u64 g, u64 h, u64 i) {
  return a + b + c + d + e + f + g + h + 9 * i;
}
NI u64 calls_nine(u64 v) { return nine_args(v, v, v, v, v, v, v, v, v + 1) + 1; }

/* A variable-length array (outside L2: R5). */
NI u64 vla(u64 n, u64 v) {
  u64 a[n];
  fill(a, n, v);
  return sum_arr(a, n);
}

/* A recursive function: frames on every level. */
NI u64 fact(u64 n) { return n <= 1 ? 1 : n * fact(n - 1); }

/* A byte buffer on the stack, accessed directly and by a callee. */
NI void bump(unsigned char *p, u64 n) {
  for (u64 i = 0; i < n; i++)
    p[i]++;
}
NI u64 byte_buf(u64 v) {
  unsigned char b[16];
  for (int i = 0; i < 16; i++)
    b[i] = (unsigned char)(v >> (i & 7));
  bump(b, 16);
  u64 s = 0;
  for (int i = 0; i < 16; i++)
    s += b[i];
  return s;
}

/* A loop with a call and an early return. */
NI i64 find_first(const u64 *p, u64 n, u64 key) {
  for (u64 i = 0; i < n; i++)
    if (leaf_add(p[i], 0) == key)
      return (i64)i;
  return -1;
}

/* Saved registers restored on two return paths. */
NI u64 two_exits(u64 a, u64 b) {
  if (a > b)
    return leaf_add(a, b) * a;
  return leaf_add(b, a) * b;
}

/* A struct returned through memory (sret). */
struct big3 {
  u64 a, b, c;
};
NI struct big3 make3(u64 v) { return (struct big3){v, v + 1, v + 2}; }
NI u64 use3(u64 v) {
  struct big3 t = make3(v);
  return t.a + t.b + t.c;
}

void _start(void) {
  u64 a[4] = {1, 2, 3, 4};
  u64 r = keep_across(1, 2, 3) + call_in_loop(a, 4) + addr_scalar(5) + (u64)addr_int(6) + local_array(7) +
          two_arrays(8) + (u64)struct_local(9) + many_live(1, 2, 3, 4, 5, 6) + two_calls(a, 4, a, 2) +
          tail_after_frame(3) + calls_eight(1) + calls_nine(2) + vla(4, 1) + fact(5) + byte_buf(3) +
          (u64)find_first(a, 4, 3) + two_exits(4, 5) + use3(2);
  register long a0 asm("a0") = (long)(r & 1);
  register long a7 asm("a7") = 93;
  asm volatile("ecall" : : "r"(a0), "r"(a7));
  for (;;) {
  }
}
