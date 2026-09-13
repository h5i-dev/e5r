/* Freestanding, and deliberately varied: every function here exists to make a
   compiler emit a different corner of the instruction set. */

typedef unsigned char u8;
typedef unsigned short u16;
typedef unsigned int u32;
typedef unsigned long u64;
typedef signed char i8;
typedef short i16;
typedef int i32;
typedef long i64;

u8 arith8(u8 a, u8 b) { return (u8)(a + b * 3 - (a & b) + (a | b) + (a ^ b)); }
u16 arith16(u16 a, u16 b) { return (u16)(a * b + (a >> 3) - (b << 2)); }
u32 arith32(u32 a, u32 b) { return a * b + (a / (b | 1)) + (a % (b | 1)); }
u64 arith64(u64 a, u64 b) { return a * b + (a / (b | 1)) + (a % (b | 1)); }
i32 sarith32(i32 a, i32 b) { return a * b + (a / (b | 1)) + (a % (b | 1)); }
i64 sarith64(i64 a, i64 b) { return a * b + (a / (b | 1)) + (a % (b | 1)); }

u64 widen(u8 a, u16 b, u32 c) { return (u64)a + b + c; }
i64 sign_widen(i8 a, i16 b, i32 c) { return (i64)a + b + c; }

u64 rotate(u64 x, int k) { return (x << (k & 63)) | (x >> ((64 - k) & 63)); }
u32 bits(u32 x) { return (x & 0xff00ff) | ((x >> 8) & 0xff) | (x << 24); }

int compares(i64 a, i64 b) {
    int r = 0;
    if (a == b) r += 1;
    if (a != b) r += 2;
    if (a < b) r += 4;
    if (a <= b) r += 8;
    if (a > b) r += 16;
    if (a >= b) r += 32;
    if ((u64)a < (u64)b) r += 64;
    return r;
}

int select_chain(int a, int b, int c) {
    int x = a > b ? a : b;
    int y = x > c ? x : c;
    return y < 0 ? -y : y;
}

long dense(int n) {
    switch (n) {
    case 0: return 0x1111;
    case 1: return 0x2222;
    case 2: return 0x3333;
    case 3: return 0x4444;
    case 4: return 0x5555;
    case 5: return 0x6666;
    case 6: return 0x7777;
    case 7: return 0x8888;
    case 8: return 0x9999;
    case 9: return 0xaaaa;
    case 10: return 0xbbbb;
    case 11: return 0xcccc;
    default: return -1;
    }
}

struct Point {
    i32 x, y;
    i64 tag;
};

i64 use_struct(struct Point *p, int n) {
    i64 acc = 0;
    for (int i = 0; i < n; i++) {
        acc += p[i].x * (i64)p[i].y + p[i].tag;
    }
    return acc;
}

void fill(u8 *dst, u8 v, u64 n) {
    for (u64 i = 0; i < n; i++) dst[i] = v;
}

void copy(u8 *dst, const u8 *src, u64 n) {
    for (u64 i = 0; i < n; i++) dst[i] = src[i];
}

u64 sum_array(const u64 *a, u64 n) {
    u64 s = 0;
    for (u64 i = 0; i < n; i++) s += a[i];
    return s;
}

i32 dot(const i32 *a, const i32 *b, u64 n) {
    i32 s = 0;
    for (u64 i = 0; i < n; i++) s += a[i] * b[i];
    return s;
}

double fmath(double a, double b) {
    double c = a * b + a / (b + 1.0);
    return c > 0.0 ? c - a : c + b;
}

float fmath32(float a, float b) {
    float c = a * b - a / (b + 1.0f);
    return c < 0.0f ? -c : c;
}

i64 f2i(double a) { return (i64)a; }
double i2f(i64 a) { return (double)a; }
float d2f(double a) { return (float)a; }
double f2d(float a) { return (double)a; }

typedef int (*fnptr)(int);
int call_through(fnptr f, int x) { return f(x) + f(x + 1); }

int nested(int n) {
    int acc = 0;
    for (int i = 0; i < n; i++)
        for (int j = i; j < n; j++)
            for (int k = j; k < n; k++)
                acc += i ^ j ^ k;
    return acc;
}

u64 collatz(u64 n) {
    u64 steps = 0;
    while (n != 1) {
        n = (n & 1) ? 3 * n + 1 : n / 2;
        steps++;
    }
    return steps;
}

int strcmp_like(const char *a, const char *b) {
    while (*a && *a == *b) { a++; b++; }
    return (int)(u8)*a - (int)(u8)*b;
}

u64 strlen_like(const char *s) {
    const char *p = s;
    while (*p) p++;
    return (u64)(p - s);
}

static u64 table[64];
u64 indexed(u64 i) { return table[i & 63] + table[(i >> 6) & 63]; }
void store_indexed(u64 i, u64 v) { table[i & 63] = v; }

u64 many_args(u64 a, u64 b, u64 c, u64 d, u64 e, u64 f, u64 g, u64 h) {
    return a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6 + g * 7 + h * 8;
}

i64 deep_recursion(i64 n) { return n <= 1 ? 1 : n * deep_recursion(n - 1) + deep_recursion(n - 2); }
