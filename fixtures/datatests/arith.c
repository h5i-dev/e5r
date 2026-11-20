/* Arithmetic and comparison cases, ported from Ghidra's decompiler datatests.
   Most of these pin an algebraic rewrite: the compiler turned a division into a
   reciprocal multiply, or a comparison into a flag expression, and the
   decompiler is expected to turn it back. */

#include "common.h"

/* divopt.xml: unsigned division by constants a compiler turns into a multiply
   by a magic reciprocal and a shift. Ghidra recovers every one of these as a
   division; the constants are the ones its test names. */
NI u32 divu81(u32 x) { return x / 81; }
NI u32 divu89(u32 x) { return x / 89; }
NI u32 divu91(u32 x) { return x / 91; }
NI u32 divu99(u32 x) { return x / 99; }
NI u32 divu101(u32 x) { return x / 101; }
NI u32 divu112(u32 x) { return x / 112; }
NI u32 divu125(u32 x) { return x / 125; }

/* divopt.xml, the signed half: the same rewrite plus a sign correction. */
NI i32 divs81(i32 x) { return x / 81; }
NI i32 divs99(i32 x) { return x / 99; }
NI i32 divs125(i32 x) { return x / 125; }

/* modulo.xml and modulo2.xml: the same reciprocal trick followed by a multiply
   and subtract, which should read as a remainder. */
NI u32 modu10(u32 x) { return x % 10; }
NI u32 modu100(u32 x) { return x % 100; }
NI i32 mods2(i32 x) { return x % 2; }
NI i32 mods3(i32 x) { return x % 3; }
NI i32 mods7(i32 x) { return x % 7; }
NI i32 mods10(i32 x) { return x % 10; }

/* Division by a power of two, which needs no reciprocal: a shift, and for the
   signed case a rounding correction. This is the easy end of divopt.xml and is
   the control for the cases above. */
NI u32 divu8(u32 x) { return x / 8; }
NI i32 divs8(i32 x) { return x / 8; }

/* sbyte.xml: a signed byte compared against constants. The decompiler must not
   reach for `char` just because the load is one byte wide. */
NI void sbyte(const i8 *p) {
    i8 c = *p;
    if (c == 10) sink1(1);
    else if (c == -9) sink2(2);
    else if (c > 0x61) sink3(3);
    else sink4(4);
    keep = c;
}

/* promotecompare.xml: a byte widened before it is compared, where the compare
   is the whole point and the widening is noise. */
NI int promotecompare(const u8 *p) {
    return p[0] - '0' < 9;
}

/* statuscmp.xml and boolless.xml in spirit: a comparison whose result is used
   as a value rather than branched on. It should read as a comparison and not
   as a shift out of a flag word. */
NI int cmpvalue(i64 a, i64 b) {
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

/* lzcount.xml: a count-leading-zeros used as a zero test. */
NI int iszero(u32 x) {
    return x == 0;
}

/* convert.xml: constants of several signs and widths handed to a callee, which
   is where a decompiler decides whether to print them signed. */
NI void convert(void) {
    sink1(256);
    sink2(-512);
    sink3(1000);
    sink4(-3000);
    sink5((int)0xfa56ea00u);
    sink6('a');
    keep = 1;
}

/* floatconv.xml: integer to floating point, in both signednesses. */
NI double i2d(i64 v) { return (double)(v - 0x10) * -0.001; }
NI double u2d(u64 v) { return (double)(v - 0x10) * -0.001; }
NI float i2f(i32 v) { return (float)(v - 0x10) * -0.001f; }

/* floatcast.xml: a float widened to double, computed on, and narrowed back. */
NI float floatcast(float a, float b) {
    double x = (double)a * 1.1234567812345;
    double y = (double)b * 1.12345678;
    return (float)(x - y);
}

/* nan.xml: a self-comparison is a NaN test and should survive; the ordinary
   comparison beside it should not grow one. */
NI void nanfn(double a, double b) {
    sink1(a != a);
    sink2(b < 0.75);
}

/* mixfloatint.xml: a prototype that alternates integer and floating point
   arguments, which is where an ABI model gets the register classes wrong. */
NI double dldlll(double a, int b, double c, int d, int e, int f) {
    return a + b + c + d + e + f;
}

NI int callmixed(int n) {
    keep = (int)dldlll(7.0, n, 8.0, n + 1, n + 2, n + 3);
    return keep;
}

/* statuscmp.xml and sbyte.xml in spirit, reduced to one relation each: the four
   signed orderings against a constant, each arm a different call, so the output
   says without ambiguity which relation it believes the branch tests. */
NI void cmp_gt(int v) { if (v > 5) sink1(v); else sink2(v); keep = v; }
NI void cmp_ge(int v) { if (v >= 5) sink1(v); else sink2(v); keep = v; }
NI void cmp_lt(int v) { if (v < 5) sink1(v); else sink2(v); keep = v; }
NI void cmp_le(int v) { if (v <= 5) sink1(v); else sink2(v); keep = v; }
