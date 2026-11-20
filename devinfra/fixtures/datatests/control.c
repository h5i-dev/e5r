/* Loops, conditionals and switches, ported from Ghidra's decompiler datatests.
   Each function is the smallest C that makes a compiler emit the shape the
   original datatest pinned. Nothing is inlined and no arm of a ladder repeats
   another, because a compiler that can fold two arms together emits a bit test
   instead of the branch the case is about. */

#include "common.h"

/* forloop1.xml: a counted loop. */
NI void forloop1(int max) {
    int i;
    for (i = 0; i < max; i++) sink(i);
    keep = max;
}

/* forloop_varused.xml: the loop variable is read inside the body. */
NI void forloop_varused(unsigned max) {
    unsigned i;
    for (i = 0; i < max; i++) {
        if ((i & 3) == 0) sink((int)i);
    }
    keep = (int)max;
}

/* forloop_withskip.xml: the body may bump the loop variable again. */
NI void forloop_withskip(int n) {
    int i;
    for (i = 0; i < n; i++) {
        if (source() > 10) i++;
    }
    keep = n;
}

/* noforloop_globcall.xml: the loop variable is a global a call can change. */
NI void noforloop_globcall(void) {
    for (counter = 0; counter < 10; counter++) sink(1);
    keep = counter;
}

/* noforloop_iterused.xml: the loop variable outlives the loop. */
NI void noforloop_iterused(unsigned max) {
    unsigned i = 10;
    while (i < max) {
        sink((int)i);
        i++;
        counter = (int)(i * 100);
    }
    keep = (int)i;
}

/* copytrim.xml: a loop that counts down to zero. */
NI void countdown(int n) {
    int i;
    for (i = n; i != 0; i = i - 1) sink(i);
    keep = n;
}

/* Nested counted loops: the inner loop must nest inside the outer one. */
NI void nested(int n, int m) {
    int i, j;
    for (i = 0; i < n; i++)
        for (j = 0; j < m; j++) sink(i * j);
    keep = n + m;
}

/* ifnoexit.xml: a loop body whose early exits are returns. */
NI int ifnoexit(const int *ptr, const int *end) {
    int r = 0;
    while (ptr != end) {
        int v = *ptr++;
        if (v == 100) return 1;
        if (v == 200) return 2;
        if (v != 300) r += v;
    }
    return r;
}

/* elseif.xml: a chain that should read as one if/else ladder. Six distinct
   calls, so no two arms are the same code and the ladder survives. */
NI void elseif(int a, int b) {
    if (a == 0) sink1(a);
    else if (a == 1) sink2(b);
    else if (b == 11) sink3(a + b);
    else if (b == 21) sink4(a - b);
    else if (b == 31) sink5(a * b);
    else sink6(a ^ b);
    keep = a + b;
}

/* orcompare.xml: two comparisons joined by a short-circuit or. */
NI void orcompare(int a, int b) {
    if (a == 10 || b == 20) sink1(a);
    else sink2(b);
    keep = a;
}

NI void orcompare3(int x, int y, int z) {
    if (y == 200 || x == 100 || z == 300) sink3(x);
    else sink4(y);
    keep = x;
}

/* ccmp.xml: two comparisons joined by a short-circuit and, which AArch64
   compiles to one ccmp and x86-64 to a pair of branches. */
NI void andcompare(const int *p, int val) {
    if (p[1] == 0x3c && val < 10) sink5(val);
    else sink6(val);
    keep = val;
}

/* switchind.xml: a dense switch, which every compiler emits as a jump table.
   The case bodies differ so nothing folds them into arithmetic. */
NI int switchind(int v) {
    switch (v) {
    case 0: sink1(0); return 10;
    case 1: return 11 * keep;
    case 2: sink2(99); sink3(4); return 12;
    case 3: return keep ^ 0x2b;
    case 4: sink4(7); return keep - 3;
    case 5: return 15;
    case 6: sink5(6); sink6(5); sink1(4); return keep | 0x40;
    case 7: return keep + 0x4d;
    case 8: return 18;
    case 9: sink2(1); return keep << 3;
    case 10: return 20;
    default: return -1;
    }
}

/* switchloop.xml: a switch whose cases all update the same loop variable. */
NI int switchloop(int n) {
    int s = 0;
    int i;
    for (i = 0; i < n; i++) {
        switch (i & 15) {
        case 0: s += 2; break;
        case 1: s *= 2; break;
        case 2: s += 100; break;
        case 3: s -= 17; break;
        case 4: s += 1000; break;
        case 5: s += 10000; break;
        case 6: s ^= 0x87; break;
        case 7: s += 8; break;
        case 8: s -= 3; break;
        case 9: s |= 0x20; break;
        case 10: s &= 0x7f; break;
        case 11: s <<= 1; break;
        default: s += 1; break;
        }
    }
    return s;
}

/* ifswitch.xml: a switch nested in an if that tests the same variable. */
NI int ifswitch(int p) {
    if (p > 99) return p * 1000;
    if (p > 20) return p - 13;
    switch (p) {
    case 0: return 10;
    case 1:
    case 10: return 6;
    case 2: return p * 4;
    case 3: sink1(3); return p - 13;
    case 4: return keep + 1;
    case 5: sink2(5); sink3(6); return keep;
    case 6: return p * 7;
    case 7: return keep - 9;
    case 8: return p + 0x20;
    case 9: sink4(9); return 0x30;
    default: return p + -13;
    }
}

/* multiret.xml: values of three widths flowing into one return. This used to
   hang Ghidra, so the property is that it terminates and returns something. */
NI long multiret(int p) {
    char c = 'a';
    short s = 1001;
    long r = c;
    r += s;
    r += p;
    return r;
}

/* condconst.xml: a value known to be constant on the path that uses it. Both
   arms write to the same place, and only one of them writes a constant. */
NI void condconst(int a, int *ptr) {
    int x;
    if (a == 0) x = 10;
    else x = source();
    ptr[2] = x;
    if (a == 1) counter = 0;
    else counter = a;
    keep = x;
}

/* condmulti.xml: a conditional constant reaching a join along two paths. */
NI void condmulti(int a, int b) {
    int x = 10;
    if (a > 0) {
        if (b > 0) sink1(1);
        else sink2(2);
    } else {
        x = a;
        sink3(3);
    }
    counter = x;
}
