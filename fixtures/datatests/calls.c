/* Call and prototype cases, ported from Ghidra's decompiler datatests. What
   each pins is that the shape of a call survives: an indirect call that turns
   out to have one target, a callee whose arguments are known, and a return
   value that does not fit one register. */

#include "common.h"

struct pair {
    int a;
    int b;
};

struct big {
    long a;
    long b;
    long c;
};

typedef int (*intfn)(int);
typedef struct pair (*pairfn)(int);

struct table {
    intfn peek;
    intfn get;
};

NI int realfunc(int x) { return x * 3 + 1; }
NI int otherfunc(int x) { return x - 7; }

intfn chosen = realfunc;

/* deindirect.xml: two indirect calls that share one argument setup and both
   collapse to the same direct call. */
NI int deindirect(int b, int c) {
    intfn f = chosen;
    int r = f(b + 3);
    r += f(c + 5);
    return r;
}

/* indproto.xml: two indirect calls through fields of one structure, which get
   their prototype from the field type rather than from the call site. */
NI int indproto(struct table *ptr, int a) {
    return ptr->peek(a) + ptr->get(a);
}

/* deindirect2.xml: an indirect call whose return value is wider than one
   register's worth of the caller's use, so the pieces have to be put back. */
NI long deindirect2(long *nm) {
    long *p = (long *)(void *)nm;
    return *p == 0 ? 0 : *p;
}

/* retstruct.xml: a structure returned in two registers. */
NI struct pair retpair(int x) {
    struct pair r;
    r.a = x * 100;
    r.b = 0x1e;
    return r;
}

NI int usepair(int x) {
    struct pair p = retpair(x);
    return p.a + p.b;
}

/* retspecial.xml: a structure too big for registers, returned through a hidden
   pointer the caller supplies. */
NI struct big returnbig(int num) {
    struct big r;
    r.a = 10;
    r.b = 100;
    r.c = num;
    return r;
}

NI long usebig(int num) {
    struct big b = returnbig(num);
    return b.c;
}

/* stackspill.xml: more integer arguments than there are argument registers, so
   the tail of the list arrives on the stack. */
NI int manyargs(int a, int b, int c, int d, int e, int f, int g, int h, int i) {
    return a + b + c + d + e + f + g + h + i;
}

NI int callmany(int n) {
    return manyargs(n, n + 1, n + 2, n + 3, n + 4, n + 5, n + 6, n + 7, n + 8);
}

/* stackcorner.xml, the parameter half: a stack parameter reached only through
   its address, which is what stops it being recovered as a register argument. */
NI int paramnodirect(int a, int b, int c, int d, int e, int f, int g) {
    sink(a + b + c + d + e + f);
    return g;
}

/* inline.xml: a callee small enough that a decompiler is tempted to inline it,
   and a caller that must still show the call. */
NI int add50(int a) { return a + 50; }

NI int callsadd50(int a) {
    keep = add50(a);
    return add50(a + 100);
}

/* overridedest.xml: a call whose target is computed, next to one that is not,
   so the two are distinguishable in the output. */
NI int mixedcalls(int a) {
    intfn f = chosen;
    int r = otherfunc(a);
    r += f(a);
    return r;
}

/* switchreturn.xml: a tail call, which is a branch out of the function. The
   call has to survive even though the function does not return normally. */
NI int tailcall(int a) {
    return realfunc(a + 1);
}
