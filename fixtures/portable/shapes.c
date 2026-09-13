/* Freestanding: builds for any target without a sysroot. Each function pins a
   control-flow shape the analysis has to recover. */

int sum_to(int n) {
    int acc = 0;
    for (int i = 0; i <= n; i++) acc += i;
    return acc;
}

int branchy(int a, int b) {
    if (a > b) return a - b;
    if (a < b) return b - a;
    return 0;
}

/* A dense switch, which compilers turn into a jump table. */
int dense_switch(int n) {
    switch (n) {
    case 0: return 11;
    case 1: return 22;
    case 2: return 33;
    case 3: return 44;
    case 4: return 55;
    case 5: return 66;
    case 6: return 77;
    case 7: return 88;
    default: return -1;
    }
}

/* A sparse switch, which compilers turn into a comparison chain. */
int sparse_switch(int n) {
    switch (n) {
    case 1: return 1;
    case 100: return 2;
    case 10000: return 3;
    case 1000000: return 4;
    default: return 0;
    }
}

static int helper(int x) { return x ^ 0x5a5a5a5a; }

int calls_helper(int x) { return helper(x) + helper(x + 1); }

/* Tail call: the last call reuses the frame, so the callee's entry must not be
   mistaken for a continuation of this function. */
int tail_call(int x) { return sum_to(x); }

int loop_nest(int n) {
    int acc = 0;
    for (int i = 0; i < n; i++)
        for (int j = 0; j < i; j++)
            acc += i * j;
    return acc;
}

int recursive(int n) { return n <= 1 ? 1 : n * recursive(n - 1); }

unsigned long shifts(unsigned long x, int k) {
    return (x << k) | (x >> (64 - k)) | (x & 0xff00ff00ff00ffUL);
}
