/* The three things M10 says emulation is for, plus a run that must not finish.

   Freestanding and static, so the same source runs natively on this machine
   and under qemu for the other architecture. `_start` records every answer the
   processor computed; the emulation tests compare against that recording
   rather than against the emulator itself. */

typedef unsigned char u8;
typedef unsigned int u32;
typedef unsigned long u64;

#define NI __attribute__((noinline))

/* Volatile so a store to it survives the optimizer and a case arm cannot be
   folded into its neighbour. */
volatile u64 keep;

/* ---- the raw system call, which is also what the stubs are measured on ---- */

static long sys3(long n, long a, long b, long c) {
#if defined(__x86_64__)
    long r;
    __asm__ volatile("syscall"
                     : "=a"(r)
                     : "a"(n), "D"(a), "S"(b), "d"(c)
                     : "rcx", "r11", "memory");
    return r;
#elif defined(__aarch64__)
    register long x8 __asm__("x8") = n;
    register long x0 __asm__("x0") = a;
    register long x1 __asm__("x1") = b;
    register long x2 __asm__("x2") = c;
    __asm__ volatile("svc #0" : "+r"(x0) : "r"(x8), "r"(x1), "r"(x2) : "memory");
    return x0;
#else
    (void)n; (void)a; (void)b; (void)c;
    return -1;
#endif
}

#if defined(__x86_64__)
#define SYS_read 0
#define SYS_write 1
#define SYS_exit 60
#else
#define SYS_read 63
#define SYS_write 64
#define SYS_exit 93
#endif

/* Emulated, never run natively: the point is what the stub answers. */
NI u64 shout(const u8 *p, u64 n) { return (u64)sys3(SYS_write, 1, (long)p, (long)n); }
NI u64 slurp(u8 *p, u64 n) { return (u64)sys3(SYS_read, 0, (long)p, (long)n); }

/* A number no kernel here implements, so the stub table must refuse it by
   number rather than invent a return value. */
NI u64 unmodelled(void) { return (u64)sys3(424242, 0, 0, 0); }

/* ---- 1. string decryption ---- */

/* Ciphertext, in writable data so nothing folds it into the decryption. The
   key rolls with the ciphertext, so no entry of the table means anything on
   its own: the routine has to run for the plaintext to exist at all. */
u8 cipher[27] = {
    0x2e, 0x25, 0x21, 0x60, 0x14, 0x56, 0x0c, 0x0b, 0x58, 0x18, 0x5b, 0x16, 0x46, 0x45,
    0x13, 0x5b, 0x0e, 0x45, 0x44, 0x17, 0x5e, 0x18, 0x17, 0x42, 0x04, 0x5b, 0x0e,
};

NI u64 decrypt(u8 *dst) {
    u8 k = 0x5a;
    u32 i;
    for (i = 0; i < sizeof cipher; i++) {
        u8 c = cipher[i];
        dst[i] = (u8)(c ^ k);
        k = (u8)(c + 0x1f);
    }
    dst[i] = 0;
    return i;
}

/* ---- 2. obfuscated control flow ---- */

NI u64 step_a(u64 x) { return x + 11; }
NI u64 step_b(u64 x) { return x * 3; }
NI u64 step_c(u64 x) { return x ^ 0x5a5a; }

#define MASK 0x00c0ffee00c0ffeeUL

/* The dispatch table is masked and built on the stack, so the image says
   nothing about where the branch goes, and the index is computed from the
   argument. Only running it settles either. */
NI u64 dispatch(u64 seed) {
    volatile u64 enc[3];
    u64 i;
    u64 (*fn)(u64);
    enc[0] = (u64)(void *)step_a ^ MASK;
    enc[1] = (u64)(void *)step_b ^ MASK;
    enc[2] = (u64)(void *)step_c ^ MASK;
    i = seed % 3;
    fn = (u64 (*)(u64))(enc[i] ^ MASK);
    return fn(seed);
}

/* ---- 3. jump tables ---- */

NI u64 case0(u64 x) { return x + 0x10; }
NI u64 case1(u64 x) { return x + 0x21; }
NI u64 case2(u64 x) { return x * 0x32; }
NI u64 case3(u64 x) { return x ^ 0x43; }
NI u64 case4(u64 x) { return x - 0x54; }
NI u64 case5(u64 x) { return x | 0x65; }
NI u64 case6(u64 x) { return x & 0x76; }
NI u64 case7(u64 x) { return x + 0x87; }
NI u64 case8(u64 x) { return x * 0x98; }
NI u64 case9(u64 x) { return x ^ 0xa9; }
NI u64 case10(u64 x) { return x - 0xba; }

/* Eleven cases. The table that follows it in the image has seven, and a scan
   that is not bounded by the guard runs straight from one into the other:
   every entry of the second is a plausible target for the first. */
NI u64 pick(u64 n, u64 x) {
    switch (n) {
    case 0: return case0(x);
    case 1: return case1(x);
    case 2: return case2(x);
    case 3: return case3(x);
    case 4: return case4(x);
    case 5: return case5(x);
    case 6: return case6(x);
    case 7: return case7(x);
    case 8: return case8(x);
    case 9: return case9(x);
    case 10: return case10(x);
    }
    return 0xdead;
}

NI u64 pick2(u64 n, u64 x) {
    switch (n) {
    case 0: return case0(x) + 1;
    case 1: return case1(x) + 2;
    case 2: return case2(x) + 3;
    case 3: return case3(x) + 4;
    case 4: return case4(x) + 5;
    case 5: return case5(x) + 6;
    case 6: return case6(x) + 7;
    }
    return 0xbeef;
}

/* ---- 4. a run that does not finish ---- */

/* Never called natively. The budget is the only thing that ends it, and a test
   that could not tell that from a return would not be testing anything. */
NI u64 forever(u64 x) {
    for (;;) keep = keep + x + 1;
}

/* ---- the recording ---- */

static void emit(u64 v) {
    u8 buf[8];
    int i;
    for (i = 0; i < 8; i++) buf[i] = (u8)(v >> (i * 8));
    sys3(SYS_write, 1, (long)buf, 8);
}

void _start(void) {
    u8 plain[32];
    u64 i;
    emit(decrypt(plain));
    for (i = 0; i < 11; i++) emit(pick(i, 3));
    for (i = 0; i < 7; i++) emit(pick2(i, 3));
    for (i = 0; i < 6; i++) emit(dispatch(i));
    sys3(SYS_write, 1, (long)plain, 27);
    sys3(SYS_exit, 0, 0, 0);
    for (;;) {}
}
