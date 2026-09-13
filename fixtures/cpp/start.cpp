// A freestanding entry point, so the C++ fixture links without a runtime and
// can be executed as its own oracle.

extern "C" long run_shapes();

static void emit(unsigned long v) {
    unsigned char buf[8];
    for (int i = 0; i < 8; i++) buf[i] = (unsigned char)(v >> (i * 8));
#if defined(__x86_64__)
    __asm__ volatile("syscall" : : "a"(1l), "D"(1l), "S"(buf), "d"(8l) : "rcx", "r11", "memory");
#elif defined(__aarch64__)
    register long x8 __asm__("x8") = 64;
    register long x0 __asm__("x0") = 1;
    register const void *x1 __asm__("x1") = buf;
    register long x2 __asm__("x2") = 8;
    __asm__ volatile("svc #0" : : "r"(x8), "r"(x0), "r"(x1), "r"(x2) : "memory");
#endif
}

extern "C" void _start() {
    emit((unsigned long)run_shapes());
#if defined(__x86_64__)
    __asm__ volatile("syscall" : : "a"(60l), "D"(0l) : "rcx", "r11");
#elif defined(__aarch64__)
    register long x8 __asm__("x8") = 93;
    register long x0 __asm__("x0") = 0;
    __asm__ volatile("svc #0" : : "r"(x8), "r"(x0));
#endif
    __builtin_unreachable();
}
