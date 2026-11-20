/* A call through a function pointer: an indirect jalr, outside version 0 of
 * the profile (rule R2). */
static int sq(int x) { return x * x; }
__attribute__((noinline)) int apply(int (*f)(int), int x) { return f(x); }
int use(int x) { return apply(sq, x); }
void _start(void) {}
