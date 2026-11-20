/* Recursion and mutual recursion: allowed by the rules; bounding the stack
 * is then a proof obligation. */
typedef unsigned long u64;

u64 fib(u64 n) { return n < 2 ? n : fib(n - 1) + fib(n - 2); }

int is_odd(unsigned n);
__attribute__((noinline)) int is_even(unsigned n) { return n == 0 ? 1 : is_odd(n - 1); }
__attribute__((noinline)) int is_odd(unsigned n) { return n == 0 ? 0 : is_even(n - 1); }

void _start(void) {}
