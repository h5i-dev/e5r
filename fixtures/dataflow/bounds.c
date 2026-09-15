/* Calls whose argument bounds are known by construction, for the dataflow
   query gate.

   Each wrapper holds exactly one call and the answer for its length argument
   is decided by the source rather than by what an analysis happens to manage:
   a literal, a length a comparison guards, a length a mask narrows, a length
   read straight out of memory, and a length that arrives from the caller. The
   last two are the pair the feature exists for. They are both "not bounded"
   and they are not the same claim.

   Freestanding and -fno-builtin, so `memcpy` here is this file's own function
   and a call to it is a call to a named symbol rather than to a libc the link
   does not have. Every wrapper ends by touching a volatile, which is what
   stops the compiler turning the call into a tail call and taking the call
   site with it. */

/* `noclone` as well as `noinline`: a compiler that sees one call site with a
   constant argument otherwise emits a specialized copy under another name, and
   the call is then to that name rather than to the one the query asks about. */
#define NI __attribute__((noinline, noclone))

typedef unsigned long usize;

volatile int keep;
/* A length the program reads rather than computes: nothing in the code
   constrains what memory holds here. */
volatile usize untrusted;

static char dst[512];
static char src[512];
static char command[64];

NI void *memcpy(void *d, const void *s, usize n) {
    char *a = (char *)d;
    const char *b = (const char *)s;
    for (usize i = 0; i < n; i++) a[i] = b[i];
    return d;
}

NI char *strcpy(char *d, const char *s) {
    char *out = d;
    while ((*d++ = *s++) != 0) {
    }
    return out;
}

NI int system(const char *cmd) {
    keep += cmd[0];
    return 0;
}

/* Bounded: the length is in the instruction. */
NI void copy_literal_length(void) {
    memcpy(dst, src, 32);
    keep++;
}

/* Bounded: the comparison that guards the call bounds it. */
NI void copy_checked_length(usize n) {
    if (n > 64) {
        return;
    }
    memcpy(dst, src, n);
    keep++;
}

/* Bounded: a mask cannot produce a bit the mask does not have. */
NI void copy_masked_length(void) {
    memcpy(dst, src, untrusted & 63);
    keep++;
}

/* Unbounded, and provably so: read from memory, nothing between. */
NI void copy_untrusted_length(void) {
    memcpy(dst, src, untrusted);
    keep++;
}

/* Not known to be bounded: the length is this function's own argument, and
   what the callers pass is not visible from here. */
NI void copy_argument_length(usize n) {
    memcpy(dst, src, n);
    keep++;
}

static void *(*volatile copy_through)(void *, const void *, usize) = memcpy;

/* The same copy through a function pointer: an indirect call. */
NI void copy_through_pointer(void) {
    copy_through(dst, src, untrusted);
    keep++;
}

NI void copy_string(void) {
    strcpy(dst, src);
    keep++;
}

/* A command the program builds itself.

   The string is a writable global rather than a literal, so that the argument
   is still a constant address while the compiler can make nothing of what is
   behind it: passing a literal to a function that reads it is exactly what
   makes a compiler emit a specialized copy of that function and call that
   instead, which would move the call site out from under the query. */
static char fixed_command[] = "/bin/echo hi";

NI void run_fixed(void) {
    system(fixed_command);
    keep++;
}

/* A command that arrives from outside this function. */
NI void run_from_input(const char *cmd) {
    system(cmd);
    keep++;
}

void _start(void) {
    copy_literal_length();
    copy_checked_length(untrusted);
    copy_masked_length();
    copy_untrusted_length();
    copy_argument_length(untrusted);
    copy_through_pointer();
    copy_string();
    run_fixed();
    run_from_input(command);
    for (;;) {
    }
}
