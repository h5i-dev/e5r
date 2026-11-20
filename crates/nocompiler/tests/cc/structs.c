/* Struct copies, which clang lowers to memcpy calls: the program supplies a
 * memcpy and memset of its own, and they have to conform too. */
typedef unsigned long u64;

void *memcpy(void *d, const void *s, u64 n) {
  char *dp = d;
  const char *sp = s;
  for (u64 i = 0; i < n; i++)
    dp[i] = sp[i];
  return d;
}

void *memset(void *d, int c, u64 n) {
  char *dp = d;
  for (u64 i = 0; i < n; i++)
    dp[i] = (char)c;
  return d;
}

struct big { u64 a[32]; };

void copy(struct big *d, const struct big *s) { *d = *s; }
void clear(struct big *d) { *d = (struct big){0}; }

void _start(void) {}
