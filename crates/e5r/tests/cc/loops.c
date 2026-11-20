/* Loops in the shapes C programs use: nested, with break, continue, goto
 * out of two loops, do-while, early return from a loop body. */
typedef unsigned long u64;

int nested(int n) {
  int s = 0;
  for (int i = 0; i < n; i++)
    for (int j = 0; j < i; j++) {
      if ((i ^ j) & 1)
        continue;
      s += i * j;
      if (s > 1000)
        goto out;
    }
out:
  return s;
}

u64 find(const u64 *a, u64 n, u64 x) {
  for (u64 i = 0; i < n; i++)
    if (a[i] == x)
      return i;
  return n;
}

u64 collatz(u64 x) {
  u64 steps = 0;
  do {
    x = (x & 1) ? 3 * x + 1 : x / 2;
    steps++;
  } while (x != 1 && steps < 1000);
  return steps;
}

int matrix(int n, int m) {
  int t = 0;
  for (int i = 0; i < n; i++) {
    int j = 0;
    while (j < m) {
      if (j == i)
        break;
      t += j++;
    }
  }
  return t;
}

void _start(void) {}
