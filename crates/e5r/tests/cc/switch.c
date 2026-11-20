/* A dense switch, which clang would turn into a jump table, and a sparse
 * one. */
int dense(int x) {
  switch (x) {
  case 0: return x + 3;
  case 1: return x * 7;
  case 2: return x - 9;
  case 3: return x ^ 5;
  case 4: return x << 2;
  case 5: return x | 64;
  case 6: return 100 - x;
  case 7: return x * x;
  default: return -1;
  }
}

int sparse(int x) {
  switch (x) {
  case 3: return 1;
  case 300: return 2;
  case 30000: return 3;
  default: return 0;
  }
}

void _start(void) {}
