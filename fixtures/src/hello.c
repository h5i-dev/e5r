/* Smallest useful fixture: a call, a loop, a switch, and a string. */
#include <stdio.h>
#include <string.h>

static int sum_to(int n) {
    int acc = 0;
    for (int i = 0; i <= n; i++) acc += i;
    return acc;
}

static const char *classify(int n) {
    switch (n) {
    case 0: return "zero";
    case 1: return "one";
    case 2: return "two";
    case 3: return "three";
    case 4: return "four";
    default: return "many";
    }
}

int main(int argc, char **argv) {
    int n = argc > 1 ? (int)strlen(argv[1]) : 4;
    printf("%s %d\n", classify(n), sum_to(n));
    return 0;
}
