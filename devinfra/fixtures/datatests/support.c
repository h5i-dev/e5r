/* The definitions common.h declares, plus an entry point, so each source links
   into a static freestanding executable. A linked image is what the jump table
   and global-reference cases need: a relocatable object leaves both unresolved. */

#include "common.h"

volatile int keep;
volatile int counter;

NI void sink(int v) { keep += v; }
NI void sink1(int v) { keep = v + 1; }
NI void sink2(int v) { keep = v + 2; }
NI void sink3(int v) { keep = v + 3; }
NI void sink4(int v) { keep = v + 4; }
NI void sink5(int v) { keep = v + 5; }
NI void sink6(int v) { keep = v + 6; }
NI int source(void) { return keep * 3 + 1; }

void _start(void) {
    for (;;) sink(source());
}
