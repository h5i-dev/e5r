/* Shared by every datatest source: the pieces that keep a freestanding build
   honest.
   `keep` is volatile so a store to it survives optimization, and the sinks are
   real calls the optimizer cannot see through. There are six of them because a
   compiler folds an if/else ladder whose arms differ only in a constant into a
   bit test, and the ladder is what several of these cases are about. */

#ifndef R12E_DATATESTS_COMMON_H
#define R12E_DATATESTS_COMMON_H

#define NI __attribute__((noinline))

typedef unsigned char u8;
typedef unsigned short u16;
typedef unsigned int u32;
typedef unsigned long u64;
typedef signed char i8;
typedef short i16;
typedef int i32;
typedef long i64;

extern volatile int keep;
extern volatile int counter;

NI void sink(int v);
NI void sink1(int v);
NI void sink2(int v);
NI void sink3(int v);
NI void sink4(int v);
NI void sink5(int v);
NI void sink6(int v);
NI int source(void);

#endif
