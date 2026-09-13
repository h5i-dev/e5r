/* Memory shape cases, ported from Ghidra's decompiler datatests: arrays,
   structures, the stack frame, and references to global data. What each pins is
   that an address computation reads back as an index or a field rather than as
   the multiply and add the machine actually does. */

#include "common.h"

int myarray[10][10];
int my3[8][8][8];
int globindex;
char globstring[32];

struct inner {
    int sub1;
    int sub2;
};

struct outer {
    int first;
    struct inner d;
    int array[16];
};

struct outer glob1;
int glob2;

/* twodim.xml: a two dimensional global array read and written at one row. */
NI void twodim(int valin, int valout) {
    int v = myarray[globindex][valin];
    myarray[globindex][valout] = v + 10;
}

/* threedim.xml: the same with one more dimension. */
NI void threedim(int a, int valin, int valout) {
    int v = my3[globindex][a][valin];
    my3[globindex][a][valout] = v + 3;
}

/* nestedoffset.xml: an array inside a structure, indexed through a pointer, so
   the field offset lands inside the index expression. */
NI int nestedoffset(struct outer *ptr, int a, int b) {
    return ptr->array[b + a];
}

/* offsetarray.xml: an array indexed with a negative adjustment, which folds the
   field offset and the index offset into one constant. */
NI int offsetarray(int n) {
    struct outer s;
    int i;
    for (i = 0; i < 16; i++) s.array[i] = i;
    s.first = 7;
    return s.array[n - 1];
}

/* wayoffarray.xml: the same, with an adjustment big enough to pull the base
   reference out of the structure entirely. */
NI int wayoffarray(int n) {
    struct outer s;
    int i;
    for (i = 0; i < 16; i++) s.array[i] = i * 3;
    s.first = 9;
    return s.array[n - 4];
}

/* stackcorner.xml: a local array written through a computed index, where the
   frame layout has to survive an index that reaches past the declared bound. */
NI int arraybottom(int n) {
    int arr[16];
    int i;
    for (i = 0; i < 16; i++) arr[i] = i;
    arr[n & 15] = 100;
    return arr[(n + 1) & 15];
}

/* dupptr.xml: several accesses that share an intermediate pointer. The base has
   to be pushed past the shared part for the natural expression to come back. */
NI void dupptr(struct outer *ptr, int a) {
    ptr->array[a] = ptr->array[a] >> 3 & 0xf;
    ptr->d.sub1 = ptr->array[a] + 0x25;
}

/* pointercmp.xml: a pointer walked until it reaches the address of a later
   field, which is the loop bound. The bound comes from a volatile so the
   compiler cannot turn the walk into a fixed run of stores. */
NI void pointercmp(struct outer *ptr) {
    char *p;
    char *end = (char *)ptr->array + (counter & 63);
    for (p = (char *)ptr->array; p < end; p++) *p = 'a';
}

/* offcut.xml: references into the middle of a global, which should read as the
   field they land on rather than as a bare address. */
NI void offcut(void) {
    sink1(glob2);
    sink2(glob1.d.sub1);
    sink3(glob1.array[3]);
    keep = 1;
}

/* condconst.xml, the global half: constants stored to globals on one path. */
NI void globalconst(int d) {
    globindex = 0;
    glob2 = d;
    glob1.first = 10;
    glob1.d.sub2 = 10;
}

/* stackstring.xml: a string constant the compiler stores as immediates into a
   stack buffer, which is what makes it invisible to a string scan. */
NI void stackstring(void) {
    char buf[32];
    buf[0] = 'h'; buf[1] = 'e'; buf[2] = 'l'; buf[3] = 'l';
    buf[4] = 'o'; buf[5] = ' '; buf[6] = 'w'; buf[7] = 'o';
    buf[8] = 'r'; buf[9] = 'l'; buf[10] = 'd'; buf[11] = 0;
    sink(buf[counter & 7]);
}

/* heapstring.xml: the same store pattern, to memory the function does not own. */
NI void heapstring(char *ptr) {
    ptr[0] = 'M'; ptr[1] = 'e'; ptr[2] = 's'; ptr[3] = 's';
    ptr[4] = 'a'; ptr[5] = 'g'; ptr[6] = 'e'; ptr[7] = ':'; ptr[8] = ' ';
}

/* varcross.xml: two stores to the same place with a call between them. Neither
   store may be merged with the other, because the call can read what is there. */
NI void varcross(void) {
    globstring[10] = 0x18;
    sink1(source());
    globstring[10] = 0x48;
}

/* revisit.xml: two accesses of different widths to one global, where the
   narrower one forces the wider one's definition to be reconsidered. */
NI void revisit(void) {
    glob2 = glob2 + 10;
    *(short *)&glob2 = (short)(*(short *)&glob2 + 100);
    glob1.first = glob2;
}

/* wraprange.xml: a stack range written from a high address down to a low one,
   so the frame offsets run through zero. */
NI int wraprange(int a, int b) {
    int frame[4];
    frame[3] = a;
    frame[2] = b;
    frame[1] = a + b;
    frame[0] = a - b;
    return frame[0] + frame[1] + frame[2] + frame[3];
}
