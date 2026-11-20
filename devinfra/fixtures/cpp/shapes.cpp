// Virtual dispatch, inheritance and RTTI, which is what vtable recovery has to
// find. Freestanding: no library, so the fixture builds anywhere.

struct Shape {
    virtual ~Shape() {}
    virtual long area() const = 0;
    virtual long perimeter() const = 0;
    virtual const char *name() const { return "shape"; }
};

struct Square : Shape {
    long side;
    explicit Square(long s) : side(s) {}
    long area() const override { return side * side; }
    long perimeter() const override { return 4 * side; }
    const char *name() const override { return "square"; }
};

struct Rect : Shape {
    long w, h;
    Rect(long a, long b) : w(a), h(b) {}
    long area() const override { return w * h; }
    long perimeter() const override { return 2 * (w + h); }
};

struct Cube : Square {
    explicit Cube(long s) : Square(s) {}
    long area() const override { return 6 * side * side; }
    const char *name() const override { return "cube"; }
};

// Called through the base, so the compiler has to dispatch.
long total_area(Shape **shapes, int n) {
    long total = 0;
    for (int i = 0; i < n; i++) total += shapes[i]->area();
    return total;
}

// Written so the optimizer cannot turn the loop into a call to `strlen`,
// which a freestanding link has nothing to resolve against.
long describe(Shape *s) {
    const char *volatile n = s->name();
    long length = 0;
    const char *p = n;
    while (*p != 0) {
        length += 1;
        p += 1;
    }
    return length + s->perimeter();
}

extern "C" long run_shapes() {
    Square square(3);
    Rect rect(2, 5);
    Cube cube(2);
    Shape *shapes[3] = {&square, &rect, &cube};
    return total_area(shapes, 3) + describe(&square);
}

// The operators a freestanding C++ program still needs.
void *operator new(unsigned long, void *p) noexcept { return p; }
void operator delete(void *) noexcept {}
void operator delete(void *, unsigned long) noexcept {}
extern "C" void __cxa_pure_virtual() {}
