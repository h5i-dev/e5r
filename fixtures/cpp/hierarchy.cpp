// A class hierarchy known by construction: this file is the oracle the RTTI
// reader is measured against. Single inheritance, multiple inheritance,
// virtual inheritance, an abstract base and a virtual destructor, so every
// shape of Itanium type information appears: __class_type_info,
// __si_class_type_info and __vmi_class_type_info.
//
// Freestanding, so it links with no C++ runtime. The ABI's three type-info
// class vtables are named here as bare arrays, because the compiler emits
// references to them and a -nostdlib link has nothing else to resolve them
// against. Only their addresses matter: a type-info object's first word names
// one of the three and that is how its kind is read back. They are given
// non-zero contents so they land in .rodata; all-zero data would go to .bss,
// and a -nostdlib static link puts .bss in a segment this kernel will not map.

void *operator new(__SIZE_TYPE__, void *p) noexcept { return p; }
void operator delete(void *) noexcept {}
void operator delete(void *, __SIZE_TYPE__) noexcept {}

#if defined(_WIN32)
// The Microsoft ABI's own pieces. `type_info`'s vtable is what every RTTI
// type descriptor's first word points at, and the pure-virtual stub is what
// an abstract class's unimplemented slots hold.
extern "C" int _purecall() { return 0; }
const void *msvc_type_info[4] __asm__("??_7type_info@@6B@") = {
    (const void *)1, (const void *)2, (const void *)3, (const void *)4};
#else
extern "C" void __cxa_pure_virtual() {}
const void *abi_class[4] __asm__("_ZTVN10__cxxabiv117__class_type_infoE") = {
    (const void *)1, (const void *)2, (const void *)3, (const void *)4};
const void *abi_si[4] __asm__("_ZTVN10__cxxabiv120__si_class_type_infoE") = {
    (const void *)1, (const void *)2, (const void *)3, (const void *)4};
const void *abi_vmi[4] __asm__("_ZTVN10__cxxabiv121__vmi_class_type_infoE") = {
    (const void *)1, (const void *)2, (const void *)3, (const void *)4};
#endif

// Abstract, with a virtual destructor. Type information: __class_type_info.
struct Base {
    long id;
    Base() : id(1) {}
    virtual ~Base();
    virtual long tag() const = 0;
};
Base::~Base() {}

// Single inheritance: __si_class_type_info, one base at offset zero.
struct Single : Base {
    long extra;
    explicit Single(long e) : extra(e) {}
    ~Single() override;
    long tag() const override { return id + extra; }
};
Single::~Single() {}

// Two roots joined by multiple inheritance. Leftish is one vtable pointer
// plus one word, so Rightish's subobject starts at offset 16.
struct Leftish {
    long a;
    Leftish() : a(2) {}
    virtual ~Leftish();
    virtual long left() const { return a; }
};
Leftish::~Leftish() {}

struct Rightish {
    long b;
    Rightish() : b(3) {}
    virtual ~Rightish();
    virtual long right() const { return b; }
};
Rightish::~Rightish() {}

// __vmi_class_type_info: Leftish at 0, Rightish at 16.
struct Pair : Leftish, Rightish {
    long both;
    Pair() : both(4) {}
    ~Pair() override;
    long left() const override { return a + both; }
    long right() const override { return b + both; }
};
Pair::~Pair() {}

// Virtual inheritance: one Root under two paths, so a Join has one Root and
// the type information records the base as virtual rather than at an offset.
struct Root {
    long r;
    Root() : r(5) {}
    virtual ~Root();
    virtual long root() const { return r; }
};
Root::~Root() {}

struct ViaA : virtual Root {
    long a2;
    ViaA() : a2(6) {}
    ~ViaA() override;
    long root() const override { return r + a2; }
};
ViaA::~ViaA() {}

struct ViaB : virtual Root {
    long b2;
    ViaB() : b2(7) {}
    ~ViaB() override;
};
ViaB::~ViaB() {}

// __vmi_class_type_info: ViaA at 0, ViaB at 16, and Root reached through both.
struct Join : ViaA, ViaB {
    long j;
    Join() : j(8) {}
    ~Join() override;
    long root() const override { return r + a2 + b2 + j; }
};
Join::~Join() {}

static long through_base(const Base *b) { return b->tag(); }

// Named `run_shapes` so the fixture shares the freestanding entry point in
// start.cpp, which writes the answer out: 11 + 6 + 7 + 26 = 50. The Windows
// build has its own entry, because start.cpp is a Linux system call.
#if defined(_WIN32)
extern "C" int mainCRTStartup();
#endif
extern "C" long run_shapes() {
    Single s(10);
    Pair p;
    Join j;
    const Leftish *l = &p;
    const Rightish *r = &p;
    const Root *rt = &j;
    return through_base(&s) + l->left() + r->right() + rt->root();
}

#if defined(_WIN32)
extern "C" int mainCRTStartup() { return (int)run_shapes(); }
#endif
