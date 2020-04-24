struct A {
    virtual int f() const = 0;
    virtual ~A() {}
};

struct B : public A {
    virtual int f() const { return 0; }
};

struct C : public B {
    virtual int f() const { return 1; }
    virtual ~C() {}
};


int call(const A* a) {
    return a->f();
}
