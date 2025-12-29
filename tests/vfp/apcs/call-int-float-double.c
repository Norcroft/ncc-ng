// RUN: %cc %s -S -o -

// Layout (AAPCS VFP hard-float):
//  main:
//     r0: 7
//     s0: 3.5f
//     d1: 9.25

// What to see:
//  - widen b to double for (c + b): vcvt.f64.f32
//  - double add: vadd.f64
//  - int conversions from b,c: vcvt.s32.f32 and vcvt.s32.f64

// CHECK-LABEL: callee:

//

static int g;
static volatile double gd;

int callee(int a, float b, double c) {
    // CHECK: vcvt.s32.f32
    // CHECK: add
    // CHECK: vcvt.s32.f64
    // CHECK: add
    g = a + (int)b + (int)c;

    // CHECK: vcvt.f64.f32
    // CHECK: vadd.f64
    gd = c + b;

    // CHECK: vcvt.s32.f64
    // CHECK: mov pc, lr
    return g + (int)gd;
}

int main()
{
    // CHECK-LABEL: main
    // CHECK: vldr    d1, [pc
    // CHECK: vmov.f32    s0, #12
    // CHECK: mov    r0, #7

    return callee(7, 3.5f, 9.25);
}
