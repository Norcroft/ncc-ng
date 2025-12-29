// RUN: %cc %s -S -o -

// Layout (AAPCS VFP hard-float, non-HFA struct):
//  Params: int a, P p{int x; double y}, float b
//  Caller:
//    a -> r0
//    p.x -> r1
//    p.y -> r2/r3  (double split across two core regs; not a homogeneous FP aggregate)
//    b -> s0       (scalar float still uses VFP arg reg)
//  Callee:
//    reconstruct p.y into a D-reg with vmov d?, r2, r3
//    widen a and p.x to double for accumulation (vcvt.f64.s32)
//    widen b to double (vcvt.f64.f32)
//    accumulate with vadd.f64 and return double in d0
// What to see:

typedef struct {
    int x;
    double y;
} P;

// CHECK-LABEL: f:
double f(int a, P p, float b)
{
    // CHECK: add r0, r0, r1
    // CHECK: vmov s
    // CHECK: vcvt.f64.s32
    // CHECK: vadd.f64
    // CHECK: vcvt.f64.f32
    // CHECK: vadd.f64
    // CHECK: pc}
    return a + p.x + p.y + b;
}

int main()
{
    P p = {2, 4.5};

    return (int)f(1, p, 3.0f);
}
