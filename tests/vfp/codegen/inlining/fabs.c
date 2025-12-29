// RUN: %cc %s -S -o -

#include <math.h>

double fabs_sum(double p, double q) {
    // CHECK: vadd.f64        d0, d0, d1
    // CHECK: vabs.f64        d0, d0
    double r = fabs(p + q);

    // CHECK: vmov.f64        d1, #112        @ =1.0 (0x3ff00000...0)
    // CHECK: vsub.f64        d0, d0, d1
    // CHECK: mov     pc, lr
    return r - 1;
}

float fabsf_sum(float p, float q) {
    // CHECK: vadd.f32    s0, s0, s2
    // CHECK: vabs.f32    s0, s0
    float r = fabsf(p + q);

    // CHECK: vmov.f32    s2, #112      @ =1.0 (0x3f800000)
    // CHECK: vsub.f32    s0, s0, s2
    // CHECK: mov     pc, lr
    return r - 1;
}

// Register allocations in main are adapted as it knows the register allocations
// for floor_sum().
int main(void)
{
    // CHECK: vmov.f64        d1, #24 @ =6.0    (0x40180000...0)
    // CHECK: vmov.f64        d0, #20 @ =5.0    (0x40140000...0)
    float a = 5;
    int b = 6;

    // This relies on it knowing the register layout of abs_sum().
    // see tests/vfp/call-func-1.c for the same test but extern.
    // CHECK: vmov.f64        d2, d0
    // CHECK: bl
    double c = fabs_sum(a, b);

    // CHECK: vadd.f64        d0, d2, d0
    // CHECK: vcvt.s32.f64    s30, d0
    // CHECK: vmov    r0, s30
    // CHECK: ldmdb   fp, {fp, sp, pc}
    return a + c;
}
