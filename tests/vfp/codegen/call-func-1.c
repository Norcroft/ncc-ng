// RUN: %cc %s -S -o -

#include <math.h>

double something(double p, double q);

int main(void)
{
    // CHECK: vmov.f64        d1, #24 @ =6.0
    // CHECK: vmov.f64        d0, #20 @ =5.0
    float a = 5;
    int b = 6;

    // CHECK: bl
    double c = something(a, b);

    // CHECK: vadd.f64        d0,
    // CHECK: vcvt.s32.f64    s30, d0
    // CHECK: vmov    r0, s30
    // CHECK: ldmdb   fp, {fp, sp, pc}
    return a + c;
}
