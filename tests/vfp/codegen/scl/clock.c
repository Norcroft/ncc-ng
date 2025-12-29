// RUN: %cc %s -S -o -

#include <time.h>

double second(void)
{
    clock_t t = clock();

    // CHECK: vcvt.f64.s32    d0, s0
    double td = (double)t;

    // CHECK: vldr    d1, [pc,
    // CHECK: vdiv.f64    d0, d0, d1
    double td_div_ps = td / (double)CLOCKS_PER_SEC;

    // CHECK: ldmdb    fp, {fp, sp, pc}
    return td_div_ps;
}

// Check for 100 (VFP word order):
// CHECK: 0x00000000
// CHECK: 0x40590000

