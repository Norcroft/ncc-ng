// RUN: %cc %s -S -o -

#include <time.h>

double second(void)
{
    // CHECK: mov             ip, sp
    // CHECK: stmdb           sp!, {fp-ip, lr-pc}
    // CHECK: sub             fp, ip, #4
    // CHECK: cmp             sp, r10
    // CHECK: blmi            __rt_stkovf_split_small
    // CHECK: bl              clock
    clock_t t = clock();

    // unsigned to double
    // CHECK: eor             r0, r0, #2147483648
    // CHECK: fltd            f0, r0
    // CHECK: ldfd            f1, [pc, #L000040-.-8]
    // CHECK: adfd            f0, f0, f1
    double td = (double)t;

    // CHECK: ldfd            f1, [pc, #L000048-.-8]
    // CHECK: dvfd            f0, f0, f1
    double td_div_ps = td / (double)CLOCKS_PER_SEC;

    // CHECK: ldmdb           fp, {fp, sp, pc}
    return td_div_ps;
}
// CHECK: L000040
// CHECK: DCFD     2147483648.0

// CHECK: L000048
// CHECK: DCFD     100.0
