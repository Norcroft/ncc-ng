// RUN: %cc %s -S -o -

#include <math.h>

double something(double p, double q);

int main(void)
{
    // CHECK: sfm             f4, 1, [sp, #-&c]!
    // CHECK: cmp             sp, r10
    // CHECK: blmi            __rt_stkovf_split_small
    // CHECK: add             r2, pc, #L00004c-.-8
    // CHECK: mvfd            f4, #&5     @ =5.0
    // CHECK: stfd            f4, [sp, #-&8]!
    // CHECK: ldmia           sp!, {r0-r1}
    // CHECK: ldmia           r2, {r2-r3}
    float a = 5;
    int b = 6;

    // CHECK: bl
    double c = something(a, b);

    // CHECK: adfd            f0, f4, f0
    // CHECK: fixsz           r0, f0
    // CHECK: lfm             f4, 1, [fp, #-&18]
    // CHECK: ldmdb           fp, {fp, sp, pc}
    return a + c;

    // literal: 6.0
    // CHECK: DCD      0x40180000, 0x00000000
}
