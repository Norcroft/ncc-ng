// RUN: %cc %s -S -o -

#include <math.h>

double fabs_sum(double p, double q) {
    // CHECK: mov             ip, sp
    // CHECK: stmdb           sp!, {r0-r3, fp-ip, lr-pc}
    // CHECK: sub             fp, ip, #4
    // CHECK: cmp             sp, r10
    // CHECK: blmi            __rt_stkovf_split_small
    // CHECK: stmdb           sp!, {r0-r1}
    // CHECK: ldfd            f1, [sp], #&8
    // CHECK: stmdb           sp!, {r2-r3}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: adfd            f0, f1, f0
    // CHECK: stfd            f0, [sp, #-&8]!
    // CHECK: ldmia           sp!, {r0-r1}
    // CHECK: bl              fabs
    double r = fabs(p + q);

    // CHECK: sufd            f0, f0, #&1     @ =1.0
    // CHECK: ldmdb           fp, {fp, sp, pc}
    return r - 1;
}

float fabsf_sum(float p, float q) {
    // CHECK: mov             ip, sp
    // CHECK: stmdb           sp!, {r0-r3, fp-ip, lr-pc}
    // CHECK: sub             fp, ip, #4
    // CHECK: cmp             sp, r10
    // CHECK: blmi            __rt_stkovf_split_small
    // CHECK: stmdb           sp!, {r0-r1}
    // CHECK: ldfd            f1, [sp], #&8
    // CHECK: stmdb           sp!, {r2-r3}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: mvfs            f1, f1
    // CHECK: mvfs            f0, f0
    // CHECK: adfs            f0, f1, f0
    // CHECK: stfd            f0, [sp, #-&8]!
    // CHECK: ldmia           sp!, {r0-r1}
    // CHECK: bl              fabsf
    float r = fabsf(p + q);

    // CHECK: sufs            f0, f0, #&1     @ =1.0
    // CHECK: ldmdb           fp, {fp, sp, pc}
    return r - 1;
}

int main(void)
{
    // CHECK: mov             ip, sp
    // CHECK: stmdb           sp!, {fp-ip, lr-pc}
    // CHECK: sub             fp, ip, #4
    // CHECK: sfm             f4, 1, [sp, #-&c]!
    // CHECK: cmp             sp, r10
    // CHECK: blmi            __rt_stkovf_split_small

    // CHECK: add             r2, pc, #L0000ec-.-8
    // CHECK: mvfd            f4, #&5         @ =5.0
    // CHECK: stfd            f4, [sp, #-&8]!
    float a = 5;
    int b = 6;

    // CHECK: ldmia           sp!, {r0-r1}
    // CHECK: ldmia           r2, {r2-r3}
    // CHECK: bl              fabs_sum
    double c = fabs_sum(a, b);

    // CHECK: adfd            f0, f4, f0
    // CHECK: fixsz           r0, f0
    // CHECK: lfm             f4, 1, [fp, #-&18]
    // CHECK: ldmdb           fp, {fp, sp, pc}
    return a + c;
}
// CHECK: L0000ec
// CHECK: DCD      0x40180000, 0x00000000
